(* ========================================================================= *)
(* pc_moi_s30_tame: triangulated topological surfaces (Moise GTM 47,        *)
(* section 30 and pp.37-38).  Main theorems:                                *)
(*   SURFACE_TRIANG   |- MOI_S30_SURFACE_TRIANG                             *)
(*   POLY_DISK        |- MOI_S30_POLY_DISK                                  *)
(*   PL_TORUS_COMPLEX |- MOI_S30_PL_TORUS_COMPLEX                           *)
(* SURFACE_TRIANG: the locally finite form of MOI_S28_SURF_LOCAL.  The      *)
(* finite proof (pc_moi_s28_tria, pc_moi_s28_trib) is local; here each      *)
(* local step runs in the closed star of a point (a finite subcomplex whose *)
(* polyhedron contains the open star, open in both polyhedra), with the     *)
(* charts transferred between the two polyhedra.  POLY_DISK: a locally      *)
(* polyhedral topological 2-cell is a PL 2-cell with the same boundary      *)
(* (a triangulation is a combinatorial surface with boundary the image of   *)
(* the circle; chi = 1 and one boundary circle give a PL disk).             *)
(* PL_TORUS_COMPLEX: a PL torus is a closed connected combinatorial surface *)
(* with chi 0.                                                              *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s28_plane.ml";;
needs "src/pc_moi_s28_torus.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: chart shrinking and transfer.  Plane and half-plane charts can be *)
(* shrunk into any open neighbourhood (a ball, a half ball with the radial  *)
(* rescaling z |-> z / (r - |z|)), so they pass between two polyhedra that  *)
(* share an open neighbourhood of the point.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TM_HALF_BALL_HOMEO = prove
 (`!r. &0 < r
       ==> homeomorphism ({z:real^2 | &0 <= z$2} INTER ball(vec 0,r),{z | &0 <= z$2})
                         ((\z. inv(r - norm z) % z),(\w. (r * inv(&1 + norm w)) % w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TA_HOMEO_INV THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SUBGOAL_THEN `(lift o (\z:real^2. inv(r - norm z))) = (lift o inv o (\z. r - norm z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SUBGOAL_THEN `(lift o (\w:real^2. r * inv(&1 + norm w))) =
                  (\w. r % (lift o inv o (\w. &1 + norm w)) w)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPEC `w:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC];
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < r - norm(z:real^2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_ABS_INV;
                 REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LID] `!c z:real^2. c = &1 ==> c % z = z`) THEN
    MP_TAC(ISPEC `z:real^2` NORM_POS_LE) THEN
    UNDISCH_TAC `&0 < r - norm(z:real^2)` THEN UNDISCH_TAC `&0 < r` THEN
    CONV_TAC REAL_FIELD;
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &1 + norm(w:real^2)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `w:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `q = r * inv(&1 + norm(w:real^2))` THEN
    SUBGOAL_THEN `&0 < q /\ q * norm(w:real^2) < r /\ r - q * norm w = q`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ];
        SUBGOAL_THEN `(r * inv(&1 + norm(w:real^2))) * norm w =
                      r * (norm w / (&1 + norm w))` SUBST1_TAC THENL
         [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < &1 + norm(w:real^2)` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(MESON[VECTOR_MUL_LID] `!c w:real^2. c = &1 ==> c % w = w`) THEN
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD]]);;

let MOI_S3TM_R2_SHRINK = prove
 (`!(X:real^N->bool) W y.
     moi_s28_locally_r2 X y /\ open_in (subtopology euclidean X) W /\ y IN W
     ==> ?u. open_in (subtopology euclidean X) u /\ y IN u /\ u SUBSET W /\
             u homeomorphic (:real^2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u0:real^N->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f:real^N->real^2` (X_CHOOSE_THEN `g:real^2->real^N`
    ASSUME_TAC) o GEN_REWRITE_RULE I [homeomorphic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean u0) (u0 INTER W:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(u0:real^N->bool) SUBSET X` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `open_in (subtopology euclidean X) (W:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN EXISTS_TAC `G:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (f:real^N->real^2) (u0 INTER W))` MP_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^2`; `g:real^2->real^N`; `u0:real^N->bool`;
                   `(:real^2)`; `u0 INTER W:real^N->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^2) y`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (g:real^2->real^N) (ball((f:real^N->real^2) y,r))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u0:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (g:real^2->real^N) (ball((f:real^N->real^2) y,r)) =
                  {x | x IN u0 /\ f x IN ball(f y,r)}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; OPEN_BALL; SUBTOPOLOGY_UNIV; GSYM OPEN_IN];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(f:real^N->real^2) y` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ASM SET_TAC[];
    MATCH_MP_TAC(ISPECL [`IMAGE (g:real^2->real^N) (ball((f:real^N->real^2) y,r))`;
                         `ball((f:real^N->real^2) y,r)`; `(:real^2)`] HOMEOMORPHIC_TRANS) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_BALL_UNIV] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`g:real^2->real^N`; `f:real^N->real^2`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^2)`; `u0:real^N->bool`] THEN
    ASM_SIMP_TAC[HOMEOMORPHISM_SYM; SUBSET_UNIV] THEN ASM SET_TAC[]]);;

let MOI_S3TM_HALF_SHRINK = prove
 (`!(X:real^N->bool) W y.
     moi_s28_locally_half X y /\ open_in (subtopology euclidean X) W /\ y IN W
     ==> ?u (h:real^N->real^2) k.
           open_in (subtopology euclidean X) u /\ y IN u /\ u SUBSET W /\
           homeomorphism (u,{z:real^2 | &0 <= z$2}) (h,k) /\ h y = vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u0:real^N->bool` (X_CHOOSE_THEN
    `h:real^N->real^2` (X_CHOOSE_THEN `k:real^2->real^N` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean u0) (u0 INTER W:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(u0:real^N->bool) SUBSET X` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `open_in (subtopology euclidean X) (W:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN EXISTS_TAC `G:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean {z:real^2 | &0 <= z$2})
                  (IMAGE (h:real^N->real^2) (u0 INTER W))` MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->real^N`; `u0:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^2` o CONJUNCT2 o
    GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `(h:real^N->real^2) y = vec 0`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `r:real` MOI_S3TM_HALF_BALL_HOMEO) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `ph = \z:real^2. inv(r - norm z) % z` THEN
  ABBREV_TAC `ps = \w:real^2. (r * inv(&1 + norm w)) % w` THEN DISCH_TAC THEN
  ABBREV_TAC `u = {x | x IN u0 /\ (h:real^N->real^2) x IN ball(vec 0,r)}` THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^2) u = {z:real^2 | &0 <= z$2} INTER ball(vec 0,r)`
  ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `(ph:real^2->real^2) o (h:real^N->real^2)`;
                        `(k:real^2->real^N) o (ps:real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u0:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "u" THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    EXPAND_TAC "u" THEN
    UNDISCH_TAC `ball(vec 0:real^2,r) INTER {z | &0 <= z$2} SUBSET
                 IMAGE (h:real^N->real^2) (u0 INTER W)` THEN
    UNDISCH_TAC `!x. x IN u0 ==> (k:real^2->real^N) (h x) = x` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^2) u0 = {z | &0 <= z$2}` THEN
    SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `{z:real^2 | &0 <= z$2} INTER ball(vec 0,r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u0:real^N->bool`; `{z:real^2 | &0 <= z$2}`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "u" THEN SET_TAC[];
    EXPAND_TAC "ph" THEN ASM_REWRITE_TAC[o_THM; VECTOR_MUL_RZERO]]);;

let MOI_S3TM_CHART_TRANSFER = prove
 (`!(X:real^N->bool) Y W y.
     open_in (subtopology euclidean X) W /\ open_in (subtopology euclidean Y) W /\ y IN W
     ==> (moi_s28_locally_r2 X y ==> moi_s28_locally_r2 Y y) /\
         (moi_s28_locally_half X y ==> moi_s28_locally_half Y y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`X:real^N->bool`; `W:real^N->bool`; `y:real^N`] MOI_S3TM_R2_SHRINK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`X:real^N->bool`; `W:real^N->bool`; `y:real^N`]
      MOI_S3TM_HALF_SHRINK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
      (X_CHOOSE_THEN `k:real^2->real^N` STRIP_ASSUME_TAC))) THEN
    REWRITE_TAC[moi_s28_locally_half] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `h:real^N->real^2`; `k:real^2->real^N`] THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `W:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `X:real^N->bool` THEN ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]);;


(* ------------------------------------------------------------------------- *)
(* Part 2: closed stars in a locally finite complex.  The closed star of a  *)
(* point v (the faces of the simplices through v) is a finite subcomplex;   *)
(* its polyhedron contains the open star moi_sta_open_star c v, which is    *)
(* open in |c| and hence in the closed star, so chart predicates at points  *)
(* of the open star agree in the two polyhedra.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TM_STAR = prove
 (`!c (v:real^N).
     lf_simplicial_complex c /\ v IN UNIONS c
     ==> simplicial_complex {s | ?t. t IN c /\ v IN t /\ s face_of t} /\
         {s | ?t. t IN c /\ v IN t /\ s face_of t} SUBSET c /\
         (!t. t IN c /\ v IN t ==> t IN {s | ?t. t IN c /\ v IN t /\ s face_of t}) /\
         v IN moi_sta_open_star c v /\
         moi_sta_open_star c v SUBSET UNIONS {s | ?t. t IN c /\ v IN t /\ s face_of t} /\
         open_in (subtopology euclidean (UNIONS c)) (moi_sta_open_star c v) /\
         open_in (subtopology euclidean (UNIONS {s | ?t. t IN c /\ v IN t /\ s face_of t}))
                 (moi_sta_open_star c v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (v:real^N) IN t /\ s face_of t}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN c ==> convex t /\ polytope t` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_POLYTOPE]; ALL_TAC] THEN
  SUBGOAL_THEN `(K:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN c /\ v IN t ==> t IN K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[FACE_OF_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_sta_open_star c (v:real^N) SUBSET UNIONS K` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sta_open_star; SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (moi_sta_open_star c (v:real^N))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_complex] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `UNIONS (IMAGE (\t:real^N->bool. {f | f face_of t})
                                {t | t IN c /\ v IN t})` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_IMAGE THEN
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`]
            MOI_FDN_LF_COMPACT_MEETS_FINITE) THEN
          ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET] THEN DISCH_TAC THEN
          MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{s | s IN c /\ ~(s INTER {v:real^N} = {})}` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN ASM_MESON_TAC[]];
        EXPAND_TAC "K" THEN
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[]];
      ASM SET_TAC[];
      EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[FACE_OF_TRANS];
      ASM SET_TAC[]];
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Chart predicates at points of the open star agree in |c| and in the     *)
(* closed star.                                                             *)

let MOI_S3TM_STAR_CHART = prove
 (`!c (v:real^N) y.
     lf_simplicial_complex c /\ v IN UNIONS c /\ y IN moi_sta_open_star c v
     ==> (moi_s28_locally_r2 (UNIONS c) y <=>
          moi_s28_locally_r2 (UNIONS {s | ?t. t IN c /\ v IN t /\ s face_of t}) y) /\
         (moi_s28_locally_half (UNIONS c) y <=>
          moi_s28_locally_half (UNIONS {s | ?t. t IN c /\ v IN t /\ s face_of t}) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`;
                 `UNIONS {s | ?t. t IN c /\ (v:real^N) IN t /\ s face_of t}`;
                 `moi_sta_open_star c (v:real^N)`; `y:real^N`] MOI_S3TM_CHART_TRANSFER) THEN
  MP_TAC(ISPECL [`UNIONS {s | ?t. t IN c /\ (v:real^N) IN t /\ s face_of t}`;
                 `UNIONS c:real^N->bool`;
                 `moi_sta_open_star c (v:real^N)`; `y:real^N`] MOI_S3TM_CHART_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Under charts on |c|, the points of the open star have charts in the      *)
(* closed star.                                                             *)

let MOI_S3TM_STAR_CH = prove
 (`!c (v:real^N) y.
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     v IN UNIONS c /\ y IN moi_sta_open_star c v
     ==> moi_s28_locally_r2 (UNIONS {s | ?t. t IN c /\ v IN t /\ s face_of t}) y \/
         moi_s28_locally_half (UNIONS {s | ?t. t IN c /\ v IN t /\ s face_of t}) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`] MOI_S3TM_STAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_sta_open_star c v` THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 3: dimension, purity and edge counts for locally finite c with      *)
(* charts (MOI_S8TB_DIM, _MAXIMAL, _PURE, _EDGE_CARD for locally finite c;  *)
(* each local argument runs in a closed star).                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TM_DIM_LF = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y)
     ==> !s. s IN c ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`; `y:real^N`] MOI_S3TM_STAR_CH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S8TA_EMB2_DIM THEN
  MAP_EVERY EXISTS_TAC [`{s | ?t. t IN c /\ (y:real^N) IN t /\ s face_of t}`; `y:real^N`] THEN
  ASM_SIMP_TAC[MOI_S8TA_EMB2_OF]);;

let MOI_S3TM_MAXIMAL_LF = prove
 (`!c (t:real^N->bool).
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     t IN c /\ ~(t = {}) /\ (!u. u IN c /\ t SUBSET u ==> u = t)
     ==> &2 <= aff_dim t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(relative_interior t:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(y:real^N) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`; `y:real^N`] MOI_S3TM_STAR_CH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (y:real^N) IN t /\ s face_of t}` THEN
  MATCH_MP_TAC(ISPECL
   [`UNIONS K:real^N->bool`; `y:real^N`;
    `{x:real^N | x IN UNIONS K /\ !u. u IN K /\ x IN u ==> t SUBSET u}`;
    `t:real^N->bool`] MOI_S8TB_LOW_NO) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[];
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `(K:(real^N->bool)->bool) SUBSET c`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^N->bool) IN c` ASSUME_TAC THENL
     [MP_TAC(ASSUME `(K:(real^N->bool)->bool) SUBSET c`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^N->bool) SUBSET u` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!u:real^N->bool. u IN K /\ (x:real^N) IN u ==> t SUBSET u`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^N->bool) = t` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!u:real^N->bool. u IN c /\ t SUBSET u ==> u = t`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ASM_INT_ARITH_TAC]);;

let MOI_S3TM_PURE_LF = prove
 (`!c (s:real^N->bool).
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     s IN c /\ ~(s = {})
     ==> ?t. t IN c /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN c ==> aff_dim u <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3TM_DIM_LF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!u:real^N->bool. u IN c /\ s SUBSET u
                     ==> aff_dim u <= &1 /\ &0 <= aff_dim u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(u:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(u:real^N->bool) <= &2` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(u:real^N->bool) = &2)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_GE) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `?t:real^N->bool. t IN c /\ aff_dim t = &1 /\ s SUBSET t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_S3TM_MAXIMAL_LF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S3TM_MAXIMAL_LF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      UNDISCH_TAC `~(?t:real^N->bool. t IN c /\ aff_dim t = &1 /\ s SUBSET t)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC]]);;

let MOI_S3TM_EDGE_CARD_LF = prove
 (`!c (e:real^N->bool).
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     e IN c /\ aff_dim e = &1
     ==> CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1 \/
         CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior e:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(y:real^N) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`; `y:real^N`] MOI_S3TM_STAR_CH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (y:real^N) IN t /\ s face_of t}` THEN
  ABBREV_TAC `ts = {t | t IN c /\ aff_dim t = &2 /\ (e:real^N->bool) SUBSET t}` THEN
  SUBGOAL_THEN `(ts:(real^N->bool)->bool) SUBSET K` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^N->bool. t IN c /\ y IN t ==> t IN K`) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (ts:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(ts:(real^N->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_S3TM_PURE_LF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(ts:(real^N->bool)->bool) <= 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`3`; `ts:(real^N->bool)->bool`] CHOOSE_SUBSET_STRONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_SCF_HAS_SIZE_3]) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
      (X_CHOOSE_THEN `t3:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(t1:real^N->bool) IN ts /\ t2 IN ts /\ t3 IN ts` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t1:real^N->bool) IN K /\ t2 IN K /\ t3 IN K` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^N->bool) IN K` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t:real^N->bool. t IN c /\ y IN t ==> t IN K`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(t1:real^N->bool) IN ts /\ t2 IN ts /\ t3 IN ts` THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e:real^N->bool`; `t1:real^N->bool`;
                   `t2:real^N->bool`; `t3:real^N->bool`; `y:real^N`]
      MOI_S8TA_EDGE3_NO) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Part 4: vertex links.  The local vertex-link lemma, applied in the       *)
(* closed star of a vertex (same link, same triangles at the edges through  *)
(* the vertex).                                                              *)
(* ------------------------------------------------------------------------- *)

(* The vertex-link analysis of MOI_S8TB_VERTEX_LINK from local data at w    *)
(* only (dimension, purity, punctured neighbourhoods of w, edge counts at  *)
(* the edges through w), so that it applies to closed stars.  The proof is  *)
(* that of MOI_S8TB_VERTEX_LINK with these facts as hypotheses.            *)

let MOI_S3TM_VERTEX_LINK_LOC = prove
 (`!d (w:real^N).
     simplicial_complex d /\ {w} IN d /\
     (!s. s IN d ==> aff_dim s <= &2) /\
     (!s. s IN d /\ ~(s = {}) ==> ?t. t IN d /\ aff_dim t = &2 /\ s SUBSET t) /\
     (!u0. open_in (subtopology euclidean (UNIONS d)) u0 /\ w IN u0
           ==> ?v. open_in (subtopology euclidean (UNIONS d)) v /\ w IN v /\
                   v SUBSET u0 /\ connected (v DELETE w)) /\
     (!a. {a} IN simplicial_link d w
          ==> CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 1 \/
              CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)
     ==> (pl_sphere 1 (UNIONS (simplicial_link d w)) \/
          pl_ball 1 (UNIONS (simplicial_link d w))) /\
         ((!a. {a} IN simplicial_link d w
               ==> CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)
          ==> pl_sphere 1 (UNIONS (simplicial_link d w)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pure")
    (CONJUNCTS_THEN2 (LABEL_TAC "punct") (LABEL_TAC "ecard")))))) THEN
  SUBGOAL_THEN `simplicial_complex (simplicial_link d (w:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LINK_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN simplicial_link d w ==> aff_dim s <= &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_LINK_DIM THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `w:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN simplicial_link d w /\ ~(s = {})
                     ==> ?e. e IN simplicial_link d w /\ aff_dim e = &1 /\ s SUBSET e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_LINK_COVER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^N. {a} IN simplicial_link d w
     ==> CARD {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ a IN e} =
         CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} /\
         (CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 1 \/
          CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)`
  (LABEL_TAC "degs") THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S8TB_LINK_DEGREE THEN ASM_REWRITE_TAC[];
      USE_THEN "ecard" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (UNIONS (simplicial_link d (w:real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TB_LINK_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`] MOI_S8TB_LINK_NONEMPTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    MP_TAC(ISPEC `t0:real^N->bool` AFF_DIM_LE_UNIV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* all link vertices of degree 2: a PL 1-sphere *)
  SUBGOAL_THEN
   `(!a:real^N. {a} IN simplicial_link d w
                ==> CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)
    ==> pl_sphere 1 (UNIONS (simplicial_link d w))`
  ASSUME_TAC THENL
   [DISCH_THEN(LABEL_TAC "allTwo") THEN
    MP_TAC(ISPEC `simplicial_link d (w:real^N)` MOI_S4L_CM1_CIRCLES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN simplicial_link d w`)) THEN
      USE_THEN "allTwo" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN simplicial_link d w`)) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `components(UNIONS (simplicial_link d (w:real^N))) =
                  {UNIONS (simplicial_link d w)}`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  ASM_CASES_TAC
   `!a:real^N. {a} IN simplicial_link d w
               ==> CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2`
  THENL [DISJ1_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a0:real^N` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  (* a link vertex of degree 1: a PL 1-ball *)
  SUBGOAL_THEN `!v:real^N. {v} IN simplicial_link d w
                ==> CARD {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ v IN e} <= 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN simplicial_link d w`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ (a0:real^N) IN e}
                = 1`
  ASSUME_TAC THENL
   [USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{a0:real^N} IN simplicial_link d w`)) THEN
    UNDISCH_TAC `~(CARD {t | t IN d /\ aff_dim t = &2 /\
                             convex hull {w:real^N,a0} SUBSET t} = 2)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. (!a. a IN P ==> {a} IN simplicial_link d w) /\ ~(P = {}) /\
        (!a b. a IN P /\ ~(a = b) /\ segment[a,b] IN simplicial_link d w ==> b IN P)
        ==> !b:real^N. {b} IN simplicial_link d w ==> b IN P`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_LINK_GRAPH_CONN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8TB_K1_ARC THEN EXISTS_TAC `a0:real^N` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3TM_LINK_STAR = prove
 (`!c (w:real^N).
     lf_simplicial_complex c
     ==> simplicial_link {s | ?t. t IN c /\ w IN t /\ s face_of t} w = simplicial_link c w`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ALL_TAC] THEN
    EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LF_FACE];
    CONJ_TAC THENL [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_REFL; MOI_FM3_LF_CONVEX]]);;

let MOI_S3TM_STAR_TRIS = prove
 (`!c (w:real^N) e.
     lf_simplicial_complex c /\ w IN e
     ==> {t | t IN {s | ?t. t IN c /\ w IN t /\ s face_of t} /\ aff_dim t = &2 /\
              e SUBSET t} =
         {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE];
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_REFL; MOI_FM3_LF_CONVEX; SUBSET]]);;

let MOI_S3TM_VERTEX_LINK_LF = prove
 (`!c (w:real^N).
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     {w} IN c
     ==> (pl_sphere 1 (UNIONS (simplicial_link c w)) \/
          pl_ball 1 (UNIONS (simplicial_link c w))) /\
         ((!a. {a} IN simplicial_link c w
               ==> CARD {t | t IN c /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)
          ==> pl_sphere 1 (UNIONS (simplicial_link c w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `w:real^N`] MOI_S3TM_STAR_CH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`] MOI_S3TM_LINK_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a:real^N. {t | t IN {s | ?t. t IN c /\ w IN t /\ s face_of t} /\ aff_dim t = &2 /\
                    convex hull {w,a} SUBSET t} =
               {t | t IN c /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t}`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_S3TM_STAR_TRIS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (w:real^N) IN t /\ s face_of t}` THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`] MOI_S3TM_VERTEX_LINK_LOC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> s IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET c` THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^N->bool. t IN c /\ w IN t ==> t IN K`) (concl th))) THEN
    ASM_REWRITE_TAC[IN_SING];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3TM_DIM_LF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) IN K` THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_S3TM_PURE_LF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `w:real^N` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[FACE_OF_REFL; MOI_FM3_LF_CONVEX]];
      MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_PUNCT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `a:real^N`]
      MOI_S8TB_LINK_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t:real^N->bool. t IN c /\ w IN t ==> t IN K`) (concl th))) THEN
      ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_S3TM_EDGE_CARD_LF THEN ASM_SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 5: the boundary is the set of points without plane chart            *)
(* (MOI_S8TA_BD_NO_R2 and MOI_S8TA_NONR2_BD for locally finite c).          *)
(* ------------------------------------------------------------------------- *)

(* The closed star of a point z with its chart facts, packaged.             *)

let MOI_S3TM_STAR_PACK = prove
 (`!c (z:real^N).
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     z IN UNIONS c
     ==> simplicial_complex {s | ?t. t IN c /\ z IN t /\ s face_of t} /\
         {s | ?t. t IN c /\ z IN t /\ s face_of t} SUBSET c /\
         (!t. t IN c /\ z IN t ==> t IN {s | ?t. t IN c /\ z IN t /\ s face_of t}) /\
         (!s. s IN {s | ?t. t IN c /\ z IN t /\ s face_of t} ==> aff_dim s <= &2) /\
         (moi_s28_locally_r2 (UNIONS c) z <=>
          moi_s28_locally_r2 (UNIONS {s | ?t. t IN c /\ z IN t /\ s face_of t}) z) /\
         (moi_s28_locally_half (UNIONS c) z <=>
          moi_s28_locally_half (UNIONS {s | ?t. t IN c /\ z IN t /\ s face_of t}) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N`; `z:real^N`] MOI_S3TM_STAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3TM_DIM_LF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

let MOI_S3TM_CARRIER_LF = prove
 (`!c (y:real^N).
     lf_simplicial_complex c /\ y IN UNIONS c ==> ?s. s IN c /\ y IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (y:real^N) IN t /\ s face_of t}` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`] MOI_S8TA_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_sta_open_star c (y:real^N) SUBSET UNIONS K` THEN
    UNDISCH_TAC `(y:real^N) IN moi_sta_open_star c y` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET c` THEN
  UNDISCH_TAC `(s:real^N->bool) IN K` THEN SET_TAC[]);;

let MOI_S3TM_LINK_VERTEX_LF = prove
 (`!c (w:real^N) a.
     lf_simplicial_complex c /\ {w} IN c /\ {a} IN simplicial_link c w
     ==> ~(a = w) /\ {a} IN c /\ convex hull {w,a} IN c /\
         aff_dim(convex hull {w,a}) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`] MOI_S3TM_LINK_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (w:real^N) IN t /\ s face_of t}` THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `a:real^N`]
    MOI_S8TB_LINK_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^N->bool. t IN c /\ w IN t ==> t IN K`) (concl th))) THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET c` THEN
  UNDISCH_TAC `convex hull {w:real^N,a} IN K` THEN
  UNDISCH_TAC `{a:real^N} IN K` THEN SET_TAC[]);;

(* Points of boundary edges have no plane chart (MOI_S8TA_BD_NO_R2 for      *)
(* locally finite c: the local analysis MOI_S8TA_EDGE1_NO_R2 runs in the    *)
(* closed star of a point of the open edge).                                *)

let MOI_S3TM_BD_NO_R2_LF = prove
 (`!c (y:real^N).
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     y IN surface_boundary c
     ==> ~moi_s28_locally_r2 (UNIONS c) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN surface_boundary c` THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_OPEN] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?z:real^N. z IN relative_interior e /\ z IN oo` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(oo INTER closure(relative_interior e:real^N->bool) = {})` MP_TAC THENL
     [SUBGOAL_THEN `closure(relative_interior e:real^N->bool) = e` SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure(e:real^N->bool)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN
          ASM_MESON_TAC[MOI_FM3_LF_CONVEX];
          MATCH_MP_TAC CLOSURE_CLOSED THEN
          ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]];
        ASM SET_TAC[]];
      ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS c) (z:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N`] MOI_S3TM_STAR_PACK) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (z:real^N) IN t /\ s face_of t}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> s IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET c` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN c /\ e SUBSET t ==> t IN K` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^N->bool. t IN c /\ z IN t ==> t IN K`) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t:real^N->bool. {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = {t}`
  (X_CHOOSE_TAC `t:real^N->bool`) THENL
   [REWRITE_TAC[GSYM MOI_FSA_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_SCF_SC_FINITE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &2 /\ e SUBSET t /\
                (!t'. t' IN c /\ aff_dim t' = &2 /\ e SUBSET t' ==> t' = t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = {t:real^N->bool}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN K /\ t IN K` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^N->bool. t IN c /\ e SUBSET t ==> t IN K`) (concl th))) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e:real^N->bool`; `t:real^N->bool`;
                 `z:real^N`] MOI_S8TA_EDGE1_NO_R2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t':real^N->bool. t' IN c /\ aff_dim t' = &2 /\ e SUBSET t' ==> t' = t`) (concl th))) THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The carrier of a point without plane chart, if not a vertex, lies in the *)
(* boundary (the edge and triangle cases of MOI_S8TA_NONR2_BD).             *)

let MOI_S3TM_NONR2_CARRIER_LF = prove
 (`!c (z:real^N) s.
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     z IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) z /\
     s IN c /\ z IN relative_interior s /\ ~(aff_dim s = &0)
     ==> s SUBSET surface_boundary c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(z:real^N) IN relative_interior s` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s28_locally_half (UNIONS c) (z:real^N)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:real^N) IN UNIONS c`) o
      check (fun th -> can (term_match []
      `!y:real^N. y IN UNIONS c ==> P y \/ Q y`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N`] MOI_S3TM_STAR_PACK) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = {s | ?t. t IN c /\ (z:real^N) IN t /\ s face_of t}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN K ==> r IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET c` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN c /\ s SUBSET t ==> t IN K` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^N->bool. t IN c /\ z IN t ==> t IN K`) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN K` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^N->bool. t IN c /\ s SUBSET t ==> t IN K`) (concl th))) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1 \/ aff_dim s = &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
    UNDISCH_TAC `~(s:real^N->bool = {})` THEN REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(aff_dim(s:real^N->bool) = &0)` THEN INT_ARITH_TAC;
    ALL_TAC;
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`; `z:real^N`]
      MOI_S8TA_TRI_R2) THEN
    ASM_REWRITE_TAC[]] THEN
  (* an edge: exactly one triangle *)
  SUBGOAL_THEN `CARD {r | r IN c /\ aff_dim r = &2 /\ (s:real^N->bool) SUBSET r} = 1`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `?t:real^N->bool. t IN c /\ aff_dim t = &2 /\ s SUBSET t` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `?t':real^N->bool. t' IN c /\ aff_dim t' = &2 /\ s SUBSET t' /\
                                       ~(t' = t)` THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
         [UNDISCH_TAC `~(t':real^N->bool = t)` THEN MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(t:real^N->bool) IN K /\ t' IN K` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!t:real^N->bool. t IN c /\ s SUBSET t ==> t IN K`) (concl th))) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`; `t:real^N->bool`;
                       `t':real^N->bool`; `z:real^N`] MOI_S8TA_EDGE2_R2) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `{r | r IN c /\ aff_dim r = &2 /\ (s:real^N->bool) SUBSET r} = {t}`
        SUBST1_TAC THENL
         [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
          X_GEN_TAC `r:real^N->bool` THEN EQ_TAC THENL
           [STRIP_TAC THEN
            UNDISCH_TAC `~(?t':real^N->bool. t' IN c /\ aff_dim t' = &2 /\ s SUBSET t' /\
                                             ~(t' = t))` THEN
            REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `r:real^N->bool`) THEN
            ASM_REWRITE_TAC[];
            DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
          REWRITE_TAC[CARD_SING]]];
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`; `z:real^N`]
        MOI_S8TA_EDGE0_NO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `~(?t:real^N->bool. t IN c /\ aff_dim t = &2 /\ s SUBSET t)` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[surface_boundary] THEN
  MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* Every point without plane chart is on the boundary (MOI_S8TA_NONR2_BD    *)
(* for locally finite c; the proof is that of MOI_S8TA_NONR2_BD with the    *)
(* locally finite carrier, vertex-link and carrier-boundary lemmas).       *)

let MOI_S3TM_NONR2_BD_LF = prove
 (`!c (y:real^N).
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y) /\
     y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y
     ==> y IN surface_boundary c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z s. z IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) z /\
          s IN c /\ z IN relative_interior s /\ ~(aff_dim s = &0)
          ==> s SUBSET surface_boundary (c:(real^N->bool)->bool)`
  (LABEL_TAC "nv") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3TM_NONR2_CARRIER_LF THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S3TM_CARRIER_LF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THENL
   [ALL_TAC;
    USE_THEN "nv" (MP_TAC o SPECL [`y:real^N`; `s:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]] THEN
  (* the carrier is a vertex v = y *)
  UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `(y:real^N) IN relative_interior {v}` THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_S3TM_VERTEX_LINK_LF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(DISJ_CASES_TAC o CONJUNCT1)] THENL
   [SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS c) (v:real^N)` MP_TAC THENL
     [REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `moi_sta_open_star c (v:real^N)` THEN
      ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN; MOI_S8TA_CIRCLE_CHART;
                   MOI_S8TA_VERTEX_IN_OPEN_STAR];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_S8TA_ARC_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^2` (X_CHOOSE_THEN `k:real^2->real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (a:real^N->bool,{z:real^2 | &0 <= z$2}) (f,g)`) (concl th))) THEN
  ABBREV_TAC `z = (k:real^2->real^N) (basis 1)` THEN
  SUBGOAL_THEN `(basis 1:real^2) IN {z:real^2 | &0 <= z$2}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN moi_sta_open_star c v /\ (h:real^N->real^2) z = basis 1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s28_locally_half (UNIONS c) (z:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `moi_sta_open_star c (v:real^N)`;
                   `h:real^N->real^2`; `k:real^2->real^N`; `z:real^N`] MOI_S8TA_HCHART) THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^N = v)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(h:real^N->real^2) z = basis 1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$1`) THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN moi_sta_open_star c v` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N`] MOI_S3TM_CARRIER_LF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN s'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TA_OPEN_STAR_IN THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `z:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(aff_dim(s':real^N->bool) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(z:real^N) IN relative_interior {a}` THEN
    UNDISCH_TAC `(v:real^N) IN {a}` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':real^N->bool) SUBSET surface_boundary c` MP_TAC THENL
   [USE_THEN "nv" MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;



(* ------------------------------------------------------------------------- *)
(* Part 6: SURFACE_TRIANG.                                                   *)
(* ------------------------------------------------------------------------- *)

let SURFACE_TRIANG = prove
 (MOI_S30_SURFACE_TRIANG,
  DISCH_TAC THEN X_GEN_TAC `c:(real^N->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch")) THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (c:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_S3TM_VERTEX_LINK_LF) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `surface_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[surface_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC MOI_S3TM_BD_NO_R2_LF THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN MATCH_MP_TAC MOI_S3TM_NONR2_BD_LF THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_S3TM_VERTEX_LINK_LF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `a:real^N`]
      MOI_S3TM_LINK_VERTEX_LF) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull {v:real^N,a}`]
      MOI_S3TM_EDGE_CARD_LF) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {v:real^N,a} SUBSET surface_boundary c` MP_TAC THENL
     [REWRITE_TAC[surface_boundary] THEN
      MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_REWRITE_TAC[SUBSET_EMPTY; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]]]);;


(* ------------------------------------------------------------------------- *)
(* Part 7: POLY_DISK.  A triangulation m of a topological 2-cell d is a     *)
(* combinatorial surface with boundary the image of the circle (2D          *)
(* invariance SURF_INVARIANT of pc_moi_s28_trib, from the face complex of   *)
(* the standard triangle T, homeomorphic to the unit disk with frontier     *)
(* onto the circle by invariance of domain); d is simply connected, so      *)
(* chi(m) = 1 (Z2_SC_BOUNDARY), the boundary is one circle, and             *)
(* SURFACE_PLANAR with k = 0 and SQUARE_CELL give the PL 2-cell.            *)
(* ------------------------------------------------------------------------- *)

(* The face complex of a 2-simplex: duplicates of MOI_S3CA_FACE_CMWB2 and    *)
(* MOI_S3CA_FACE_SB (pc_moi_s30_cut_a; MOI_FRB_FACE_COMPLEX_CMWB2 of         *)
(* pc_moi_fnd_rnb2), not loaded to keep the load closure small.            *)

let MOI_S3TM_FACE_CMWB2 = prove
 (`!k:real^N->bool.
        &2 simplex k ==> combinatorial_manifold_with_boundary 2 {f | f face_of k}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_FMB_FACE_COMPLEX]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_ELIM_THM; FACE_OF_SING] THEN
  UNDISCH_TAC `&2 simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_LINK] THEN DISJ2_TAC THEN
  MATCH_MP_TAC PL_BALL_SIMPLEX THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `V DELETE (v:real^N)` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE] THEN
  UNDISCH_TAC `&(CARD(V:real^N->bool)):int = &2 + &1` THEN
  SUBGOAL_THEN `1 <= CARD(V:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN INT_ARITH_TAC);;

let MOI_S3TM_FACE_SB = prove
 (`!k:real^N->bool.
     &2 simplex k ==> surface_boundary {f | f face_of k} = relative_frontier k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim (k:real^N->bool) = &2 /\ convex k /\ polyhedron k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYHEDRON]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON] THEN
  REWRITE_TAC[surface_boundary; IN_ELIM_THM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; facet_of] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  ASM_CASES_TAC `(s:real^N->bool) face_of k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `aff_dim (s:real^N->bool) = &1` THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (s:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{r:real^N->bool | r face_of k /\ aff_dim r = &2 /\ s SUBSET r} = {k}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `k:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    REWRITE_TAC[CARD_SING]]);;

(* A homeomorphism between closed sets of the same space maps frontier onto *)
(* frontier (invariance of domain).                                         *)

let MOI_S3TM_HOMEO_FRONTIER = prove
 (`!(s:real^N->bool) t (f:real^N->real^N) g.
     homeomorphism (s,t) (f,g) /\ closed s /\ closed t
     ==> IMAGE f (frontier s) = frontier t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (interior s) SUBSET interior t` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `IMAGE (f:real^N->real^N) s = t`)) THEN
    MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN ASM_REWRITE_TAC[LE_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^N->real^N) (interior t) SUBSET interior s` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `IMAGE (g:real^N->real^N) t = s`)) THEN
    MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN ASM_REWRITE_TAC[LE_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `t:real^N->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) (interior s) SUBSET interior t` THEN
  UNDISCH_TAC `IMAGE (g:real^N->real^N) (interior t) SUBSET interior s` THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) s = t` THEN
  UNDISCH_TAC `!x:real^N. x IN s ==> (g:real^N->real^N) (f x) = x` THEN
  UNDISCH_TAC `!y:real^N. y IN t ==> (f:real^N->real^N) (g y) = y` THEN
  UNDISCH_TAC `IMAGE (g:real^N->real^N) t = s` THEN
  SET_TAC[]);;

(* A finite triangulation of a topological 2-cell: a combinatorial surface   *)
(* with boundary the image of the circle.                                    *)

let MOI_S3TM_DISK_TRI = prove
 (`!(m:(real^N->bool)->bool) (f:real^2->real^N) g.
     simplicial_complex m /\ homeomorphism (cball(vec 0,&1),UNIONS m) (f,g)
     ==> combinatorial_manifold_with_boundary 2 m /\
         surface_boundary m = IMAGE f (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `tr = convex hull {vec 0:real^2,basis 1,basis 2}` THEN
  SUBGOAL_THEN `&2 simplex (tr:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "tr" THEN MATCH_MP_TAC MOI_SS2_STD_TRIANGLE THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (tr:real^2->bool) /\ compact tr /\ ~(interior tr = {})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `convex (tr:real^2->bool) /\ compact tr` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "tr" THEN SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL;
                                    FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP AFF_DIM_NONEMPTY_INTERIOR_EQ th)]) THEN
    REWRITE_TAC[DIMINDEX_2] THEN MATCH_MP_TAC AFF_DIM_SIMPLEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tr:real^2->bool`; `vec 0:real^2`; `&1`] HOMEOMORPHIC_CONVEX_COMPACT_CBALL) THEN
  ASM_REWRITE_TAC[REAL_LT_01; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:real^2->real^2` (X_CHOOSE_TAC `k0:real^2->real^2`)) THEN
  SUBGOAL_THEN `IMAGE (h0:real^2->real^2) (relative_frontier tr) = sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    REWRITE_TAC[GSYM FRONTIER_CBALL] THEN MATCH_MP_TAC MOI_S3TM_HOMEO_FRONTIER THEN
    EXISTS_TAC `k0:real^2->real^2` THEN
    ASM_SIMP_TAC[CLOSED_CBALL; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (tr,UNIONS m) ((f:real^2->real^N) o (h0:real^2->real^2),
                                            k0 o (g:real^N->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{s:real^2->bool | s face_of tr}`; `m:(real^N->bool)->bool`;
                 `(f:real^2->real^N) o (h0:real^2->real^2)`; `(k0:real^2->real^2) o (g:real^N->real^2)`]
    (MP SURF_INVARIANT (CONJ (INST_TYPE [`:M`,`:N`] SURF_CHARTS) SURF_LOCAL))) THEN
  MP_TAC(ISPECL [`&2:int`; `tr:real^2->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_S3TM_FACE_CMWB2; MOI_S3TM_FACE_SB; MOI_SCF_SC_FINITE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    rand(concl th) = `surface_boundary (m:(real^N->bool)->bool)`)) THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]);;

let POLY_DISK = prove
 (MOI_S30_POLY_DISK,
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "Z2")
    (LABEL_TAC "PLAN"))) THEN
  MAP_EVERY X_GEN_TAC [`d:real^N->bool`; `f:real^2->real^N`; `g:real^N->real^2`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (d:real^N->bool) /\ connected d /\ ~(d = {})` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = d`)) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; CBALL_EQ_EMPTY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[CONNECTED_CBALL];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^N->real^2`]
    MOI_S3TM_DISK_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (f:real^2->real^N) (sphere(vec 0,&1))) /\
                ~(IMAGE (f:real^2->real^N) (sphere(vec 0,&1)) = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  (* chi = 1 *)
  SUBGOAL_THEN `complex_euler (m:(real^N->bool)->bool) = &1` ASSUME_TAC THENL
   [USE_THEN "Z2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `simply_connected (d:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `d:real^N->bool`]
        HOMEOMORPHIC_SIMPLY_CONNECTED) THEN
      SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_CBALL] THEN
      REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    DISCH_TAC THEN X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* one boundary circle *)
  USE_THEN "PLAN" (MP_TAC o SPEC `m:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `components (IMAGE (f:real^2->real^N) (sphere(vec 0,&1))) =
                {IMAGE f (sphere(vec 0,&1))}`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; ALL_TAC] THEN
  REWRITE_TAC[CARD_SING; ADD_CLAUSES; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^2->real^N` (X_CHOOSE_THEN `g':real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhand(concl th) = `IMAGE (f':real^2->real^N) (frontier (holed_disk_model 0))`)) THEN
  MATCH_MP_TAC SQUARE_CELL THEN EXISTS_TAC `g':real^N->real^2` THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 8: PL_TORUS_COMPLEX.  A PL torus t is a polyhedron (PL image of the *)
(* model) whose points all have plane charts (MOI_S8TO_PL_TORUS_R2 of       *)
(* pc_moi_s28_torus), so a triangulation is a combinatorial surface with    *)
(* empty boundary by SURFACE_TRIANG (antecedent); chi 0 by EULER_VALUES     *)
(* (antecedent).                                                            *)
(* ------------------------------------------------------------------------- *)

let PL_TORUS_COMPLEX = prove
 (MOI_S30_PL_TORUS_COMPLEX,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ST") (LABEL_TAC "EV")) THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                       `g:real^N->real^(2,2)finite_sum`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `pl_polyhedron (t:real^N->bool) /\ connected t /\ ~(t = {})`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^(2,2)finite_sum->real^N) pl_torus_model = t`)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[MOI_S8TO_MODEL_FACTS];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[MOI_S8TO_MODEL_FACTS];
      REWRITE_TAC[IMAGE_EQ_EMPTY; pl_torus_model; GSYM moi_fps_sq] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                  MOI_FPS_SQ] THEN
      MAP_EVERY EXISTS_TAC [`vec 1:real^2`; `vec 1:real^2`] THEN
      REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:(real^N->bool)->bool` THEN
  SUBGOAL_THEN `FINITE (m:(real^N->bool)->bool) /\ lf_simplicial_complex m`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN t ==> moi_s28_locally_r2 t y` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TO_PL_TORUS_R2 THEN
    MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^N`;
                          `g:real^N->real^(2,2)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "ST" (MP_TAC o SPEC `m:(real^N->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!y:real^N. y IN t ==> moi_s28_locally_r2 t y` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "EV" (MP_TAC o SPEC `m:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3TM_DIM_LF THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o el 5 o CONJUNCTS) THEN
  MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^N`;
                        `g:real^N->real^(2,2)finite_sum`] THEN
  ASM_REWRITE_TAC[]);;

