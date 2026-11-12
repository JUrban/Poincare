(* ========================================================================= *)
(* pc_moi_s34_cellnba: Moise Sec 34, Lemma 3 (GTM 47, p.240), first half:   *)
(* a small PL 3-ball around h(s) inside a given open set, for a 2-simplex s *)
(* of kk (the general position half is pc_moi_s34_cellnbb and the assembly  *)
(* CELLNB_FND is pc_moi_s34_cellnb).  Main theorem                          *)
(*   INIT_BALL : |- MOI_S4C_INIT_BALL (defined below)                       *)
(* Route: a PL 3-simplex image B around s in the preimage of the open set   *)
(* (MOI_FND_SIMPLEX_SMALL_CELL of pc_moi_fnd_stmt2.ml, an antecedent,       *)
(* proved in pc_moi_fnd_rnsc; MOI_S4C_FND_SMALL_CELL derives it from        *)
(* MOI_FND_DERIVED_NBHD_BALL: the second-derived neighbourhood of s in a    *)
(* fine iterated barycentric subdivision of the finite closed star of s,    *)
(* small by MOI_FND_DERIVED_NBHD_SMALL, is a PL 3-cell); a homeomorphism of *)
(* cball(0,2) in real^3 onto the model simplex, followed by the cell map    *)
(* and h, gives two topological 3-cells c1 = G(cball(0,rho)) and            *)
(* c2 = G(cball(0,2)) with h(s) inside c1 and a spherical shell between     *)
(* (invariance of domain); Moise 30.5 (MOISE_305_STATEMENT, an antecedent)  *)
(* gives the PL ball.                                                       *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_fnd_stmt2.ml";;
needs "src/pc_moi_s34_frame.ml";;
needs "src/pc_moi_s34_src.ml";;
needs "src/pc_moi_p305.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_S4C_INIT_BALL_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (s:real^N->bool) (w0:real^3->bool).
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\ s IN moi_s34_simp kk (&2) /\
     open w0 /\ IMAGE h s SUBSET w0
     ==> ?c. pl_ball 3 c /\ IMAGE h s SUBSET interior c /\ c SUBSET w0`;;

let MOI_S4C_INIT_BALL =
  mk_imp(MOI_FND_SIMPLEX_SMALL_CELL,
         mk_imp(`MOISE_305_STATEMENT`,MOI_S4C_INIT_BALL_BODY));;

(* ------------------------------------------------------------------------- *)
(* Part 1: the finite closed star complex of a simplex, and a small PL      *)
(* 3-cell around the simplex inside a relatively open set (the derived      *)
(* neighbourhood in an iterated barycentric subdivision).                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4C_STAR_COMPLEX = prove
 (`!(tt:(real^N->bool)->bool) s.
     lf_simplicial_complex tt /\ s IN tt
     ==> simplicial_complex {f | ?r. r IN tt /\ ~(r INTER s = {}) /\ f face_of r} /\
         simplicial_subcomplex {f | ?r. r IN tt /\ ~(r INTER s = {}) /\ f face_of r} tt /\
         (~(s = {})
          ==> simplicial_subcomplex {f | f face_of s}
                {f | ?r. r IN tt /\ ~(r INTER s = {}) /\ f face_of r}) /\
         (!v. v IN s
              ==> simplicial_link
                    {f | ?r. r IN tt /\ ~(r INTER s = {}) /\ f face_of r} v =
                  simplicial_link tt v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `t0 = {f:real^N->bool | ?r. r IN tt /\ ~(r INTER s = {}) /\ f face_of r}` THEN
  SUBGOAL_THEN `simplicial_subcomplex (t0:(real^N->bool)->bool) tt` ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN MATCH_MP_TAC MOI_FDN_MEETS_FACES_SUBCOMPLEX THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (t0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN MATCH_MP_TAC MOI_FDN_MEETS_FACES_FINITE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FDN_LF_COMPACT_MEETS_FINITE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      UNDISCH_TAC `(s:real^N->bool) IN tt` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (t0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN EXPAND_TAC "t0" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[INTER_IDEMPOT];
      MESON_TAC[FACE_OF_TRANS]];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:real^N->bool` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN EQ_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (t0:(real^N->bool)->bool) tt` THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `~((t:real^N->bool) INTER s = {})` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:real^N) IN t` THEN UNDISCH_TAC `(v:real^N) IN s` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^N->bool) face_of t` ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_REFL THEN
      UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1) THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    EXPAND_TAC "t0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

let MOI_S4C_ITER_FINITE = prove
 (`!(c:(real^N->bool)->bool) n.
     FINITE c ==> FINITE (ITER n barycentric_subdivision c)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; MOI_BAR_SUBDIVISION_FINITE]);;

let MOI_S4C_SIMPLEX_PL_BALL = prove
 (`!s:real^N->bool.
     ~(s = {}) /\ (?n. n simplex s) /\ aff_dim s <= &3
     ==> ?m. m <= 3 /\ pl_ball m s`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:int`) ASSUME_TAC)) THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = n` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `?m. (n:int) = &m` MP_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN
    UNDISCH_TAC `aff_dim(s:real^N->bool) = n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[AFF_DIM_POS_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  EXISTS_TAC `m:num` THEN CONJ_TAC THENL
   [UNDISCH_TAC `aff_dim(s:real^N->bool) <= &3` THEN ASM_REWRITE_TAC[INT_OF_NUM_LE];
    ALL_TAC] THEN
  REWRITE_TAC[pl_ball] THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let MOI_S4C_SMALL_CELL = prove
 (mk_imp(MOI_FND_DERIVED_NBHD_BALL,
  `!(tt:(real^N->bool)->bool) s v.
     lf_simplicial_complex tt /\ s IN tt /\ ~(s = {}) /\ aff_dim s <= &3 /\
     (!w. {w} IN tt /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link tt w))) /\
     open_in (subtopology euclidean (UNIONS tt)) v /\ s SUBSET v
     ==> ?k (f:real^N->real^N) g.
           &3 simplex k /\ pl_homeomorphism (k,IMAGE f k) (f,g) /\
           IMAGE f k SUBSET v /\ s SUBSET IMAGE f (relative_interior k)`),
  DISCH_THEN(LABEL_TAC "fnd") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sph") STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4C_STAR_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `t0 = {f:real^N->bool | ?r. r IN tt /\ ~(r INTER s = {}) /\ f face_of r}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk")))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ls = {f:real^N->bool | f face_of s}` THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `d:int`) THENL
   [UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (ls:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (t0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (t0:(real^N->bool)->bool)` THEN
    SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (t0:(real^N->bool)->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (t0:(real^N->bool)->bool) tt` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS t0` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (ls:(real^N->bool)->bool) t0` THEN
    UNDISCH_TAC `UNIONS (ls:(real^N->bool)->bool) = s` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N. {u} IN ls ==> pl_sphere 2 (UNIONS (simplicial_link t0 u))`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^N) IN s /\ {u} IN tt` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{u:real^N} IN ls` THEN EXPAND_TAC "ls" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN SET_TAC[];
        UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    USE_THEN "lk" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(u:real^N) IN s`)]) THEN
    USE_THEN "sph" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `ls:(real^N->bool)->bool`;
                 `(v:real^N->bool) INTER UNIONS t0`] DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_INTER] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `UNIONS tt:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `UNIONS tt INTER (v:real^N->bool) = v` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `ls:(real^N->bool)->bool`; `n:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t1 = ITER n barycentric_subdivision (t0:(real^N->bool)->bool)` THEN
  ABBREV_TAC `l1 = ITER n barycentric_subdivision (ls:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (l1:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "l1" THEN MATCH_MP_TAC MOI_S4C_ITER_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. {w} IN l1 ==> pl_sphere 2 (UNIONS (simplicial_link t1 w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{w:real^N} IN t1 /\ w IN s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `simplicial_subcomplex (l1:(real^N->bool)->bool) t1` THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o REWRITE_RULE[simplicial_subcomplex]) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `UNIONS (l1:(real^N->bool)->bool) = s` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4R_LINK THEN
    MAP_EVERY EXISTS_TAC [`t0:(real^N->bool)->bool`; `ls:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. m <= 3 /\ pl_ball m (UNIONS (l1:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4C_SIMPLEX_PL_BALL THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `d:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "fnd" (MP_TAC o ISPECL [`t1:(real^N->bool)->bool`; `l1:(real^N->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) k = derived_nbhd t1 l1` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k,derived_nbhd t1 l1) (f:real^N->real^N,g)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `derived_nbhd t1 l1 SUBSET (v:real^N->bool) INTER UNIONS t0` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t1:(real^N->bool)->bool`; `l1:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER derived_frontier t1 l1 = {}` MP_TAC THENL
   [REWRITE_TAC[derived_frontier; frontier_of] THEN
    UNDISCH_TAC `UNIONS (l1:(real^N->bool)->bool)
                 SUBSET (subtopology euclidean (UNIONS t1)) interior_of
                        derived_nbhd t1 l1` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET derived_nbhd t1 l1` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (UNIONS t1)) interior_of
                (derived_nbhd t1 l1:real^N->bool)` THEN
    REWRITE_TAC[INTERIOR_OF_SUBSET] THEN
    UNDISCH_TAC `UNIONS (l1:(real^N->bool)->bool)
                 SUBSET (subtopology euclidean (UNIONS t1)) interior_of
                        derived_nbhd t1 l1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) k = derived_nbhd t1 l1` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `derived_frontier t1 l1 = IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `k:real^N->bool` CLOSURE_SUBSET) THEN
  REWRITE_TAC[relative_frontier] THEN SET_TAC[]);;

(* The two split terms of pc_moi_fnd_stmt2.ml follow from                   *)
(* MOI_FND_DERIVED_NBHD_BALL (sanity checks of the split; INIT_BALL takes   *)
(* MOI_FND_SIMPLEX_SMALL_CELL as its antecedent).                           *)

let MOI_S4C_FND_SMALL_CELL = prove
 (mk_imp(MOI_FND_DERIVED_NBHD_BALL, MOI_FND_SIMPLEX_SMALL_CELL),
  DISCH_THEN(LABEL_TAC "sc" o MATCH_MP MOI_S4C_SMALL_CELL) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `s:real^N->bool`;
                       `v:real^N->bool`] THEN
  STRIP_TAC THEN
  USE_THEN "sc" (MP_TAC o SPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`;
                                 `v:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `aff_dim(s:real^N->bool) <= &2` THEN
    INT_ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;

let MOI_S4C_FND_NBHD_SIMPLEX = prove
 (mk_imp(MOI_FND_DERIVED_NBHD_BALL, MOI_FND_DERIVED_NBHD_SIMPLEX),
  DISCH_THEN(LABEL_TAC "fnd") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `s:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sph"))))) THEN
  SUBGOAL_THEN `(?n. n simplex (s:real^N->bool)) /\
                (!f:real^N->bool. f face_of s ==> f IN t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (s:real^N->bool) /\ convex s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {f:real^N->bool | f face_of s} = s` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
      DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[FACE_OF_REFL]];
    ALL_TAC] THEN
  USE_THEN "fnd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_OF_TRANS];
    ASM_SIMP_TAC[FINITE_POLYTOPE_FACES];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "sph" MATCH_MP_TAC THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SING_SUBSET];
    DISJ1_TAC THEN MATCH_MP_TAC MOI_S4C_SIMPLEX_PL_BALL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `aff_dim(s:real^N->bool) <= &2` THEN INT_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: images of round balls of real^3 under a continuous injective     *)
(* map G on cball(0,2): interiors and frontiers (invariance of domain), and *)
(* the spherical shell between the images of cball(0,rho) and cball(0,2).  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4C_IMAGE_CBALL = prove
 (`!(G:real^3->real^3) R r.
     G continuous_on cball(vec 0,R) /\
     (!x y. x IN cball(vec 0,R) /\ y IN cball(vec 0,R) /\ G x = G y ==> x = y) /\
     &0 < r /\ r <= R
     ==> interior (IMAGE G (cball(vec 0,r))) = IMAGE G (ball(vec 0,r)) /\
         frontier (IMAGE G (cball(vec 0,r))) = IMAGE G (sphere(vec 0,r)) /\
         IMAGE G (cball(vec 0,r)) homeomorphic cball(vec 0:real^3,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(vec 0:real^3,r) SUBSET cball(vec 0,R)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:real^3->real^3) continuous_on cball(vec 0,r) /\
    (!x y. x IN cball(vec 0,r) /\ y IN cball(vec 0,r) /\ G x = G y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^3,r)`; `G:real^3->real^3`;
                 `IMAGE (G:real^3->real^3) (cball(vec 0,r))`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(X_CHOOSE_TAC `G':real^3->real^3`) THEN
  SUBGOAL_THEN
   `interior (IMAGE (G:real^3->real^3) (cball(vec 0,r))) = IMAGE G (ball(vec 0,r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN IMAGE (G:real^3->real^3) (cball(vec 0,r))` MP_TAC THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM INTERIOR_CBALL] THEN MATCH_MP_TAC MOI_P35_HOMEO_INTERIOR THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (G:real^3->real^3) (cball(vec 0,r))`;
                            `G:real^3->real^3`; `G':real^3->real^3`] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
        MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL; SUBSET]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `closure (IMAGE (G:real^3->real^3) (cball(vec 0,r))) = IMAGE G (cball(vec 0,r))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CBALL_DIFF_BALL] THEN
    UNDISCH_TAC `!x y. x IN cball(vec 0:real^3,r) /\ y IN cball(vec 0,r) /\
                       (G:real^3->real^3) x = G y ==> x = y` THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `r:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
    MP_TAC(ISPECL [`IMAGE (G:real^3->real^3) (cball(vec 0,r))`; `cball(vec 0:real^3,r)`;
                   `cball(vec 0:real^3,&1)`] HOMEOMORPHIC_TRANS) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`G:real^3->real^3`; `G':real^3->real^3`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[HOMEOMORPHIC_CBALLS_EQ] THEN ASM_REWRITE_TAC[REAL_LT_01]]]);;

let MOI_S4C_ANNULUS_CLOSURE = prove
 (`!rho. &0 < rho /\ rho < &2
         ==> closure (cball(vec 0:real^3,&2) DIFF cball(vec 0,rho)) =
             {y:real^3 | rho <= norm y /\ norm y <= &2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y:real^3 | rho <= norm y /\ norm y <= &2} =
                cball(vec 0,&2) DIFF ball(vec 0,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_DIFF THEN
      REWRITE_TAC[CLOSED_CBALL; OPEN_BALL]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `norm(y:real^3) = rho` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    REWRITE_TAC[IN_DIFF; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `t = min (e / &2) ((&2 - rho) / &2)` THEN
  SUBGOAL_THEN `&0 < t /\ t < e /\ rho + t < &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `((rho + t) / rho) % (y:real^3)` THEN
  REWRITE_TAC[IN_DIFF; IN_CBALL_0; NORM_MUL; dist] THEN
  SUBGOAL_THEN `abs((rho + t) / rho) * norm(y:real^3) = rho + t` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (rho + t) / rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `((rho + t) / rho) % (y:real^3) - y = (t / rho) % y` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `a % y - y:real^N = (a - &1) % y`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(t / rho) * rho = t` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < t / rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD;
    ASM_REAL_ARITH_TAC]);;

let MOI_S4C_RADIAL_CONT = prove
 (`!rho. (\y:real^3. ((rho + (norm y - &1) * (&2 - rho)) / norm y) % y)
           continuous_on {y:real^3 | &1 <= norm y /\ norm y <= &2}`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_ADD] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_ID];
    MP_TAC(ISPECL [`norm:real^3->real`; `{y:real^3 | &1 <= norm y /\ norm y <= &2}`]
      CONTINUOUS_ON_INV) THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; o_DEF; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN REAL_ARITH_TAC]);;
let MOI_S4C_RADIAL_NORM = prove
 (`!rho (y:real^3).
     &0 < rho /\ rho < &2 /\ &1 <= norm y
     ==> norm(((rho + (norm y - &1) * (&2 - rho)) / norm y) % y) =
         rho + (norm y - &1) * (&2 - rho)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `&0 < (rho + (norm(y:real^3) - &1) * (&2 - rho)) / norm y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let MOI_S4C_RADIAL_PRE = prove
 (`!rho (z:real^3).
     &0 < rho /\ rho < &2 /\ rho <= norm z /\ norm z <= &2
     ==> norm(((&1 + (norm z - rho) / (&2 - rho)) / norm z) % z) =
         &1 + (norm z - rho) / (&2 - rho) /\
         ((rho + (norm(((&1 + (norm z - rho) / (&2 - rho)) / norm z) % z) - &1) *
                 (&2 - rho)) /
          norm(((&1 + (norm z - rho) / (&2 - rho)) / norm z) % z)) %
         (((&1 + (norm z - rho) / (&2 - rho)) / norm z) % z) = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (norm(z:real^3) - rho) / (&2 - rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(((&1 + (norm z - rho) / (&2 - rho)) / norm z) % (z:real^3)) =
                &1 + (norm z - rho) / (&2 - rho)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&0 < (&1 + (norm(z:real^3) - rho) / (&2 - rho)) / norm z`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(norm(z:real^3) = &0) /\ ~(&2 - rho = &0) /\
                ~(&1 + (norm(z:real^3) - rho) / (&2 - rho) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;
let MOI_S4C_RADIAL_BOUNDS = prove
 (`!rho n. &0 < rho /\ rho < &2 /\ &1 <= n /\ n <= &2
           ==> rho <= rho + (n - &1) * (&2 - rho) /\
               rho + (n - &1) * (&2 - rho) <= &2 /\
               (rho + (n - &1) * (&2 - rho) = rho <=> n = &1) /\
               (rho + (n - &1) * (&2 - rho) = &2 <=> n = &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (n - &1) * (&2 - rho) /\ (n - &1) * (&2 - rho) <= &1 * (&2 - rho)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  (SUBGOAL_THEN `~(&2 - rho = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD));;

let MOI_S4C_PRE_BOUNDS = prove
 (`!rho m. &0 < rho /\ rho < &2 /\ rho <= m /\ m <= &2
           ==> &1 <= &1 + (m - rho) / (&2 - rho) /\
               &1 + (m - rho) / (&2 - rho) <= &2 /\
               (&1 + (m - rho) / (&2 - rho) = &1 <=> m = rho) /\
               (&1 + (m - rho) / (&2 - rho) = &2 <=> m = &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (m - rho) / (&2 - rho) /\ (m - rho) / (&2 - rho) <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  (SUBGOAL_THEN `~(&2 - rho = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD));;
let MOI_S4C_RADIAL_FACTS = prove
 (`!rho. &0 < rho /\ rho < &2
         ==> (!x y:real^3. x IN {y:real^3 | &1 <= norm y /\ norm y <= &2} /\
                           y IN {y:real^3 | &1 <= norm y /\ norm y <= &2} /\
                           ((rho + (norm x - &1) * (&2 - rho)) / norm x) % x =
                           ((rho + (norm y - &1) * (&2 - rho)) / norm y) % y
                           ==> x = y) /\
             IMAGE (\y:real^3. ((rho + (norm y - &1) * (&2 - rho)) / norm y) % y)
                   {y:real^3 | &1 <= norm y /\ norm y <= &2} =
             {y:real^3 | rho <= norm y /\ norm y <= &2} /\
             IMAGE (\y:real^3. ((rho + (norm y - &1) * (&2 - rho)) / norm y) % y)
                   (sphere(vec 0,&1)) = sphere(vec 0,rho) /\
             IMAGE (\y:real^3. ((rho + (norm y - &1) * (&2 - rho)) / norm y) % y)
                   (sphere(vec 0,&2)) = sphere(vec 0,&2)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:real^3. &1 <= norm y /\ norm y <= &2
               ==> norm(((rho + (norm y - &1) * (&2 - rho)) / norm y) % y) =
                   rho + (norm y - &1) * (&2 - rho) /\
                   rho <= rho + (norm y - &1) * (&2 - rho) /\
                   rho + (norm y - &1) * (&2 - rho) <= &2 /\
                   (rho + (norm y - &1) * (&2 - rho) = rho <=> norm y = &1) /\
                   (rho + (norm y - &1) * (&2 - rho) = &2 <=> norm y = &2)`
  (LABEL_TAC "fw") THENL
   [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4C_RADIAL_NORM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4C_RADIAL_BOUNDS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. rho <= norm z /\ norm z <= &2
               ==> ?y. (&1 <= norm y /\ norm y <= &2) /\
                       (norm y = &1 <=> norm z = rho) /\
                       (norm y = &2 <=> norm z = &2) /\
                       z = ((rho + (norm y - &1) * (&2 - rho)) / norm y) % y`
  (LABEL_TAC "bw") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `((&1 + (norm z - rho) / (&2 - rho)) / norm z) % (z:real^3)` THEN
    MP_TAC(ISPECL [`rho:real`; `z:real^3`] MOI_S4C_RADIAL_PRE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`rho:real`; `norm(z:real^3)`] MOI_S4C_PRE_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`rho:real`; `norm(z:real^3)`] MOI_S4C_PRE_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`rho:real`; `norm(z:real^3)`] MOI_S4C_PRE_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN REFL_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `norm(x:real^3) = norm(y:real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:real^3->real`) THEN
      USE_THEN "fw" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th (CONJ (ASSUME `&1 <= norm(x:real^3)`) (ASSUME `norm(x:real^3) <= &2`)))]) THEN
      USE_THEN "fw" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th (CONJ (ASSUME `&1 <= norm(y:real^3)`) (ASSUME `norm(y:real^3) <= &2`)))]) THEN
      SUBGOAL_THEN `~(&2 - rho = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    UNDISCH_TAC `((rho + (norm(x:real^3) - &1) * (&2 - rho)) / norm x) % x =
                 ((rho + (norm(y:real^3) - &1) * (&2 - rho)) / norm y) % y` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
    MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      USE_THEN "fw" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      DISCH_TAC THEN USE_THEN "bw" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "fw" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      DISCH_TAC THEN USE_THEN "bw" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "fw" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      DISCH_TAC THEN USE_THEN "bw" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;
let MOI_S4C_BALL_PAIR = prove
 (`!(G:real^3->real^3) rho.
     G continuous_on cball(vec 0,&2) /\
     (!x y. x IN cball(vec 0,&2) /\ y IN cball(vec 0,&2) /\ G x = G y ==> x = y) /\
     &0 < rho /\ rho < &2
     ==> IMAGE G (cball(vec 0,rho)) homeomorphic cball(vec 0:real^3,&1) /\
         IMAGE G (cball(vec 0,&2)) homeomorphic cball(vec 0:real^3,&1) /\
         IMAGE G (cball(vec 0,rho)) SUBSET interior (IMAGE G (cball(vec 0,&2))) /\
         IMAGE G (ball(vec 0,rho)) SUBSET interior (IMAGE G (cball(vec 0,rho))) /\
         spherical_shell
           (closure (IMAGE G (cball(vec 0,&2)) DIFF IMAGE G (cball(vec 0,rho))))
           (frontier (IMAGE G (cball(vec 0,rho))))
           (frontier (IMAGE G (cball(vec 0,&2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `&2`; `rho:real`] MOI_S4C_IMAGE_CBALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `&2`; `&2`] MOI_S4C_IMAGE_CBALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure (IMAGE (G:real^3->real^3) (cball(vec 0,&2)) DIFF IMAGE G (cball(vec 0,rho))) =
    IMAGE G {y:real^3 | rho <= norm y /\ norm y <= &2}`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (G:real^3->real^3) (cball(vec 0,&2)) DIFF IMAGE G (cball(vec 0,rho)) =
      IMAGE G (cball(vec 0,&2) DIFF cball(vec 0,rho))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> can (find_term ((=) `(G:real^3->real^3) x = G y`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN cball(vec 0,rho)` THEN
      REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `rho:real` MOI_S4C_ANNULUS_CLOSURE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `closure(cball(vec 0:real^3,&2) DIFF cball(vec 0,rho)) SUBSET
                  cball(vec 0,&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[COMPACT_CLOSURE] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
          MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^3,&2)` THEN
          REWRITE_TAC[BOUNDED_CBALL] THEN SET_TAC[]]];
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(SPEC `rho:real` MOI_S4C_RADIAL_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "im")
    (CONJUNCTS_THEN2 (LABEL_TAC "s1") (LABEL_TAC "s2")))) THEN
  REWRITE_TAC[spherical_shell] THEN
  ABBREV_TAC `rr = \y:real^3. ((rho + (norm y - &1) * (&2 - rho)) / norm y) % y` THEN
  SUBGOAL_THEN `{y:real^3 | rho <= norm y /\ norm y <= &2} SUBSET cball(vec 0,&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`{y:real^3 | &1 <= norm y /\ norm y <= &2}`;
                 `(G:real^3->real^3) o (rr:real^3->real^3)`;
                 `IMAGE (G:real^3->real^3) {y:real^3 | rho <= norm y /\ norm y <= &2}`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | &1 <= norm y /\ norm y <= &2} =
                    cball(vec 0,&2) DIFF ball(vec 0,&1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [EXPAND_TAC "rr" THEN REWRITE_TAC[MOI_S4C_RADIAL_CONT];
        USE_THEN "im" SUBST1_TAC THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
      REWRITE_TAC[IMAGE_o] THEN USE_THEN "im" SUBST1_TAC THEN REFL_TAC;
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
      STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(rr:real^3->real^3) x IN {y:real^3 | rho <= norm y /\ norm y <= &2} /\
                    rr y IN {y:real^3 | rho <= norm y /\ norm y <= &2}`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "im" (fun th -> REWRITE_TAC[GSYM th]) THEN
        CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(rr:real^3->real^3) x = rr y` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o
          check (fun th -> can (find_term ((=) `(G:real^3->real^3) x = G y`)) (concl th))) THEN
        ASM_MESON_TAC[SUBSET];
        EXPAND_TAC "rr" THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `kk:real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`(G:real^3->real^3) o (rr:real^3->real^3)`; `kk:real^3->real^3`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL
   [USE_THEN "s1" (fun th -> REWRITE_TAC[th]); USE_THEN "s2" (fun th -> REWRITE_TAC[th])]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: the theorem INIT_BALL.                                            *)
(* ------------------------------------------------------------------------- *)

let INIT_BALL = prove
 (MOI_S4C_INIT_BALL,
  DISCH_THEN(LABEL_TAC "fnd") THEN REWRITE_TAC[MOISE_305_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "m305") THEN
  MAP_EVERY X_GEN_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `s:real^N->bool`; `w0:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4K_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4K_FT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[moi_s34_emb] o
    check (fun th -> concl th = `moi_s34_emb (h:real^N->real^3) (UNIONS tt)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hinj")) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN tt` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. {w} IN tt /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link tt w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `graph_in_complex tt (skeleton 1 (kk:(real^N->bool)->bool))` THEN
    REWRITE_TAC[graph_in_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[MOI_S4K_SKEL_VERTEX] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
      MOI_S4K_TUBE_FACTS) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o el 3 o CONJUNCTS) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`{w:real^N}`; `s:real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{w:real^N} INTER s = {w}` (fun th -> SIMP_TAC[th]) THEN
    UNDISCH_TAC `(w:real^N) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^3`; `UNIONS tt:real^N->bool`; `w0:real^3->bool`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "fnd" (fun th -> MP_TAC(SPECL
    [`tt:(real^N->bool)->bool`; `s:real^N->bool`;
     `{x:real^N | x IN UNIONS tt /\ (h:real^N->real^3) x IN w0}`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) s SUBSET w0` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS tt` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k /\ aff_dim k = &3`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^3,&2)`; `k:real^N->bool`]
    HOMEOMORPHIC_CONVEX_COMPACT_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CBALL; COMPACT_CBALL; AFF_DIM_CBALL; DIMINDEX_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^N` (X_CHOOSE_THEN `psi:real^N->real^3`
    (LABEL_TAC "ph"))) THEN
  USE_THEN "ph" (STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  SUBGOAL_THEN `(f:real^N->real^N) continuous_on k /\
                (!x y. x IN k /\ y IN k /\ f x = f y ==> x = y) /\
                (g:real^N->real^N) continuous_on IMAGE f k /\
                (!x. x IN k ==> g(f x) = x) /\ (!y. y IN IMAGE f k ==> f(g y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k,IMAGE (f:real^N->real^N) k) (f,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) k SUBSET UNIONS tt /\
                IMAGE (h:real^N->real^3) (IMAGE f k) SUBSET w0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) k SUBSET
                 {x:real^N | x IN UNIONS tt /\ (h:real^N->real^3) x IN w0}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `G = (h:real^N->real^3) o (f:real^N->real^N) o (phi:real^3->real^N)` THEN
  SUBGOAL_THEN
   `(G:real^3->real^3) continuous_on cball(vec 0,&2) /\
    (!x y. x IN cball(vec 0,&2) /\ y IN cball(vec 0,&2) /\ G x = G y ==> x = y) /\
    IMAGE G (cball(vec 0,&2)) = IMAGE (h:real^N->real^3) (IMAGE (f:real^N->real^N) k)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[IMAGE_o; o_THM] THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]]] THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(phi:real^3->real^N) x IN k /\ phi y IN k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (phi:real^3->real^N) (cball(vec 0,&2)) = k` THEN
        UNDISCH_TAC `(x:real^3) IN cball(vec 0,&2)` THEN
        UNDISCH_TAC `(y:real^3) IN cball(vec 0,&2)` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^N->real^N) ((phi:real^3->real^N) x) = f (phi y)` MP_TAC THENL
       [USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (f:real^N->real^N) k SUBSET UNIONS tt` THEN
        UNDISCH_TAC `(phi:real^3->real^N) x IN k` THEN
        UNDISCH_TAC `(phi:real^3->real^N) y IN k` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^3->real^N) x = phi y` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `(f:real^N->real^N) x = f y`)) (concl th) &&
          is_forall (concl th))) THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(MP_TAC o AP_TERM `psi:real^N->real^3`) THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `kd = IMAGE (psi:real^N->real^3) (IMAGE (g:real^N->real^N) s)` THEN
  SUBGOAL_THEN `compact (kd:real^3->bool) /\ ~(kd = {}) /\ kd SUBSET ball(vec 0,&2) /\
                IMAGE (G:real^3->real^3) kd = IMAGE (h:real^N->real^3) s`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (g:real^N->real^N) s SUBSET relative_interior k` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) SUBSET IMAGE (f:real^N->real^N) (relative_interior k)` THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `!x. x IN k ==> (g:real^N->real^N)(f x) = x` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET IMAGE (f:real^N->real^N) k` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) SUBSET IMAGE (f:real^N->real^N) (relative_interior k)` THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "kd" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
         [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
          ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; MOI_S4K_FT_FACTS; lf_simplicial_complex]]];
      EXPAND_TAC "kd" THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      EXPAND_TAC "kd" THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (psi:real^N->real^3) (relative_interior k)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`psi:real^N->real^3`; `k:real^N->bool`; `cball(vec 0:real^3,&2)`]
        CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[SUBSET_REFL; AFF_DIM_CBALL; DIMINDEX_3;
                      RELATIVE_INTERIOR_CBALL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[INT_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      EXPAND_TAC "kd" THEN EXPAND_TAC "G" THEN REWRITE_TAC[IMAGE_o] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
        DISCH_THEN(X_CHOOSE_THEN `u:real^N` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
        SUBGOAL_THEN `(g:real^N->real^N) x IN k /\ x IN IMAGE (f:real^N->real^N) k`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `IMAGE (g:real^N->real^N) s SUBSET relative_interior k` THEN
          MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
          UNDISCH_TAC `(s:real^N->bool) SUBSET IMAGE (f:real^N->real^N) k` THEN
          UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
          ALL_TAC] THEN
        ASM_SIMP_TAC[];
        DISCH_TAC THEN
        SUBGOAL_THEN `(g:real^N->real^N) z IN k /\ z IN IMAGE (f:real^N->real^N) k`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `IMAGE (g:real^N->real^N) s SUBSET relative_interior k` THEN
          MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
          UNDISCH_TAC `(s:real^N->bool) SUBSET IMAGE (f:real^N->real^N) k` THEN
          UNDISCH_TAC `(z:real^N) IN s` THEN SET_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `(g:real^N->real^N) z` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `(psi:real^N->real^3) ((g:real^N->real^N) z)` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `(g:real^N->real^N) z` THEN REWRITE_TAC[] THEN
        EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^3. norm y`; `kd:real^3->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `norm(y0:real^3) < &2` ASSUME_TAC THENL
   [UNDISCH_TAC `(kd:real^3->bool) SUBSET ball(vec 0,&2)` THEN
    UNDISCH_TAC `(y0:real^3) IN kd` THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `rho = (norm(y0:real^3) + &2) / &2` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < &2 /\ (kd:real^3->bool) SUBSET ball(vec 0,rho)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `y0:real^3` NORM_POS_LE) THEN EXPAND_TAC "rho" THEN
    REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `rho:real`] MOI_S4C_BALL_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "m305" (MP_TAC o SPECL [`IMAGE (G:real^3->real^3) (cball(vec 0,rho))`;
                                  `IMAGE (G:real^3->real^3) (cball(vec 0,&2))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (G:real^3->real^3) kd = IMAGE (h:real^N->real^3) s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (G:real^3->real^3) (cball(vec 0,rho))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `rho:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (G:real^3->real^3) (cball(vec 0,&2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interior(IMAGE (G:real^3->real^3) (cball(vec 0,&2)))` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      ASM_REWRITE_TAC[]]]);;

