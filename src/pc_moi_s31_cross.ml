(* ========================================================================= *)
(* pc_moi_s31_cross: Moise GTM 47, p.221, the crossing condition for solid  *)
(* torus boundaries.  Main theorem RECROSS = MOI_S31_RECROSS                *)
(* (pc_moi_s3032_stmt.ml).  Route: a small ambient PL homeomorphism from    *)
(* MOI_FND_GP_SURFACES_3 (w = UNIV) moves the frontier torus of s to cross  *)
(* the union of the tori of the family; it keeps a in the interior and the  *)
(* solid torus in w; the crossing is localized to each torus and swapped    *)
(* for the reverse order.                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_ptri.ml";;
needs "src/pc_moi_s34_frame.ml";;
needs "src/pc_moi_s34_fball.ml";;
needs "src/pc_moi_s34_op2a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: generic lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

(* A crossing chart with the first two coordinates exchanged. *)

let MOI_S3RC_CROSS_SWAP = prove
 (`!s t (x:real^3). pl_crossing_at s t x ==> pl_crossing_at t s x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `sw = \y:real^3. vector[y$2; y$1; y$3]:real^3` THEN
  SUBGOAL_THEN `!y:real^3. (sw:real^3->real^3) y$1 = y$2 /\ sw y$2 = y$1 /\ sw y$3 = y$3`
  ASSUME_TAC THENL
   [EXPAND_TAC "sw" THEN REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. (sw:real^3->real^3) (sw y) = y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3]; ALL_TAC] THEN
  SUBGOAL_THEN `linear (sw:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "sw" THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^3),(:real^3)) ((sw:real^3->real^3),sw)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4P_PLH_UNIV_INV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sw:real^3->real^3`; `sw:real^3->real^3`; `IMAGE (f:real^3->real^3) u`]
    MOI_S4P_PLH_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a:real^3->bool. IMAGE (sw:real^3->real^3) (a INTER {y:real^3 | y$2 = &0}) =
                                 IMAGE sw a INTER {y:real^3 | y$1 = &0} /\
                                 IMAGE (sw:real^3->real^3) (a INTER {y:real^3 | y$1 = &0}) =
                                 IMAGE sw a INTER {y:real^3 | y$2 = &0}`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3)$1 = &0` THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3)$2 = &0` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `(sw:real^3->real^3) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (sw:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "sw" THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT]]);;

(* A finite union of finite combinatorial n-manifolds with pairwise disjoint *)
(* spaces is a finite combinatorial n-manifold (links are local).            *)

let MOI_S3RC_CM_UNIONS = prove
 (`!(ff:((real^N->bool)->bool)->bool) n.
     FINITE ff /\ (!m. m IN ff ==> FINITE m /\ combinatorial_manifold n m) /\
     (!m m'. m IN ff /\ m' IN ff /\ ~(m = m') ==> DISJOINT (UNIONS m) (UNIONS m'))
     ==> FINITE (UNIONS ff) /\ combinatorial_manifold n (UNIONS ff)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cm") (LABEL_TAC "dj"))) THEN
  SUBGOAL_THEN `FINITE (UNIONS ff:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex] THEN
  SUBGOAL_THEN
   `!m. m IN ff
        ==> (!s:real^N->bool. s IN m ==> ?n. n simplex s) /\
            (!f s. s IN m /\ f face_of s ==> f IN m) /\
            (!s s'. s IN m /\ s' IN m
                    ==> (s INTER s') face_of s /\ (s INTER s') face_of s') /\
            (!v. {v} IN m ==> pl_sphere (n - 1) (UNIONS (simplicial_link m v)))`
  (LABEL_TAC "mf") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "cm" (MP_TAC o C MP (ASSUME `(m:(real^N->bool)->bool) IN ff`) o
                   SPEC `m:(real^N->bool)->bool`) THEN
    REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* membership in a unique member *)
  SUBGOAL_THEN `!m m' (s:real^N->bool) s'.
                  m IN ff /\ m' IN ff /\ s IN m /\ s' IN m' /\ ~(s INTER s' = {})
                  ==> m = m'`
  (LABEL_TAC "un") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:(real^N->bool)->bool = m'` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "dj" (MP_TAC o SPECL [`m:(real^N->bool)->bool`; `m':(real^N->bool)->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(s:real^N->bool) IN m`; `(s':real^N->bool) IN m'`;
      `~((s:real^N->bool) INTER s' = {})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `m:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "un" (K ALL_TAC) THEN
    USE_THEN "mf" (MP_TAC o C MP (ASSUME `(m:(real^N->bool)->bool) IN ff`) o
                    SPEC `m:(real^N->bool)->bool`) THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "mf" (MP_TAC o C MP (ASSUME `(m:(real^N->bool)->bool) IN ff`) o
                    SPEC `m:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_UNIONS] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `m':(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `(s:real^N->bool) INTER s' = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_FACE_OF]; ALL_TAC] THEN
    SUBGOAL_THEN `m:(real^N->bool)->bool = m'` SUBST_ALL_TAC THENL
     [USE_THEN "un" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "mf" (MP_TAC o C MP (ASSUME `(m':(real^N->bool)->bool) IN ff`) o
                    SPEC `m':(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS ff:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `simplicial_link (UNIONS ff) (v:real^N) = simplicial_link m v`
    SUBST1_TAC THENL
     [REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM; IN_UNIONS] THEN
      X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m1:(real^N->bool)->bool` STRIP_ASSUME_TAC)
          (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
            (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m2:(real^N->bool)->bool` STRIP_ASSUME_TAC)
              STRIP_ASSUME_TAC)))) THEN
        SUBGOAL_THEN `m2:(real^N->bool)->bool = m` SUBST_ALL_TAC THENL
         [USE_THEN "un" MATCH_MP_TAC THEN
          MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `{v:real^N}`] THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^N) IN t` THEN SET_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [USE_THEN "mf" (MP_TAC o C MP (ASSUME `(m:(real^N->bool)->bool) IN ff`) o
                    SPEC `m:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
          EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]];
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]];
      REMOVE_THEN "un" (K ALL_TAC) THEN
      USE_THEN "mf" (MP_TAC o C MP (ASSUME `(m:(real^N->bool)->bool) IN ff`) o
                    SPEC `m:(real^N->bool)->bool`) THEN ASM_SIMP_TAC[]]]);;

(* PL solid tori are polyhedra, and PL homeomorphisms of real^3 preserve them. *)

let MOI_S3RC_SOLID_TORUS_POLYHEDRON = prove
 (`!s:real^N->bool. pl_solid_torus s ==> pl_polyhedron s`,
  GEN_TAC THEN REWRITE_TAC[pl_solid_torus] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^N`
    (X_CHOOSE_THEN `g:real^N->real^(2,1)finite_sum` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
  REWRITE_TAC[GSYM moi_fps_ann; GSYM moi_fps_m; MOI_FPS_M_PL_POLYHEDRON] THEN
  ASM_MESON_TAC[pl_homeomorphism; moi_fps_m; moi_fps_ann]);;

let MOI_S3RC_SOLID_TORUS_IMAGE = prove
 (`!(f:real^3->real^3) g s.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ pl_solid_torus s
     ==> pl_solid_torus (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4K_SOLID_TORUS_IMAGE THEN
  EXISTS_TAC `(:real^3)` THEN
  ASM_SIMP_TAC[MOI_S3RC_SOLID_TORUS_POLYHEDRON; SUBSET_UNIV] THEN
  UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),g)` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: RECROSS.  e1 keeps s inside w, e2 keeps a inside interior s;      *)
(* GP_SURFACES_3 with w = (:real^3) and e = min e1 e2 moves frontier s to    *)
(* cross the union of the tori of ff; the moved solid torus s' = IMAGE f s  *)
(* has frontier IMAGE f (frontier s); the crossing is localized to each     *)
(* torus (the others are closed and disjoint) and swapped.                   *)
(* ------------------------------------------------------------------------- *)

let RECROSS = prove
 (MOI_S31_RECROSS,
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gp") (CONJUNCTS_THEN2 (LABEL_TAC "bas")
    (CONJUNCTS_THEN2 (LABEL_TAC "tc") (LABEL_TAC "st")))) THEN
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `a:real^3->bool`; `w:real^3->bool`;
                       `ff:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  (* the margins *)
  SUBGOAL_THEN `compact (s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_STD_PL_SOLID_TORUS_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `w:real^3->bool`] MOI_S4Q_COMPACT_IN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `interior s:real^3->bool`] MOI_S4Q_COMPACT_IN_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  (* complexes of the tori *)
  SUBGOAL_THEN `!t:real^3->bool. (?s0. pl_solid_torus s0 /\ t = frontier s0)
                                 ==> ?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = t`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `s0:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "bas" (MP_TAC o C MP (ASSUME `pl_solid_torus (s0:real^3->bool)`) o
                    SPEC `s0:real^3->bool` o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `f0:real^(2,2)finite_sum->real^3`
      (X_CHOOSE_TAC `g0:real^3->real^(2,2)finite_sum`)) THEN
    USE_THEN "tc" (MP_TAC o
      C MP (ASSUME `pl_homeomorphism (pl_torus_model,frontier s0)
                      ((f0:real^(2,2)finite_sum->real^3),g0)`) o
      SPECL [`frontier s0:real^3->bool`;
             `f0:real^(2,2)finite_sum->real^3`; `g0:real^3->real^(2,2)finite_sum`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `frontier s:real^3->bool`) THEN
  ANTS_TAC THENL [EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?mt. !t:real^3->bool.
                  t IN ff ==> FINITE (mt t) /\ combinatorial_manifold 2 (mt t) /\
                              UNIONS (mt t) = t`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "combinatorial_manifold"))
          (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_solid_torus")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `MM = UNIONS (IMAGE (mt:(real^3->bool)->(real^3->bool)->bool) ff)` THEN
  SUBGOAL_THEN `FINITE (MM:(real^3->bool)->bool) /\ combinatorial_manifold 2 MM`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "MM" THEN MATCH_MP_TAC MOI_S3RC_CM_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `t':real^3->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `pairwise DISJOINT (ff:(real^3->bool)->bool)` THEN
    REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC
     `~((mt:(real^3->bool)->(real^3->bool)->bool) t' = mt t')` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (MM:(real^3->bool)->bool) = UNIONS ff` ASSUME_TAC THENL
   [EXPAND_TAC "MM" THEN REWRITE_TAC[UNIONS_IMAGE] THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `UNIONS ((mt:(real^3->bool)->(real^3->bool)->bool) t) = t` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(k:real^3->bool) IN (mt:(real^3->bool)->(real^3->bool)->bool) t` THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `UNIONS ((mt:(real^3->bool)->(real^3->bool)->bool) t) = t` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^3->bool. t IN ff ==> closed t` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^3->bool` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (concl th) &&
      not (can (find_term (fun t -> is_const t &&
                          fst(dest_const t) = "combinatorial_manifold")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[FRONTIER_CLOSED];
    ALL_TAC] THEN
  (* the general position move *)
  USE_THEN "gp" (MP_TAC o SPECL [`m0:(real^3->bool)->bool`; `MM:(real^3->bool)->bool`;
                                 `(:real^3)`; `min e1 e2:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM CLOSED_IN;
                    REAL_LT_MIN] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `(!x. (g:real^3->real^3) ((f:real^3->real^3) x) = x) /\ (!y. f (g y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),g)` THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^3->bool. interior (IMAGE (f:real^3->real^3) u) = IMAGE f (interior u) /\
                                 frontier (IMAGE f u) = IMAGE f (frontier u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`; `(:real^3)`;
                   `u:real^3->bool`] HOMEOMORPHISM_INTERIOR_OF) THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`; `(:real^3)`;
                   `u:real^3->bool`] HOMEOMORPHISM_FRONTIER_OF) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; SUBTOPOLOGY_UNIV; EUCLIDEAN_INTERIOR_OF;
                    EUCLIDEAN_FRONTIER_OF] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f:real^3->real^3) s` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3RC_SOLID_TORUS_IMAGE THEN EXISTS_TAC `g:real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `(g:real^3->real^3) y` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `e2:real`)) (concl th))) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^3->real^3) y` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `min e1 e2:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN SIMP_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `e1:real`)) (concl th) &&
      not (can (find_term (fun t -> t = `min e1 e2:real`)) (concl th)))) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `min e1 e2:real`)) (concl th))) THEN
    REWRITE_TAC[REAL_LT_MIN] THEN MESON_TAC[DIST_SYM];
    MAP_EVERY X_GEN_TAC [`t:real^3->bool`; `x:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pl_crossing_at (frontier (IMAGE (f:real^3->real^3) s)) t x` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (f:real^3->real^3) (UNIONS m0)`;
        `UNIONS MM:real^3->bool`; `(:real^3) DIFF UNIONS (ff DELETE (t:real^3->bool))`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
        UNDISCH_TAC `(x:real^3) IN frontier (IMAGE (f:real^3->real^3) s) INTER t` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(t:real^3->bool) IN ff` THEN SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
        MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
        REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_DELETE; NOT_EXISTS_THM] THEN
        X_GEN_TAC `t':real^3->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `pairwise DISJOINT (ff:(real^3->bool)->bool)` THEN
        REWRITE_TAC[pairwise] THEN
        DISCH_THEN(MP_TAC o SPECL [`t:real^3->bool`; `t':real^3->bool`]) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(x:real^3) IN frontier (IMAGE (f:real^3->real^3) s) INTER t` THEN
        UNDISCH_TAC `(x:real^3) IN t'` THEN UNDISCH_TAC `~(t':real^3->bool = t)` THEN
        SET_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        UNDISCH_TAC `~((y:real^3) IN UNIONS (ff DELETE (t:real^3->bool)))` THEN
        UNDISCH_TAC `(t:real^3->bool) IN ff` THEN SET_TAC[]];
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC MOI_S3RC_CROSS_SWAP THEN FIRST_ASSUM ACCEPT_TAC]]]);;

