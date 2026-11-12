(* ========================================================================= *)
(* pc_moi_s34_shell: Moise Sec 34, Lemma 2 (GTM 47, p.240), the domain part *)
(* used by the frame:                                                        *)
(*   SHELL_FND : |- MOI_FND_SOLID_TORUS_TRIANGLE ==> MOI_S34_SHELL           *)
(* (MOI_S34_SHELL of pc_moi_s34_stmt.ml has the antecedent MOISE_308_       *)
(* STATEMENT, which this route does not use.)                               *)
(* Route: no toroidal shell and no collar.  The face                        *)
(* torus N_s is a solid torus with spine Bd s (the foundation).  Its circle *)
(* coordinate, moved to h(N_s), extends to an open set V of real^3 with     *)
(* values in the unit circle (the circle is an ANR).  w0 is the part of the *)
(* preimage of V in the open stars of the vertices of s, so h(w0) is open   *)
(* (invariance of domain on the vertex stars, MOI_S4K_STAR_IMAGE_OPEN_ON).  *)
(* For an embedding f1 of N_s into h(w0) the extension r is defined on      *)
(* f1(N_s); the loop around h(Bd s) winds once under r, so its degree in   *)
(* the solid torus f1(N_s) is +1 or -1 (the degree of r on the core times   *)
(* the degree of the loop is 1), and every loop of f1(N_s) is homotopic to *)
(* a power of it (the degree tools of pc_moi_s308).                         *)
(* The foundation MOI_FND_SOLID_TORUS_TRIANGLE is proved as                 *)
(* GRAPH_TUBE_TRIANGLE_SOLID_TORUS in pc_moi_fnd_tubec.ml and discharged in *)
(* pc_moi_s34_status.ml.                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s308.ml";;
needs "src/pc_moi_s34_frame.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A map from a solid torus to the unit circle that winds once              *)
(* along a loop forces that loop to have degree +1 or -1; hence the loop   *)
(* carries all loops of the solid torus.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4S_CIRCLEPATH_SPHERE = prove
 (`!t. circlepath(vec 0,&1) t IN sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[CIRCLEPATH] THEN
  REWRITE_TAC[IN_SPHERE_0; VECTOR_ADD_LID; COMPLEX_MUL_LID] THEN
  SUBGOAL_THEN `Cx(&2) * Cx pi * ii * Cx(drop t) = ii * Cx(&2 * pi * drop t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[NORM_CEXP_II]]);;

let MOI_S4S_MAP_DEGREE = prove
 (`!(x:real^N->bool) f g (r:real^N->real^2) c.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      r continuous_on x /\ IMAGE r x SUBSET sphere(vec 0:real^2,&1) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x /\
      winding_number(r o c,vec 0) = Cx(&1)
      ==> winding_number(sndcart o g o c,vec 0) = Cx(&1) \/
          winding_number(sndcart o g o c,vec 0) = --Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `vec 0:real^2`] MOI_S38_SPINE_LOOP) THEN
  REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = (f:real^(2,2)finite_sum->real^N) o
                  (\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `k:real^1->real^N`;
                 `c:real^1->real^N`] MOI_S38_LOOP_AS_POWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` (LABEL_TAC "pow")) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `k:real^1->real^N`;
                 `c:real^1->real^N`; `n:num`] MOI_S38_HOMOTOPIC_POWER_DEGREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RID] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(vec 0 IN IMAGE (r:real^N->real^2) x)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(vec 0:real^2) IN sphere(vec 0,&1)` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(r:real^N->real^2) continuous_on path_image (k:real^1->real^N) /\
    ~(vec 0 IN IMAGE r (path_image k)) /\
    r continuous_on path_image (moi_s38_looppow k n) /\
    ~(vec 0 IN IMAGE r (path_image (moi_s38_looppow k n)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `x:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]) THEN
    UNDISCH_TAC `~(vec 0 IN IMAGE (r:real^N->real^2) x)` THEN
    UNDISCH_TAC `path_image (k:real^1->real^N) SUBSET x` THEN
    UNDISCH_TAC `path_image (moi_s38_looppow (k:real^1->real^N) n) SUBSET
                 path_image k` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_integer(winding_number((r:real^N->real^2) o (k:real^1->real^N),vec 0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN
    ASM_SIMP_TAC[PATH_CONTINUOUS_IMAGE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                 PATH_IMAGE_COMPOSE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `winding_number((r:real^N->real^2) o (c:real^1->real^N),vec 0) =
    winding_number(r o moi_s38_looppow (k:real^1->real^N) n,vec 0) \/
    winding_number(r o c,vec 0) =
    winding_number(r o reversepath(moi_s38_looppow k n),vec 0)`
  MP_TAC THENL
   [SUBGOAL_THEN `IMAGE (r:real^N->real^2) x SUBSET (:complex) DELETE vec 0`
    ASSUME_TAC THENL
     [UNDISCH_TAC `~(vec 0 IN IMAGE (r:real^N->real^2) x)` THEN SET_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "pow" DISJ_CASES_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real^N->real^2`; `k:real^1->real^N`; `n:num`]
    MOI_S38_WINDING_LOOPPOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:real^N->real^2`; `moi_s38_looppow (k:real^1->real^N) n`]
    MOI_S38_WINDING_REVERSEPATH_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:real^N->real^2`; `k:real^1->real^N`; `n:num`]
    MOI_S38_WINDING_LOOPPOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`;
                `winding_number((r:real^N->real^2) o (k:real^1->real^N),vec 0)`]
    MOI_S38_UNIT_CASES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl) o
      check (can (find_term ((=) `Cx(&1)`)) o concl) o
      check (can (find_term (fun t -> t = `r:real^N->real^2`)) o concl)) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC(CONJUNCT1 th)) THEN
  UNDISCH_TAC
   `winding_number(sndcart o (g:real^N->real^(2,2)finite_sum) o (c:real^1->real^N),
                   vec 0) = Cx(&1) \/
    winding_number(sndcart o g o c,vec 0) = --Cx(&1)` THEN
  REWRITE_TAC[]);;

let MOI_S4S_CARRIED_BY_DEGREE = prove
 (`!(x:real^N->bool) f g (r:real^N->real^2) c j.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      r continuous_on x /\ IMAGE r x SUBSET sphere(vec 0:real^2,&1) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET j /\ j SUBSET x /\
      winding_number(r o c,vec 0) = Cx(&1)
      ==> loops_carried j x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image (c:real^1->real^N) SUBSET x` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `r:real^N->real^2`;
                 `c:real^1->real^N`] MOI_S4S_MAP_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[loops_carried] THEN X_GEN_TAC `gam:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`;
                 `gam:real^1->real^N`] MOI_S38_LOOP_AS_POWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` (LABEL_TAC "pow")) THEN
  MP_TAC(SPECL [`c:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "pow" DISJ_CASES_TAC THENL
   [EXISTS_TAC `moi_s38_looppow (c:real^1->real^N) n`;
    EXISTS_TAC `reversepath(moi_s38_looppow (c:real^1->real^N) n)`] THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  PATH_IMAGE_REVERSEPATH] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* The face torus is a solid torus with spine Bd s (from the                *)
(* foundation), it lies in the open stars of the vertices of s, and an      *)
(* open set V of real^3 around h(N_s) gives w0 with h(w0) open inside V.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4S_FT_SPINE = prove
 (mk_imp(MOI_FND_SOLID_TORUS_TRIANGLE,
   `!(tt:(real^N->bool)->bool) kk s.
      moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2)
      ==> spine (relative_frontier s) (moi_s34_ft tt kk s)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4K_FT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4K_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`;
                                `skeleton 1 (kk:(real^N->bool)->bool)`;
                                `s:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s34_ft; moi_s34_vb; MOI_S4K_SKEL_VERTEX] THEN SIMP_TAC[]);;

let MOI_S4S_FT_STARS = prove
 (`!(tt:(real^N->bool)->bool) kk s.
      moi_s34_tube tt kk
      ==> moi_s34_ft tt kk s SUBSET
          UNIONS {moi_sta_open_star tt v | v | v IN s /\ {v} IN kk} /\
          moi_s34_ft tt kk s SUBSET UNIONS tt`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4K_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_ft tt kk (s:real^N->bool) SUBSET
                UNIONS {moi_sta_open_star tt v | v | v IN s /\ {v} IN kk}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_ft; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `moi_sta_open_star tt (v:real^N)` THEN CONJ_TAC THENL
     [EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_s34_vb tt kk (v:real^N) SUBSET moi_sta_open_star tt v`
    MP_TAC THENL
     [REWRITE_TAC[moi_s34_vb] THEN MATCH_MP_TAC MOI_S5A_CELL_OPEN_STAR THEN
      ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX];
      UNDISCH_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS {moi_sta_open_star tt v | v | v IN s /\ {v:real^N} IN kk}` THEN
  ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[MOI_S4K_OPEN_STAR_FACTS]);;

let MOI_S4S_W0 = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) s v.
      moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
      open v /\ IMAGE h (moi_s34_ft tt kk s) SUBSET v
      ==> ?w0. w0 SUBSET UNIONS tt /\ moi_s34_ft tt kk s SUBSET w0 /\
               open (IMAGE h w0) /\ IMAGE h w0 SUBSET v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4K_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4S_FT_STARS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fst") (LABEL_TAC "ftt")) THEN
  UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
  REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^3`; `UNIONS tt:real^N->bool`; `v:real^3->bool`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "ueq"))) THEN
  SUBGOAL_THEN `!w:real^N. moi_sta_open_star tt w SUBSET UNIONS tt` (LABEL_TAC "ost")
  THENL [REWRITE_TAC[MOI_S4K_OPEN_STAR_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN UNIONS tt /\ x IN u ==> (h:real^N->real^3) x IN v`
  (LABEL_TAC "uv") THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN {x | x IN UNIONS tt /\ (h:real^N->real^3) x IN v}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN UNIONS tt /\ (h:real^N->real^3) x IN v ==> x IN u`
  (LABEL_TAC "vu") THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN {x | x IN UNIONS tt /\ (h:real^N->real^3) x IN v}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS {u INTER moi_sta_open_star tt w | w | w IN s /\ {w:real^N} IN kk}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_sta_open_star tt (w:real^N)` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS tt /\ (h:real^N->real^3) x IN v`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN moi_s34_ft tt kk s` THEN
        USE_THEN "ftt" MP_TAC THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (h:real^N->real^3) (moi_s34_ft tt kk s) SUBSET v` THEN
        UNDISCH_TAC `(x:real^N) IN moi_s34_ft tt kk s` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN u` ASSUME_TAC THENL
     [USE_THEN "vu" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "fst" MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `(u:real^N->bool) INTER moi_sta_open_star tt w` THEN CONJ_TAC THENL
     [EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE (h:real^N->real^3) (u INTER moi_sta_open_star tt w)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4K_STAR_IMAGE_OPEN_ON THEN
      EXISTS_TAC `skeleton 1 (kk:(real^N->bool)->bool)` THEN
      EXISTS_TAC `UNIONS tt:real^N->bool` THEN
      ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_sta_open_star tt (w:real^N)` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `(u:real^N->bool) INTER moi_sta_open_star tt w` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool`
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  USE_THEN "uv" MATCH_MP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN moi_sta_open_star tt w` THEN
  USE_THEN "ost" (MP_TAC o SPEC `w:real^N`) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem SHELL_FND.                                               *)
(* ------------------------------------------------------------------------- *)

let SHELL_FND = prove
 (mk_imp(MOI_FND_SOLID_TORUS_TRIANGLE,MOI_S34_SHELL),
  DISCH_THEN(LABEL_TAC "sp" o MATCH_MP MOI_S4S_FT_SPINE) THEN
  DISCH_THEN(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `s:real^N->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "sp" (MP_TAC o SPECL [`tt:(real^N->bool)->bool`;
                                    `kk:(real^N->bool)->bool`; `s:real^N->bool`]) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[spine] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^(2,2)finite_sum->real^N`
   (X_CHOOSE_THEN `gg:real^N->real^(2,2)finite_sum`
    (X_CHOOSE_THEN `p0:real^2`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "bd" o SYM)))))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4S_FT_STARS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[moi_s34_emb] o
    check (fun th -> concl th = `moi_s34_emb (h:real^N->real^3) (UNIONS tt)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hinj")) THEN
  ABBREV_TAC `nn = moi_s34_ft tt kk (s:real^N->bool)` THEN
  SUBGOAL_THEN `(p0:real^2) IN cball(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p0:real^2) IN ball(vec 0,&1)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (nn:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                   `nn:real^N->bool`] HOMEOMORPHIC_COMPACTNESS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`ff:real^(2,2)finite_sum->real^N`;
                            `gg:real^N->real^(2,2)finite_sum`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^3) continuous_on nn` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS tt:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nn:real^N->bool`; `h:real^N->real^3`;
                 `IMAGE (h:real^N->real^3) nn`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(nn:real^N->bool) SUBSET UNIONS tt` THEN
    UNDISCH_TAC `(x:real^N) IN nn` THEN UNDISCH_TAC `(y:real^N) IN nn` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `hinv:real^3->real^N`)] THEN
  MP_TAC(ISPECL [`ff:real^(2,2)finite_sum->real^N`; `gg:real^N->real^(2,2)finite_sum`;
                 `h:real^N->real^3`; `hinv:real^3->real^N`;
                 `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                 `nn:real^N->bool`; `IMAGE (h:real^N->real^3) nn`]
    HOMEOMORPHISM_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) nn`;
                 `(h:real^N->real^3) o (ff:real^(2,2)finite_sum->real^N)`;
                 `(gg:real^N->real^(2,2)finite_sum) o (hinv:real^3->real^N)`]
    MOI_S38_SOLID_TORUS_COORD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sndcart o (gg:real^N->real^(2,2)finite_sum) o (hinv:real^3->real^N)`;
                 `(:real^3)`; `IMAGE (h:real^N->real^3) nn`;
                 `sphere(vec 0:real^2,&1)`]
    ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ANR_SPHERE; SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` (X_CHOOSE_THEN `r:real^3->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "rext"))))))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `s:real^N->bool`; `v:real^3->bool`] MOI_S4S_W0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w0:real^N->bool` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  X_GEN_TAC `f1:real^N->real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nn:real^N->bool`; `f1:real^N->real^3`;
                 `IMAGE (f1:real^N->real^3) nn`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `finv:real^3->real^N`) THEN
  MP_TAC(ISPECL [`ff:real^(2,2)finite_sum->real^N`; `gg:real^N->real^(2,2)finite_sum`;
                 `f1:real^N->real^3`; `finv:real^3->real^N`;
                 `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                 `nn:real^N->bool`; `IMAGE (f1:real^N->real^3) nn`]
    HOMEOMORPHISM_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) nn`;
                 `(h:real^N->real^3) o (ff:real^(2,2)finite_sum->real^N)`;
                 `(gg:real^N->real^(2,2)finite_sum) o (hinv:real^3->real^N)`;
                 `p0:real^2`] MOI_S38_SPINE_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) nn SUBSET v` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (h:real^N->real^3) w0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4S_CARRIED_BY_DEGREE THEN
  MAP_EVERY EXISTS_TAC
   [`(f1:real^N->real^3) o (ff:real^(2,2)finite_sum->real^N)`;
    `(gg:real^N->real^(2,2)finite_sum) o (finv:real^3->real^N)`;
    `r:real^3->real^2`;
    `((h:real^N->real^3) o (ff:real^(2,2)finite_sum->real^N)) o
     (\t. pastecart (p0:real^2) (circlepath(vec 0,&1) t))`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `v:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (r:real^3->real^2) v` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((h:real^N->real^3) o (ff:real^(2,2)finite_sum->real^N))
                      ({p0:real^2} PCROSS sphere(vec 0:real^2,&1))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMAGE_o] THEN
    USE_THEN "bd" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior(IMAGE (f1:real^N->real^3) nn)` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(r:real^3->real^2) o ((h:real^N->real^3) o (ff:real^(2,2)finite_sum->real^N)) o
    (\t. pastecart (p0:real^2) (circlepath(vec 0,&1) t)) =
    sndcart o ((gg:real^N->real^(2,2)finite_sum) o (hinv:real^3->real^N)) o
    ((h:real^N->real^3) o ff) o (\t. pastecart p0 (circlepath(vec 0,&1) t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `t:real^1` THEN
    SUBGOAL_THEN
     `(h:real^N->real^3) ((ff:real^(2,2)finite_sum->real^N)
        (pastecart (p0:real^2) (circlepath(vec 0,&1) t))) IN IMAGE h nn`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN
      SUBGOAL_THEN `IMAGE (ff:real^(2,2)finite_sum->real^N)
                      (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) = nn /\
                    pastecart (p0:real^2) (circlepath(vec 0,&1) t) IN
                      cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
      MP_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),
                                      nn:real^N->bool)
                         (ff:real^(2,2)finite_sum->real^N,gg)` THEN
          SIMP_TAC[homeomorphism];
          ASM_REWRITE_TAC[PASTECART_IN_PCROSS; MOI_S4S_CIRCLEPATH_SPHERE]];
        SET_TAC[]];
      DISCH_THEN(fun th -> USE_THEN "rext" (MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[o_THM]];
    FIRST_ASSUM ACCEPT_TAC]);;

