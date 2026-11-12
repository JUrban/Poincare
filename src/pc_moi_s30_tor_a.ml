(* ========================================================================= *)
(* pc_moi_s30_tor_a: the torus region and an essential loop (Moise GTM 47,  *)
(* 30.7, printed p.217).  Main theorems TORUS_REGION and TORUS_LOOP (the    *)
(* statements MOI_S30_TORUS_REGION and MOI_S30_TORUS_LOOP of                *)
(* pc_moi_s3032_stmt).  TORUS_REGION follows by separation, the complement  *)
(* of a solid torus being connected; TORUS_LOOP from the winding numbers of *)
(* loops on S1 x S1 and the solid torus model of revolution.                *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s30_shell.ml";;   (* shell facts, HOMEO_INTERIOR_GEN, rho *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: the complement of a solid torus is connected (the solid          *)
(* torus is homotopy equivalent to its spine circle, a simple closed curve, *)
(* HOMOTOPY_EQUIVALENT_SEPARATION), and the theorem TORUS_REGION by         *)
(* separation: the connected unbounded set outside the interior of s2 lies  *)
(* in the outside of the surface, so the outside lies in the side of        *)
(* frontier s2, and s1 lies in the other side, inside the surface.  The     *)
(* antecedent MOISE_266 is not needed.                                       *)
(* ========================================================================= *)

let MOI_S3TA_SPINE_PATH = prove
 (`simple_path (\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t)) /\
   path_image (\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t)) =
   {vec 0:real^2} PCROSS sphere(vec 0:real^2,&1)`,
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t)) =
                  (\z:real^2. pastecart (vec 0:real^2) z) o circlepath(vec 0,&1)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[SIMPLE_PATH_CIRCLEPATH; REAL_OF_NUM_EQ; ARITH_EQ; PASTECART_INJ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      MESON_TAC[]];
    UNDISCH_TAC `path_image (circlepath(vec 0,&1)) = sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[path_image; EXTENSION; IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                IN_SING; PASTECART_INJ] THEN
    MESON_TAC[]]);;

let MOI_S3TA_SOLID_TORUS_COMPLEMENT = prove
 (`!s:real^3->bool.
     solid_torus s
     ==> connected ((:real^3) DIFF s) /\ connected ((:real^3) DIFF interior s) /\
         ~bounded ((:real^3) DIFF interior s)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S38_SOLID_TORUS_COMPACT) THEN
  MP_TAC(MATCH_MP MOI_S38_SOLID_TORUS_HOMEO (ASSUME `solid_torus (s:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_TAC `g:real^3->real^(2,2)finite_sum`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `{vec 0:real^2} PCROSS sphere(vec 0:real^2,&1) SUBSET
                cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SING_SUBSET; CENTRE_IN_CBALL; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^3) DIFF s)` ASSUME_TAC THENL
   [ABBREV_TAC `c = (f:real^(2,2)finite_sum->real^3) o
                    (\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t))` THEN
    SUBGOAL_THEN
     `simple_path (c:real^1->real^3) /\
      path_image c = IMAGE (f:real^(2,2)finite_sum->real^3)
                       ({vec 0:real^2} PCROSS sphere(vec 0:real^2,&1))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[PATH_IMAGE_COMPOSE; MOI_S3TA_SPINE_PATH] THEN
      MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S3TA_SPINE_PATH] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`a:real^(2,2)finite_sum`; `b:real^(2,2)finite_sum`] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(a:real^(2,2)finite_sum) IN
                      cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
                      (b:real^(2,2)finite_sum) IN
                      cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
        STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `path_image (c:real^1->real^3)`]
                  HOMOTOPY_EQUIVALENT_SEPARATION) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_SIMPLE_PATH_IMAGE] THEN
      MATCH_MP_TAC(ISPECL [`s:real^3->bool`;
                           `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                           `IMAGE (f:real^(2,2)finite_sum->real^3)
                              ({vec 0:real^2} PCROSS sphere(vec 0:real^2,&1))`]
                          HOMOTOPY_EQUIVALENT_TRANS) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
        ASM_MESON_TAC[solid_torus];
        ALL_TAC] THEN
      MATCH_MP_TAC(ISPECL [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                           `{vec 0:real^2} PCROSS sphere(vec 0:real^2,&1)`;
                           `IMAGE (f:real^(2,2)finite_sum->real^3)
                              ({vec 0:real^2} PCROSS sphere(vec 0:real^2,&1))`]
                          HOMOTOPY_EQUIVALENT_TRANS) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HOMOTOPY_EQUIVALENT_PCROSS THEN
        REWRITE_TAC[HOMOTOPY_EQUIVALENT_REFL] THEN
        MATCH_MP_TAC HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS THEN
        SIMP_TAC[CONVEX_IMP_CONTRACTIBLE; CONVEX_CBALL; CONTRACTIBLE_SING; NOT_INSERT_EMPTY;
                 CBALL_EQ_EMPTY] THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
        REWRITE_TAC[homeomorphic] THEN
        MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^3`;
                              `g:real^3->real^(2,2)finite_sum`] THEN
        MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
        MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                              `s:real^3->bool`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE THEN
      ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN MATCH_MP_TAC CONNECTED_CLOSURE THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN MP_TAC(INST_TYPE [`:3`,`:N`] NOT_BOUNDED_UNIV) THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(:real^3) = ((:real^3) DIFF interior s) UNION s` SUBST1_TAC THENL
     [MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED]]]);;

(* The theorem TORUS_REGION. *)

let TORUS_REGION = prove
 (MOI_S30_TORUS_REGION,
  DISCH_THEN(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`s1:real^3->bool`; `s2:real^3->bool`;
                       `m:(real^3->bool)->bool`] THEN
  REWRITE_TAC[euclidean_separates] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "shell")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
        STRIP_ASSUME_TAC))))))))))) THEN
  ABBREV_TAC `M = UNIONS (m:(real^3->bool)->bool)` THEN
  ABBREV_TAC `Y = closure((s2:real^3->bool) DIFF s1)` THEN
  USE_THEN "shell" (MP_TAC o MATCH_MP TOROIDAL_SHELL_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (s1:real^3->bool) /\ compact (s2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S38_SOLID_TORUS_COMPACT]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S3TA_SOLID_TORUS_COMPLEMENT
          (ASSUME `solid_torus (s2:real^3->bool)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected (s1:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `solid_torus (s1:real^3->bool)` THEN REWRITE_TAC[solid_torus] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_CONNECTEDNESS) THEN
    SIMP_TAC[CONNECTED_PCROSS; CONNECTED_CBALL; CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
    ALL_TAC] THEN
  (* the surface lies in the interior of s2 and misses s1 *)
  SUBGOAL_THEN `(Y:real^3->bool) SUBSET s2` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^3->bool) SUBSET interior s2` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior(Y:real^3->bool)` THEN
    ASM_SIMP_TAC[SUBSET_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded (M:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `s2:real^3->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    MP_TAC(ISPEC `s2:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(M:real^3->bool) SUBSET interior s2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^3->bool) INTER s1 SUBSET frontier s1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Y:real^3->bool) SUBSET (:real^3) DIFF interior s1` MP_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
      REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^3->bool) INTER s1 = {}` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(M:real^3->bool) SUBSET interior Y`;
      `interior (Y:real^3->bool) = Y DIFF (frontier s1 UNION frontier s2)`;
      `(Y:real^3->bool) INTER s1 SUBSET frontier s1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* s1 lies on the side u *)
  SUBGOAL_THEN `(s1:real^3->bool) SUBSET u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s1:real^3->bool`; `u:real^3->bool`; `v:real^3->bool`]
                  MOI_P35_CONNECTED_IN_ONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN SET_TAC[];
        MAP_EVERY UNDISCH_TAC [`(u:real^3->bool) UNION v = (:real^3) DIFF M`;
                               `(M:real^3->bool) INTER s1 = {}`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s1:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(frontier (s1:real^3->bool) = {})`; `frontier (s1:real^3->bool) SUBSET u`;
      `(s1:real^3->bool) SUBSET v`; `DISJOINT (u:real^3->bool) v`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the outside of the surface contains the complement of the interior of s2 *)
  SUBGOAL_THEN `(:real^3) DIFF interior s2 SUBSET outside M` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; OUTSIDE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~bounded ((:real^3) DIFF interior s2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `connected_component ((:real^3) DIFF M) x` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(M:real^3->bool) SUBSET interior s2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `outside(M:real^3->bool) SUBSET v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`outside(M:real^3->bool)`; `u:real^3->bool`; `v:real^3->bool`]
                  MOI_P35_CONNECTED_IN_ONE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CONNECTED_OUTSIDE; DIMINDEX_3; ARITH] THEN CONJ_TAC THENL
       [UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN SET_TAC[];
        MP_TAC(ISPEC `M:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
        UNDISCH_TAC `(u:real^3->bool) UNION v = (:real^3) DIFF M` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `frontier (s2:real^3->bool) SUBSET (:real^3) DIFF interior s2`
    MP_TAC THENL [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(frontier (s2:real^3->bool) = {})`; `frontier (s2:real^3->bool) SUBSET v`;
      `outside (M:real^3->bool) SUBSET u`; `DISJOINT (u:real^3->bool) v`;
      `(:real^3) DIFF interior s2 SUBSET outside M`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INSIDE_OUTSIDE] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(s1:real^3->bool) SUBSET u`; `(u:real^3->bool) UNION v = (:real^3) DIFF M`;
      `outside(M:real^3->bool) SUBSET v`; `DISJOINT (u:real^3->bool) v`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(:real^3) DIFF interior s2 SUBSET outside M`;
      `(M:real^3->bool) SUBSET interior s2`] THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Part 2: the solid torus of revolution in real^(2,1)finite_sum, the       *)
(* model of pc_moi_s30_shell without the hole: moi_s3ta_sol puts            *)
(* (z,u) of disk x circle at the point of distance |z| from the core circle *)
(* of radius 4 (moi_s3sh_rho), so cball x S1 is homeomorphic to            *)
(* {rho <= 1} with interior {rho < 1}, the image of ball x S1; with         *)
(* MOI_S3SH_HOMEO_INTERIOR_GEN the interior of any solid torus in real^3 is *)
(* the image of ball x S1.                                                   *)
(* ========================================================================= *)

let moi_s3ta_sol = new_definition
 `moi_s3ta_sol (x:real^(2,2)finite_sum) =
    pastecart ((&4 + fstcart x$1) % sndcart x) (lift(fstcart x$2)):real^(2,1)finite_sum`;;

let MOI_S3TA_SOL_RHO = prove
 (`!(z:real^2) (u:real^2).
     norm u = &1 /\ norm z < &4
     ==> moi_s3sh_rho (moi_s3ta_sol (pastecart z u)) = norm z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^2`; `1`] COMPONENT_LE_NORM) THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s3sh_rho; moi_s3ta_sol; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
              NORM_MUL] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN `abs(&4 + (z:real^2)$1) = &4 + z$1` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S3TA_SOL_INJ = prove
 (`!(z:real^2) (u:real^2) (z':real^2) (u':real^2).
     norm u = &1 /\ norm z < &4 /\ norm u' = &1 /\ norm z' < &4 /\
     moi_s3ta_sol (pastecart z u) = moi_s3ta_sol (pastecart z' u')
     ==> z = z' /\ u = u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`z':real^2`; `1`] COMPONENT_LE_NORM) THEN
  REPEAT DISCH_TAC THEN
  UNDISCH_TAC `moi_s3ta_sol (pastecart z u) = moi_s3ta_sol (pastecart z' u')` THEN
  REWRITE_TAC[moi_s3ta_sol; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ;
              LIFT_EQ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^2)$1 = (z':real^2)$1` ASSUME_TAC THENL
   [UNDISCH_TAC `(&4 + (z:real^2)$1) % (u:real^2) = (&4 + (z':real^2)$1) % (u':real^2)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^2->real`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) = z'` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2]; ALL_TAC] THEN
  UNDISCH_TAC `(&4 + (z':real^2)$1) % (u:real^2) = (&4 + (z':real^2)$1) % (u':real^2)` THEN
  REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC);;

let MOI_S3TA_SOL_SURJ = prove
 (`!w. moi_s3sh_rho w < &4
       ==> ?z u. norm(u:real^2) = &1 /\ norm(z:real^2) = moi_s3sh_rho w /\
                 moi_s3ta_sol (pastecart z u) = w`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `r = norm(fstcart(w:real^(2,1)finite_sum))` THEN
  ABBREV_TAC `z = vector[r - &4; drop(sndcart(w:real^(2,1)finite_sum))]:real^2` THEN
  SUBGOAL_THEN `norm(z:real^2) = moi_s3sh_rho w` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z"; "r"] THEN REWRITE_TAC[moi_s3sh_rho]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 = r - &4 /\ z$2 = drop(sndcart(w:real^(2,1)finite_sum))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "z" THEN REWRITE_TAC[VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`z:real^2`; `1`] COMPONENT_LE_NORM) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`z:real^2`; `inv r % fstcart(w:real^(2,1)finite_sum)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3ta_sol; FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&4 + (r - &4) = r`; LIFT_DROP] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
               PASTECART_FST_SND]);;

let MOI_S3TA_SOL_DIST = prove
 (`!(z:real^2) (z':real^2) (u:real^2).
     norm u = &1
     ==> norm(moi_s3ta_sol (pastecart z u) - moi_s3ta_sol (pastecart z' u)) <=
         &2 * norm(z - z')`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s3ta_sol; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_SUB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((&4 + (z:real^2)$1) % (u:real^2) - (&4 + (z':real^2)$1) % u) +
              norm(lift((z:real^2)$2) - lift((z':real^2)$2))` THEN
  REWRITE_TAC[NORM_PASTECART_LE] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; GSYM LIFT_SUB; NORM_MUL; NORM_LIFT] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_ARITH `(&4 + a) - (&4 + b) = a - b`] THEN
  MP_TAC(ISPECL [`z - z':real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`z - z':real^2`; `2`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_S3TA_SOL_CONTINUOUS = prove
 (`!s. moi_s3ta_sol continuous_on s`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `moi_s3ta_sol =
    (\x:real^(2,2)finite_sum.
       pastecart ((&4 + (fstcart x)$1) % sndcart x) (lift((fstcart x)$2)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s3ta_sol]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX];
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX]];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX]]);;

(* The image of a product of a set of radii with the circle. *)

let MOI_S3TA_SOL_IMAGE = prove
 (`!P. (!r. P r ==> r < &4)
       ==> IMAGE moi_s3ta_sol ({z:real^2 | P(norm z)} PCROSS sphere(vec 0:real^2,&1)) =
           {w | P(moi_s3sh_rho w)}`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SPHERE_0;
              IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^(2,1)finite_sum` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^2`; `u:real^2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `norm(z:real^2)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`z:real^2`; `u:real^2`] MOI_S3TA_SOL_RHO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `moi_s3sh_rho w`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `w:real^(2,1)finite_sum` MOI_S3TA_SOL_SURJ) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`z:real^2`; `u:real^2`] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3TA_SOL_IMAGES = prove
 (`IMAGE moi_s3ta_sol (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) =
   {w | moi_s3sh_rho w <= &1} /\
   IMAGE moi_s3ta_sol (ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) =
   {w | moi_s3sh_rho w < &1}`,
  CONJ_TAC THENL
   [SUBGOAL_THEN `cball(vec 0:real^2,&1) = {z | norm z <= &1}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_CBALL_0; IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPEC `\r. r <= &1` MOI_S3TA_SOL_IMAGE);
    SUBGOAL_THEN `ball(vec 0:real^2,&1) = {z | norm z < &1}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_BALL_0; IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPEC `\r. r < &1` MOI_S3TA_SOL_IMAGE)] THEN
  REWRITE_TAC[] THEN (ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC]));;

(* The interior of the model. *)

let MOI_S3TA_MODEL_INTERIOR = prove
 (`interior {w | moi_s3sh_rho w <= &1} = {w | moi_s3sh_rho w < &1}`,
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^(2,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s3sh_rho w <= &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `{w:real^(2,1)finite_sum | moi_s3sh_rho w <= &1}` INTERIOR_SUBSET) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `w:real^(2,1)finite_sum`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball"))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ ~(a = b) ==> a < b`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(SPEC `w:real^(2,1)finite_sum` MOI_S3TA_SOL_SURJ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC)) THEN
    ABBREV_TAC `d = min (e / &4) (&1 / &2)` THEN
    SUBGOAL_THEN `&0 < d /\ &2 * d < e /\ d <= &1 / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(z:real^2) = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_s3ta_sol (pastecart ((&1 + d) % z) u) IN
      {w:real^(2,1)finite_sum | moi_s3sh_rho w <= &1}`
    MP_TAC THENL
     [USE_THEN "ball" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(SPECL [`z:real^2`; `(&1 + d) % z:real^2`; `u:real^2`] MOI_S3TA_SOL_DIST) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `z - (&1 + d) % z:real^2 = --(d % z)`; NORM_NEG;
                      NORM_MUL; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPECL [`(&1 + d) % z:real^2`; `u:real^2`] MOI_S3TA_SOL_RHO) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`lift o moi_s3sh_rho`; `(:real^(2,1)finite_sum)`;
                   `interval(lift(--(&1)),lift(&1))`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[MOI_S3SH_RHO_CONTINUOUS; OPEN_UNIV; OPEN_INTERVAL; IN_UNIV;
                IN_INTERVAL_1; o_THM; LIFT_DROP] THEN
    MATCH_MP_TAC(MESON[] `(s:real^(2,1)finite_sum->bool) = t ==> open s ==> open t`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(2,1)finite_sum` THEN
    MP_TAC(ISPEC `vector[norm(fstcart(w:real^(2,1)finite_sum)) - &4;
                        drop(sndcart w)]:real^2` NORM_POS_LE) THEN
    REWRITE_TAC[GSYM moi_s3sh_rho] THEN REAL_ARITH_TAC]);;

(* The model homeomorphism and the interior of a solid torus in real^3. *)

let MOI_S3TA_SOL_MODEL = prove
 (`?psi. homeomorphism
           (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),
            {w | moi_s3sh_rho w <= &1})
           (moi_s3ta_sol,psi)`,
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  REWRITE_TAC[MOI_S3TA_SOL_CONTINUOUS; MOI_S3TA_SOL_IMAGES] THEN CONJ_TAC THENL
   [SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_CBALL_0; IN_SPHERE_0;
              PASTECART_INJ] THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `u:real^2`; `z':real^2`; `u':real^2`] THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_S3TA_SOL_INJ THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3TA_SOLID_TORUS_INTERIOR = prove
 (`!(x:real^3->bool) f g.
     homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g)
     ==> interior x = IMAGE f (ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `psi:real^(2,1)finite_sum->real^(2,2)finite_sum`
    (LABEL_TAC "mod") MOI_S3TA_SOL_MODEL THEN
  SUBGOAL_THEN
   `homeomorphism ({w | moi_s3sh_rho w <= &1},x)
                  ((f:real^(2,2)finite_sum->real^3) o psi,
                   moi_s3ta_sol o (g:real^3->real^(2,2)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{w | moi_s3sh_rho w <= &1}`; `x:real^3->bool`;
                 `(f:real^(2,2)finite_sum->real^3) o
                  (psi:real^(2,1)finite_sum->real^(2,2)finite_sum)`;
                 `moi_s3ta_sol o (g:real^3->real^(2,2)finite_sum)`]
                MOI_S3SH_HOMEO_INTERIOR_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; DIMINDEX_3] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MOI_S3TA_MODEL_INTERIOR; GSYM(CONJUNCT2 MOI_S3TA_SOL_IMAGES); IMAGE_o] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) SUBSET
    cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
  MP_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  USE_THEN "mod" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Part 3: loops in (convex s) x S1 are null-homotopic iff their            *)
(* circle factor has winding number 0 (the cball case is                    *)
(* SOLID_TORUS_MODEL_NULLHOMOTOPIC_WINDING of pc_moi_fnd_h1); with Part 2 a *)
(* loop in the interior of a solid torus is null-homotopic there iff its    *)
(* degree is 0.  The PL torus model is homeomorphic to S1 x S1, and a loop  *)
(* of S1 x S1 with a nonzero factor winding stays essential under a         *)
(* homeomorphism.                                                            *)
(* ========================================================================= *)

let MOI_S3TA_CONVEX_CIRCLE_LOOPS = prove
 (`!(s:real^2->bool) (p:real^1->real^(2,2)finite_sum).
     convex s /\ path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET s PCROSS sphere(vec 0:real^2,&1)
     ==> (homotopic_loops (s PCROSS sphere(vec 0:real^2,&1)) p
            (linepath(pathstart p,pathstart p)) <=>
          winding_number(sndcart o p,vec 0) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->real^(2,2)finite_sum`; `s:real^2->bool`;
                 `sphere(vec 0:real^2,&1)`] MOI_FH1_LOOP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `sndcart o (p:real^1->real^(2,2)finite_sum)` MOI_FH1_CIRCLE_NULLHOMOTOPIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[PATHSTART_COMPOSE] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_PROJ) THEN
    REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`fstcart o (p:real^1->real^(2,2)finite_sum)`; `s:real^2->bool`]
                MOI_FH1_CONVEX_NULLHOMOTOPIC) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `sphere(vec 0:real^2,&1)`;
                 `fstcart o (p:real^1->real^(2,2)finite_sum)`;
                 `sndcart o (p:real^1->real^(2,2)finite_sum)`;
                 `linepath(fstcart(pathstart p):real^2,
                           fstcart(pathstart(p:real^1->real^(2,2)finite_sum)))`;
                 `linepath(sndcart(pathstart p):real^2,
                           sndcart(pathstart(p:real^1->real^(2,2)finite_sum)))`]
                MOI_FH1_HOMOTOPIC_LOOPS_PASTECART) THEN
  ASM_REWRITE_TAC[o_THM; PASTECART_FST_SND; ETA_AX; LINEPATH_REFL]);;

let MOI_S3TA_INTERIOR_LOOPS = prove
 (`!(x:real^3->bool) f g p.
     homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
     path p /\ pathfinish p = pathstart p /\ path_image p SUBSET interior x
     ==> (homotopic_loops (interior x) p (linepath(pathstart p,pathstart p)) <=>
          winding_number(sndcart o g o p,vec 0) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `homeomorphism (ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),interior x)
                  ((f:real^(2,2)finite_sum->real^3),(g:real^3->real^(2,2)finite_sum))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S3TA_SOLID_TORUS_INTERIOR) THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                          `x:real^3->bool`] THEN
    SUBGOAL_THEN `ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) SUBSET
                  cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; BALL_SUBSET_CBALL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    EXPAND_TAC "x" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`; `interior x:real^3->bool`;
    `f:real^(2,2)finite_sum->real^3`; `g:real^3->real^(2,2)finite_sum`;
    `p:real^1->real^3`; `linepath(pathstart p:real^3,pathstart p)`]
   MOI_S38_HOMEO_HOMOTOPIC_LOOPS_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`;
                 `(g:real^3->real^(2,2)finite_sum) o (p:real^1->real^3)`]
                MOI_S3TA_CONVEX_CIRCLE_LOOPS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_BALL] THEN ASM_MESON_TAC[MOI_S38_HOMEO_LOOP]; ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* The PL torus model and the tori PL homeomorphic to it. *)

let MOI_S3TA_TORUS_MODEL_HOMEO = prove
 (`pl_torus_model homeomorphic
   sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`,
  REWRITE_TAC[pl_torus_model] THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vec 1:real^2,vec 1]) homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`interval[--vec 1:real^2,vec 1]`; `cball(vec 0:real^2,&1)`]
                  HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
    REWRITE_TAC[CONVEX_INTERVAL; BOUNDED_INTERVAL; CONVEX_CBALL; BOUNDED_CBALL;
                RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[AFF_DIM_CBALL; REAL_LT_01] THEN
    MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC HOMEOMORPHIC_PCROSS THEN ASM_REWRITE_TAC[]]);;

let MOI_S3TA_TORUS_PARAM = prove
 (`!(t:real^3->bool) (f:real^(2,2)finite_sum->real^3) g.
     pl_homeomorphism (pl_torus_model,t) (f,g)
     ==> ?ft gt. homeomorphism
                   (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),t) (ft,gt)`,
  REWRITE_TAC[pl_homeomorphism] THEN REPEAT STRIP_TAC THEN
  MP_TAC MOI_S3TA_TORUS_MODEL_HOMEO THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(2,2)finite_sum->real^(2,2)finite_sum`
    (X_CHOOSE_TAC `k:real^(2,2)finite_sum->real^(2,2)finite_sum`)) THEN
  MAP_EVERY EXISTS_TAC
   [`(f:real^(2,2)finite_sum->real^3) o (k:real^(2,2)finite_sum->real^(2,2)finite_sum)`;
    `(h:real^(2,2)finite_sum->real^(2,2)finite_sum) o (g:real^3->real^(2,2)finite_sum)`] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `pl_torus_model` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]);;

(* Loops with a nonzero factor winding stay essential in a homeomorphic image. *)

let MOI_S3TA_ESSENTIAL_IMAGE = prove
 (`!(t:real^3->bool) ft gt (c:real^1->real^(2,2)finite_sum).
     homeomorphism (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),t) (ft,gt) /\
     path c /\ pathfinish c = pathstart c /\
     path_image c SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     (~(winding_number(fstcart o c,vec 0) = Cx(&0)) \/
      ~(winding_number(sndcart o c,vec 0) = Cx(&0)))
     ==> ~homotopic_loops t (ft o c) (linepath(pathstart(ft o c),pathstart(ft o c)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hom")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  USE_THEN "hom" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(gt:real^3->real^(2,2)finite_sum) ((ft:real^(2,2)finite_sum->real^3) (pathstart c)) =
    pathstart c`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `c:real^1->real^(2,2)finite_sum` PATHSTART_IN_PATH_IMAGE) THEN
    UNDISCH_TAC `path_image (c:real^1->real^(2,2)finite_sum) SUBSET
                 sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
      ((gt:real^3->real^(2,2)finite_sum) o (ft:real^(2,2)finite_sum->real^3) o c)
      (linepath(pathstart c,pathstart c))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `linepath(pathstart c,pathstart c) =
      (gt:real^3->real^(2,2)finite_sum) o
      linepath(pathstart((ft:real^(2,2)finite_sum->real^3) o c),pathstart(ft o c))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL; PATHSTART_COMPOSE]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) c
      (linepath(pathstart c,pathstart c))`
  MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(gt:real^3->real^(2,2)finite_sum) o (ft:real^(2,2)finite_sum->real^3) o
                (c:real^1->real^(2,2)finite_sum)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `path_image (c:real^1->real^(2,2)finite_sum) SUBSET
                 sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[TORUS_MODEL_NULLHOMOTOPIC_WINDING] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Part 4: the theorem TORUS_LOOP.  For a map h of S1 x S1 into the         *)
(* punctured plane the winding numbers of h along the two generator loops    *)
(* e1, e2 are integers a, b; a combination of powers of e1 and e2 (with      *)
(* e2 reversed when a and b have the same sign) has h-winding 0 and a        *)
(* nonzero second factor winding (or e1 itself if a = 0).  For h the degree  *)
(* map of the solid torus restricted to the torus t, its image in t is the  *)
(* required loop (essential in t and null in interior s2 by Part 3).         *)
(* ========================================================================= *)

let MOI_S3TA_GEN1 = prove
 (`path (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))) /\
   pathfinish (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))) =
   pathstart (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))) /\
   pathstart (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))) =
   pastecart (Cx(&1)) (Cx(&1)) /\
   path_image (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))) SUBSET
   sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
   winding_number(fstcart o (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))),vec 0) =
   Cx(&1) /\
   winding_number(sndcart o (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))),vec 0) =
   Cx(&0)`,
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  SUBGOAL_THEN
   `fstcart o (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))) = circlepath(vec 0,&1) /\
    sndcart o (\t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))) = linepath(Cx(&1),Cx(&1))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LINEPATH_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `winding_number(linepath(Cx(&1),Cx(&1)),vec 0) = Cx(&0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN REWRITE_TAC[COMPLEX_VEC_0; CX_INJ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX; GSYM path] THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish];
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    UNDISCH_TAC `path_image (circlepath(vec 0,&1)) = sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

let MOI_S3TA_GEN2 = prove
 (`path (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)) /\
   pathfinish (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)) =
   pathstart (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)) /\
   pathstart (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)) =
   pastecart (Cx(&1)) (Cx(&1)) /\
   path_image (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)) SUBSET
   sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
   winding_number(fstcart o (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)),vec 0) =
   Cx(&0) /\
   winding_number(sndcart o (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)),vec 0) =
   Cx(&1)`,
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  SUBGOAL_THEN
   `fstcart o (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)) = linepath(Cx(&1),Cx(&1)) /\
    sndcart o (\t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)) = circlepath(vec 0,&1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LINEPATH_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `winding_number(linepath(Cx(&1),Cx(&1)),vec 0) = Cx(&0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN REWRITE_TAC[COMPLEX_VEC_0; CX_INJ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX; GSYM path] THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish];
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    UNDISCH_TAC `path_image (circlepath(vec 0,&1)) = sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

(* Winding numbers of h along joins of powers of two loops of S1 x S1. *)

let MOI_S3TA_WIND_COMBO = prove
 (`!(h:real^(2,2)finite_sum->real^2) (c:real^1->real^(2,2)finite_sum) d n m.
     h continuous_on (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) /\
     ~(vec 0 IN IMAGE h (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))) /\
     path c /\ pathfinish c = pathstart c /\
     path_image c SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     path d /\ pathfinish d = pathstart d /\
     path_image d SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     pathstart d = pathstart c
     ==> winding_number(h o (moi_s38_looppow c n ++ moi_s38_looppow d m),vec 0) =
         Cx(&n) * winding_number(h o c,vec 0) + Cx(&m) * winding_number(h o d,vec 0) /\
         winding_number(h o (moi_s38_looppow c n ++ reversepath(moi_s38_looppow d m)),
                        vec 0) =
         Cx(&n) * winding_number(h o c,vec 0) - Cx(&m) * winding_number(h o d,vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^1->real^(2,2)finite_sum`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  MP_TAC(ISPECL [`d:real^1->real^(2,2)finite_sum`; `m:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `h continuous_on path_image (c:real^1->real^(2,2)finite_sum) /\
    h continuous_on path_image (d:real^1->real^(2,2)finite_sum) /\
    h continuous_on path_image (moi_s38_looppow c n) /\
    h continuous_on path_image (moi_s38_looppow d m) /\
    ~((vec 0:real^2) IN IMAGE h (path_image c)) /\
    ~((vec 0:real^2) IN IMAGE h (path_image d)) /\
    ~((vec 0:real^2) IN IMAGE h (path_image (moi_s38_looppow c n))) /\
    ~((vec 0:real^2) IN IMAGE h (path_image (moi_s38_looppow d m)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[] THEN NO_TAC) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^(2,2)finite_sum->real^2`; `c:real^1->real^(2,2)finite_sum`;
                 `n:num`] MOI_S38_WINDING_LOOPPOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:real^(2,2)finite_sum->real^2`; `d:real^1->real^(2,2)finite_sum`;
                 `m:num`] MOI_S38_WINDING_LOOPPOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:real^(2,2)finite_sum->real^2`;
                 `moi_s38_looppow (d:real^1->real^(2,2)finite_sum) m`]
                MOI_S38_WINDING_REVERSEPATH_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `path (h o moi_s38_looppow (c:real^1->real^(2,2)finite_sum) n) /\
    path (h o moi_s38_looppow (d:real^1->real^(2,2)finite_sum) m) /\
    path (h o reversepath (moi_s38_looppow (d:real^1->real^(2,2)finite_sum) m)) /\
    ~((vec 0:real^2) IN path_image (h o moi_s38_looppow c n)) /\
    ~((vec 0:real^2) IN path_image (h o moi_s38_looppow d m)) /\
    ~((vec 0:real^2) IN path_image (h o reversepath (moi_s38_looppow d m))) /\
    pathfinish (h o moi_s38_looppow c n) = h(pathstart c) /\
    pathstart (h o moi_s38_looppow d m) = h(pathstart c) /\
    pathstart (h o reversepath (moi_s38_looppow d m)) = h(pathstart c)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_REVERSEPATH; PATHSTART_COMPOSE;
                    PATHFINISH_COMPOSE; PATHSTART_REVERSEPATH] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_COMPOSE_JOIN] THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_JOIN o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC COMPLEX_RING);;

(* A loop with h-winding 0 and a nonzero factor winding. *)

let MOI_S3TA_KERNEL_LOOP = prove
 (`!h:real^(2,2)finite_sum->real^2.
     h continuous_on (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) /\
     ~(vec 0 IN IMAGE h (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))
     ==> ?c. path c /\ pathfinish c = pathstart c /\
             path_image c SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
             (~(winding_number(fstcart o c,vec 0) = Cx(&0)) \/
              ~(winding_number(sndcart o c,vec 0) = Cx(&0))) /\
             winding_number(h o c,vec 0) = Cx(&0)`,
  GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_S3TA_GEN1 THEN STRIP_ASSUME_TAC MOI_S3TA_GEN2 THEN
  ABBREV_TAC `e1 = \t. pastecart (circlepath(vec 0,&1) t) (Cx(&1))` THEN
  ABBREV_TAC `e2 = \t. pastecart (Cx(&1)) (circlepath(vec 0,&1) t)` THEN
  (* the h-windings of the generators are integers *)
  SUBGOAL_THEN
   `!e. path e /\ pathfinish e = pathstart e /\
        path_image e SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
        ==> complex_integer(winding_number((h:real^(2,2)finite_sum->real^2) o e,vec 0))`
  (LABEL_TAC "int") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `~((vec 0:real^2) IN IMAGE (h:real^(2,2)finite_sum->real^2)
                     (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))` THEN
      UNDISCH_TAC `path_image (e:real^1->real^(2,2)finite_sum) SUBSET
                   sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `winding_number((h:real^(2,2)finite_sum->real^2) o e1,vec 0) = Cx(&0)` THENL
   [EXISTS_TAC `e1:real^1->real^(2,2)finite_sum` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_integer(winding_number((h:real^(2,2)finite_sum->real^2) o e1,vec 0)) /\
    complex_integer(winding_number((h:real^(2,2)finite_sum->real^2) o e2,vec 0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "int" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_FH1_COMPLEX_INTEGER_CASES (ASSUME
   `complex_integer(winding_number((h:real^(2,2)finite_sum->real^2) o e1,vec 0))`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  MP_TAC(MATCH_MP MOI_FH1_COMPLEX_INTEGER_CASES (ASSUME
   `complex_integer(winding_number((h:real^(2,2)finite_sum->real^2) o e2,vec 0))`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(winding_number((h:real^(2,2)finite_sum->real^2) o e1,vec 0) = Cx(&0))` THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
      can (find_term ((=) `e1:real^1->real^(2,2)finite_sum`)) (concl th) &&
      is_disj(concl th))) THEN
    REWRITE_TAC[COMPLEX_NEG_0];
    ALL_TAC] THEN
  (* the windings of the combinations *)
  MP_TAC(ISPECL [`h:real^(2,2)finite_sum->real^2`; `e1:real^1->real^(2,2)finite_sum`;
                 `e2:real^1->real^(2,2)finite_sum`; `n:num`; `m:num`] MOI_S3TA_WIND_COMBO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`sndcart:real^(2,2)finite_sum->real^2`; `e1:real^1->real^(2,2)finite_sum`;
                 `e2:real^1->real^(2,2)finite_sum`; `n:num`; `m:num`] MOI_S3TA_WIND_COMBO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN
    REWRITE_TAC[IN_IMAGE; MOI_FH1_IN_PCROSS] THEN MESON_TAC[];
    STRIP_TAC] THEN
  (* the path facts of the combinations *)
  MP_TAC(ISPECL [`e1:real^1->real^(2,2)finite_sum`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  MP_TAC(ISPECL [`e2:real^1->real^(2,2)finite_sum`; `m:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!d. path d /\ pathstart d = pastecart (Cx(&1)) (Cx(&1)) /\
        pathfinish d = pastecart (Cx(&1)) (Cx(&1)) /\
        path_image d SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
        ==> path (moi_s38_looppow (e1:real^1->real^(2,2)finite_sum) n ++ d) /\
            pathfinish (moi_s38_looppow e1 n ++ d) = pathstart (moi_s38_looppow e1 n ++ d) /\
            path_image (moi_s38_looppow e1 n ++ d) SUBSET
            sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
  (LABEL_TAC "join") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    can (find_term ((=) `e1:real^1->real^(2,2)finite_sum`)) (concl th) &&
    is_disj(concl th))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    can (find_term ((=) `e2:real^1->real^(2,2)finite_sum`)) (concl th) &&
    is_disj(concl th))) THENL
   [EXISTS_TAC `moi_s38_looppow (e1:real^1->real^(2,2)finite_sum) n ++
                reversepath(moi_s38_looppow (e2:real^1->real^(2,2)finite_sum) m)`;
    EXISTS_TAC `moi_s38_looppow (e1:real^1->real^(2,2)finite_sum) n ++
                moi_s38_looppow (e2:real^1->real^(2,2)finite_sum) m`;
    EXISTS_TAC `moi_s38_looppow (e1:real^1->real^(2,2)finite_sum) n ++
                moi_s38_looppow (e2:real^1->real^(2,2)finite_sum) m`;
    EXISTS_TAC `moi_s38_looppow (e1:real^1->real^(2,2)finite_sum) n ++
                reversepath(moi_s38_looppow (e2:real^1->real^(2,2)finite_sum) m)`] THEN
  USE_THEN "join" (MP_TAC o SPEC `moi_s38_looppow (e2:real^1->real^(2,2)finite_sum) m`) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]; STRIP_TAC]) THEN
  USE_THEN "join" (MP_TAC o
    SPEC `reversepath(moi_s38_looppow (e2:real^1->real^(2,2)finite_sum) m)`) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                     PATH_IMAGE_REVERSEPATH] THEN
     ASM_MESON_TAC[SUBSET_TRANS];
     STRIP_TAC]) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_MUL_RID; COMPLEX_ADD_LID; COMPLEX_SUB_LZERO;
                  COMPLEX_NEG_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN
  CONV_TAC COMPLEX_RING);;

(* The theorem TORUS_LOOP. *)

let TORUS_LOOP = prove
 (MOI_S30_TORUS_LOOP,
  MAP_EVERY X_GEN_TAC [`t:real^3->bool`; `s2:real^3->bool`;
                       `f:real^(2,2)finite_sum->real^3`;
                       `g:real^3->real^(2,2)finite_sum`] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S38_SOLID_TORUS_HOMEO (ASSUME `solid_torus (s2:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^(2,2)finite_sum` (LABEL_TAC "st"))) THEN
  MP_TAC(MATCH_MP MOI_S3TA_TORUS_PARAM
    (ASSUME `pl_homeomorphism (pl_torus_model,t)
               ((f:real^(2,2)finite_sum->real^3),(g:real^3->real^(2,2)finite_sum))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ft:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_THEN `gt:real^3->real^(2,2)finite_sum` (LABEL_TAC "tt"))) THEN
  USE_THEN "tt" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(t:real^3->bool) SUBSET s2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s2:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(t:real^3->bool) SUBSET interior s2` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the degree map of s2 on the torus *)
  SUBGOAL_THEN
   `(sndcart o (g2:real^3->real^(2,2)finite_sum) o (ft:real^(2,2)finite_sum->real^3))
      continuous_on (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) /\
    ~(vec 0 IN IMAGE (sndcart o g2 o ft)
                (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s2:real^3->bool`; `f2:real^(2,2)finite_sum->real^3`;
                   `g2:real^3->real^(2,2)finite_sum`] MOI_S38_SOLID_TORUS_COORD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s2:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(vec 0 IN IMAGE (sndcart o (g2:real^3->real^(2,2)finite_sum)) s2)` THEN
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `sndcart o (g2:real^3->real^(2,2)finite_sum) o
                (ft:real^(2,2)finite_sum->real^3)` MOI_S3TA_KERNEL_LOOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^1->real^(2,2)finite_sum`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  EXISTS_TAC `(ft:real^(2,2)finite_sum->real^3) o (c:real^1->real^(2,2)finite_sum)` THEN
  SUBGOAL_THEN
   `path ((ft:real^(2,2)finite_sum->real^3) o (c:real^1->real^(2,2)finite_sum)) /\
    pathfinish (ft o c) = pathstart (ft o c) /\ path_image (ft o c) SUBSET t`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3TA_ESSENTIAL_IMAGE THEN
    EXISTS_TAC `gt:real^3->real^(2,2)finite_sum` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s2:real^3->bool`; `f2:real^(2,2)finite_sum->real^3`;
                   `g2:real^3->real^(2,2)finite_sum`;
                   `(ft:real^(2,2)finite_sum->real^3) o (c:real^1->real^(2,2)finite_sum)`]
                  MOI_S3TA_INTERIOR_LOOPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `winding_number((sndcart o (g2:real^3->real^(2,2)finite_sum) o
                                 (ft:real^(2,2)finite_sum->real^3)) o
                                (c:real^1->real^(2,2)finite_sum),vec 0) = Cx(&0)` THEN
    REWRITE_TAC[o_ASSOC]]);;

