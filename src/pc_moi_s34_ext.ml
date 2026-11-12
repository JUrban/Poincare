(* ========================================================================= *)
(* pc_moi_s34_ext: main theorem EXT = MOI_S34_EXT (pc_moi_s34_stmt.ml): the  *)
(* cell assembly MOISE_CELL_ASSEMBLY_ON applied to the source cells          *)
(* (labels = cells, faces = inclusions) gives a PL embedding of |kk|         *)
(* within ep of h (Moise p.246).                                             *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The theorem EXT.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4E_GSPEC_ID = prove
 (`!s:(real^N->bool)->bool. {l | l IN s} = s`,
  SET_TAC[]);;

let EXT = prove
 (MOI_S34_EXT,
  REWRITE_TAC[MOISE_CELL_ASSEMBLY_ON_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "asm") THEN
  MAP_EVERY X_GEN_TAC
   [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
    `ep:real^N->real`; `b:(real^N->bool)->real^3->bool`] THEN
  REWRITE_TAC[moi_s34_src_ok; moi_s34_tgt_ok; moi_s34_tgt_cells;
              moi_s34_tgt_meets] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (LABEL_TAC "s1") (CONJUNCTS_THEN2 (LABEL_TAC "s2")
     (CONJUNCTS_THEN2 (LABEL_TAC "s3") (CONJUNCTS_THEN2 (LABEL_TAC "s4")
       (LABEL_TAC "s5")))))
   (CONJUNCTS_THEN2 (LABEL_TAC "t1") (CONJUNCTS_THEN2 (LABEL_TAC "t2")
     (CONJUNCTS_THEN2 (LABEL_TAC "t3") (LABEL_TAC "t4")))))) THEN
  REMOVE_THEN "asm" (MP_TAC o ISPECL
   [`moi_s34_scells (tt:(real^N->bool)->bool) kk`; `\l:real^N->bool. l`;
    `b:(real^N->bool)->real^3->bool`; `moi_s34_dim:(real^N->bool)->num`;
    `\l m:real^N->bool. m IN moi_s34_scells tt kk /\ m SUBSET l`]) THEN
  REWRITE_TAC[MOI_S4E_GSPEC_ID; GSYM CONJ_ASSOC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `l:real^N->bool` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[SUBSET_REFL];
      MAP_EVERY X_GEN_TAC [`l:real^N->bool`; `m:real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `m:real^N->bool = l` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "s2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `l:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "s1" (MP_TAC o SPEC `l:real^N->bool`) THEN ASM_SIMP_TAC[];
      USE_THEN "t1" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`l:real^N->bool`; `m:real^N->bool`] THEN
      STRIP_TAC THEN
      REMOVE_THEN "s3" (MP_TAC o SPECL [`l:real^N->bool`; `m:real^N->bool`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      SET_TAC[];
      MAP_EVERY X_GEN_TAC [`l:real^N->bool`; `m:real^N->bool`] THEN
      STRIP_TAC THEN
      REMOVE_THEN "t2" (MP_TAC o SPECL [`l:real^N->bool`; `m:real^N->bool`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      SET_TAC[];
      USE_THEN "s4" ACCEPT_TAC;
      USE_THEN "t3" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "img")))) THEN
  EXISTS_TAC `f:real^N->real^3` THEN
  SUBGOAL_THEN
   `UNIONS kk SUBSET UNIONS (moi_s34_scells (tt:(real^N->bool)->bool) kk)`
  ASSUME_TAC THENL
   [USE_THEN "s5" SUBST1_TAC THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `UNIONS (moi_s34_scells (tt:(real^N->bool)->bool) kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN
    UNDISCH_TAC `moi_s34_tube (tt:(real^N->bool)->bool) kk` THEN
    SIMP_TAC[moi_s34_tube; combinatorial_manifold_with_boundary];
    UNDISCH_TAC
     `UNIONS kk SUBSET UNIONS (moi_s34_scells (tt:(real^N->bool)->bool) kk)` THEN
    REMOVE_THEN "inj" MP_TAC THEN MESON_TAC[SUBSET];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?l. l IN moi_s34_scells (tt:(real^N->bool)->bool) kk /\ (x:real^N) IN l`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN UNIONS kk` THEN
      UNDISCH_TAC
       `UNIONS kk SUBSET UNIONS (moi_s34_scells (tt:(real^N->bool)->bool) kk)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "t4" MATCH_MP_TAC THEN EXISTS_TAC `l:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      USE_THEN "img" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME
        `(l:real^N->bool) IN moi_s34_scells (tt:(real^N->bool)->bool) kk`))]) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]]);;

