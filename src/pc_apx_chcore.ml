(* ========================================================================= *)
(* pc_apx_chcore: the product chart of a one-sided infinite chain of        *)
(* eps-necks (the core of pc_apx_chchart, below the interface files, so     *)
(* that pc_apx_ncends can use it).  The engine of pc_apx_engine glues the   *)
(* necks of the initial segments one at a time (APX_CHAIN_STEP); here each  *)
(* step also exports that the new tube agrees with the old one below level  *)
(* L + 1/(8 eps) + 1 and that the length grows by at least 1/(2 eps).       *)
(* Dependent choice gives the sequence of tubes, the limit map is a         *)
(* parametrization of the region beyond the inner sphere of the first neck  *)
(* (APXC_PARAM_NESTED), and its image is the chain union (APXC_CHART_CORE). *)
(* ========================================================================= *)

needs "src/pc_apx_a21.ml";;

prioritize_real();;
type_invention_error := true;;

(* A map that is a parametrization on each set of an increasing sequence of *)
(* open sets is a parametrization of the union (local inverses agree by     *)
(* injectivity; continuity by the pasting lemma, smoothness by locality).    *)

let APXC_PARAM_NESTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (s:num->real^N->bool) (E:real^N->A).
     smooth_manifold_atlas top atlas /\
     (!m. s m SUBSET s(SUC m)) /\ (!m. mfd_param top atlas (s m) E)
     ==> mfd_param top atlas (UNIONS {s m | m IN (:num)}) E`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = UNIONS {(s:num->real^N->bool) m | m IN (:num)}` THEN
  SUBGOAL_THEN `!m n. m <= n ==> (s:num->real^N->bool) m SUBSET s n` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THENL
     [SIMP_TAC[LE; SUBSET_REFL];
      REWRITE_TAC[LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
      ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. (s:num->real^N->bool) m SUBSET S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?ei:num->A->real^N.
      !m. open (s m) /\ open_in top (IMAGE (E:real^N->A) (s m)) /\
          continuous_map (subtopology euclidean (s m),top) E /\
          continuous_map (subtopology top (IMAGE E (s m)),euclidean) (ei m) /\
          (!x. x IN s m ==> ei m (E x) = x) /\
          (!y. y IN IMAGE E (s m) ==> E(ei m y) = y) /\
          mfd_diffeo euclidean (open_set_atlas (:real^N)) (s m) top
                     (atlas:((A->bool)#(A->real^N))->bool)
                     (IMAGE E (s m)) E (ei m)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(s:num->real^N->bool) m`; `E:real^N->A`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN S /\ y IN S /\ (E:real^N->A) x = E y ==> x = y` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t1:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `m1:num` ASSUME_TAC) ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t2:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `m2:num` ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^N) IN s(MAX m1 m2) /\ (y:real^N) IN s(MAX m1 m2)` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`m1:num`; `MAX m1 m2`] (ASSUME
        `!m n. m <= n ==> (s:num->real^N->bool) m SUBSET s n`)) THEN
      MP_TAC(SPECL [`m2:num`; `MAX m1 m2`] (ASSUME
        `!m n. m <= n ==> (s:num->real^N->bool) m SUBSET s n`)) THEN
      REWRITE_TAC[ARITH_RULE `m1 <= MAX m1 m2 /\ m2 <= MAX m1 m2`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m p. p IN IMAGE (E:real^N->A) (s m)
                      ==> (ei:num->A->real^N) m p IN s m /\ E(ei m p) = p` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E' = \p:A. (ei:num->A->real^N) (@m. p IN IMAGE (E:real^N->A) (s m)) p` THEN
  SUBGOAL_THEN `!m p. p IN IMAGE (E:real^N->A) (s m) ==> (E':A->real^N) p = (ei:num->A->real^N) m p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "E'" THEN REWRITE_TAC[] THEN
    ABBREV_TAC `k = @m:num. (p:A) IN IMAGE (E:real^N->A) ((s:num->real^N->bool) m)` THEN
    SUBGOAL_THEN `(p:A) IN IMAGE (E:real^N->A) ((s:num->real^N->bool) k)` ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN CONV_TAC SELECT_CONV THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `S:real^N->bool`)) (concl th) &&
      is_imp(snd(strip_forall(concl th))))) THEN
    MP_TAC(MATCH_MP (SPECL [`k:num`; `p:A`] (ASSUME
      `!m p. p IN IMAGE (E:real^N->A) (s m)
             ==> (ei:num->A->real^N) m p IN s m /\ E(ei m p) = p`))
      (ASSUME `(p:A) IN IMAGE (E:real^N->A) ((s:num->real^N->bool) k)`)) THEN
    MP_TAC(MATCH_MP (SPECL [`m:num`; `p:A`] (ASSUME
      `!m p. p IN IMAGE (E:real^N->A) (s m)
             ==> (ei:num->A->real^N) m p IN s m /\ E(ei m p) = p`))
      (ASSUME `(p:A) IN IMAGE (E:real^N->A) ((s:num->real^N->bool) m)`)) THEN
    MP_TAC(SPEC `k:num` (ASSUME `!m. (s:num->real^N->bool) m SUBSET S`)) THEN
    MP_TAC(SPEC `m:num` (ASSUME `!m. (s:num->real^N->bool) m SUBSET S`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^N->A) S = UNIONS {IMAGE E (s m) | m IN (:num)}` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[UNIONS_GSPEC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (S:real^N->bool) /\ open_in top (IMAGE (E:real^N->A) S)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC OPEN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean S,top) (E:real^N->A) /\
    continuous_map (subtopology top (IMAGE E S),euclidean) (E':A->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(INST_TYPE [`:num`,`:K`] PASTING_LEMMA) THEN
      MAP_EVERY EXISTS_TAC [`(\m:num. E):num->real^N->A`; `s:num->real^N->bool`;
                            `(:num)`] THEN
      REWRITE_TAC[IN_UNIV; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [X_GEN_TAC `m:num` THEN
        MP_TAC(SPEC `m:num` (ASSUME `!m. (s:num->real^N->bool) m SUBSET S`)) THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `subtopology (subtopology euclidean S) ((s:num->real^N->bool) m) =
                      subtopology euclidean (s m)` SUBST1_TAC THENL
         [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
          UNDISCH_TAC `(s:num->real^N->bool) m SUBSET S` THEN SET_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `(s:num->real^N->bool) m` THEN
        ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
        UNDISCH_TAC `(s:num->real^N->bool) m SUBSET S` THEN SET_TAC[];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        UNDISCH_TAC `(x:real^N) IN S` THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
      MATCH_MP_TAC(INST_TYPE [`:num`,`:K`] PASTING_LEMMA) THEN
      MAP_EVERY EXISTS_TAC [`ei:num->A->real^N`; `\m. IMAGE (E:real^N->A) ((s:num->real^N->bool) m)`;
                            `(:num)`] THEN
      REWRITE_TAC[IN_UNIV; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `m:num` THEN
        SUBGOAL_THEN `IMAGE (E:real^N->A) ((s:num->real^N->bool) m) SUBSET IMAGE E S`
        ASSUME_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `subtopology (subtopology top (IMAGE (E:real^N->A) S))
                                  (IMAGE E ((s:num->real^N->bool) m)) =
                      subtopology top (IMAGE E (s m))` SUBST1_TAC THENL
         [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
          UNDISCH_TAC `IMAGE (E:real^N->A) ((s:num->real^N->bool) m) SUBSET IMAGE E S` THEN
          SET_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
        EXISTS_TAC `IMAGE (E:real^N->A) ((s:num->real^N->bool) m)` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (E:real^N->A) ((s:num->real^N->bool) m) SUBSET IMAGE E S` THEN
        SET_TAC[];
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `p:A`] THEN STRIP_TAC THEN
        MP_TAC(MATCH_MP (SPECL [`i:num`; `p:A`] (ASSUME
          `!m p. p IN IMAGE (E:real^N->A) (s m) ==> (E':A->real^N) p = (ei:num->A->real^N) m p`))
          (ASSUME `(p:A) IN IMAGE (E:real^N->A) ((s:num->real^N->bool) i)`)) THEN
        MP_TAC(MATCH_MP (SPECL [`j:num`; `p:A`] (ASSUME
          `!m p. p IN IMAGE (E:real^N->A) (s m) ==> (E':A->real^N) p = (ei:num->A->real^N) m p`))
          (ASSUME `(p:A) IN IMAGE (E:real^N->A) ((s:num->real^N->bool) j)`)) THEN
        MESON_TAC[];
        X_GEN_TAC `p:A` THEN STRIP_TAC THEN
        UNDISCH_TAC `(p:A) IN IMAGE (E:real^N->A) S` THEN
        ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
        DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SPECL [`m:num`; `p:A`] (ASSUME
          `!m p. p IN IMAGE (E:real^N->A) (s m) ==> (E':A->real^N) p = (ei:num->A->real^N) m p`)) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN S ==> (E':A->real^N)((E:real^N->A) x) = x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    SUBGOAL_THEN `(E:real^N->A) x IN IMAGE E ((s:num->real^N->bool) m)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(MATCH_MP (SPECL [`m:num`; `(E:real^N->A) x`] (ASSUME
      `!m p. p IN IMAGE (E:real^N->A) (s m) ==> (E':A->real^N) p = (ei:num->A->real^N) m p`))
      (ASSUME `(E:real^N->A) x IN IMAGE E ((s:num->real^N->bool) m)`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      SPEC `m:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_diffeo")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN IMAGE (E:real^N->A) S ==> (E':A->real^N) p IN S /\ E(E' p) = p`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean S,subtopology top (IMAGE (E:real^N->A) S)) E /\
    continuous_map (subtopology top (IMAGE E S),subtopology euclidean S) (E':A->real^N) /\
    open_in euclidean (S:real^N->bool) /\
    (!x. x IN topspace (subtopology euclidean S) ==> E'(E x) = x) /\
    (!y. y IN topspace (subtopology top (IMAGE E S)) ==> E(E' y) = y)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                    TOPSPACE_SUBTOPOLOGY; OPEN_IN_EUCLIDEAN; IN_INTER; SUBSET_REFL] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (open_set_atlas (:real^N)) (atlas:((A->bool)#(A->real^N))->bool) S E /\
    mfd_smooth_map atlas (open_set_atlas (:real^N)) (IMAGE (E:real^N->A) S) (E':A->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `top:A topology`] THEN
      ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      UNDISCH_TAC `(x:real^N) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
      EXISTS_TAC `(s:num->real^N->bool) m` THEN ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
      CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_diffeo")) (concl th))) THEN
      SIMP_TAC[mfd_diffeo];
      MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `euclidean:(real^N)topology`] THEN
      ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
      X_GEN_TAC `p:A` THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
      EXISTS_TAC `IMAGE (E:real^N->A) ((s:num->real^N->bool) m)` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `(ei:num->A->real^N) m`] THEN
      ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_diffeo")) (concl th))) THEN
      SIMP_TAC[mfd_diffeo]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> aconv (concl th)
    `IMAGE (E:real^N->A) S = UNIONS {IMAGE E ((s:num->real^N->bool) m) | m IN (:num)}`)) THEN
  REWRITE_TAC[mfd_param] THEN EXISTS_TAC `E':A->real^N` THEN
  ASM_REWRITE_TAC[mfd_diffeo; homeomorphic_maps]);;

(* ------------------------------------------------------------------------- *)
(* The engine step with agreement: APX_STEP_GLUE and APX_TUBE_STEP of       *)
(* pc_apx_engine (same proofs), also exporting that the new tube equals the *)
(* old one below the splice window (the glued map is E there).              *)
(* ------------------------------------------------------------------------- *)

let APXC_STEP_GLUE = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 e0 EM
    (g:real^3->real^3) g' a b d1.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e0 y) /\
        a = w1 + L + Delta - d0 - &2 /\ b = w2 + L + Delta + d0 + &2 /\
        d1 = sqrt(&2) * log(&3 / &2) /\
        mfd_param top atlas (apx_slab (a - d1) (b + d1)) EM /\ sphere_diffeo g g' /\
        (!y. y IN apx_slab (a - d1) (a + d1) ==> EM y = E y) /\
        (!y. y IN apx_slab (b - d1) (b + d1)
             ==> EM y = e'(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) /\
        (!y. y IN apx_slab (a - d1) (b + d1)
             ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (EM y) = apx_sval y) /\
        {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                  IMAGE e' (rfs_neck_dom eps) /\
             a <= apx_splice eps e' ei' Ei w1 w2 (L + Delta) p /\
             apx_splice eps e' ei' Ei w1 w2 (L + Delta) p <= b} =
        IMAGE EM {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}
        ==> ?E'. apx_eng_tube top atlas eps e0 e' E' (L + Delta) /\
                 (!y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps)
                      ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (E' y) =
                          apx_sval y) /\
                 IMAGE E' (apx_slab (--inv eps) ((L + Delta) + inv eps)) =
                 IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                 IMAGE e' (rfs_neck_dom eps) /\
                 (!y. apx_sval y < a ==> E' y = E y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th) THEN
              STRIP_ASSUME_TAC(MATCH_MP APX_STEP_DELTA_BIG th))
   STRIP_ASSUME_TAC) THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  SUBGOAL_THEN `&0 < d1 /\ d1 < &3 / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `a = w1 + L + Delta - d0 - &2`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `b = w2 + L + Delta + d0 + &2`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `d1 = sqrt(&2) * log(&3 / &2)`)) THEN
  SUBGOAL_THEN `mfd_param top atlas (apx_slab (--inv eps) (a + d1)) (E:real^3->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `apx_slab (--inv eps) (L + inv eps)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[apx_slab; OPEN_ANNULUS];
      MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param top atlas (apx_slab (b - d1) ((L + Delta) + inv eps))
      (\y. (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RADIAL_PARAM THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (b - d1) ((L + Delta) + inv eps)
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta)
              ((e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) =
            apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `g:real^3->real^3`;
                   `g':real^3->real^3`; `y:real^3`] APX_STEP_END_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (--inv eps) (a + d1)
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) ((E:real^3->A) y) = apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC APX_STEP_F_BOTTOM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `en:real^3->A`; `ein:A->real^3`; `d0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (a + d1)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta)`;
                 `E:real^3->A`; `EM:real^3->A`;
                 `\y. (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))`;
                 `--inv eps`; `a + d1`; `a - d1`; `b + d1`; `b - d1`;
                 `(L + Delta) + inv eps`; `a:real`; `b:real`] APX_GLUE3) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps)
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta)
              (if apx_sval y < a then (E:real^3->A) y
               else if apx_sval y <= b then EM y
               else (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) =
            apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ --inv eps < apx_sval y /\
                  apx_sval y < (L + Delta) + inv eps` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) ((L + Delta) + inv eps)` THEN
      SIMP_TAC[APX_SLAB_SVAL];
      ALL_TAC] THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < a + d1` THENL
     [SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (a + d1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
        (ASSUME `(y:real^3) IN apx_slab (--inv eps) (a + d1)`)]) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (--inv eps) (a + d1)`)) (concl th) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (concl th))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (--inv eps) (a + d1)`)) (concl th) &&
        not (can (find_term (fun t -> t = `EM:real^3->A`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < b + d1` THENL
     [SUBGOAL_THEN `(y:real^3) IN apx_slab (a - d1) (b + d1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
        (ASSUME `(y:real^3) IN apx_slab (a - d1) (b + d1)`)]) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (a - d1) (b + d1)`)) (concl th) &&
        is_cond (lhs(snd(dest_imp(snd(dest_forall(concl th)))))))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (a - d1) (b + d1)`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_splice")) (concl th) &&
        not (can (find_term (fun t -> t = `EM:real^3->A`)) (rhs(snd(dest_imp(snd(dest_forall(concl th))))))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (b - d1) ((L + Delta) + inv eps)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
      (ASSUME `(y:real^3) IN apx_slab (b - d1) ((L + Delta) + inv eps)`)]) o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab (b - d1) ((L + Delta) + inv eps)`)) (concl th) &&
      is_cond (lhs(snd(dest_imp(snd(dest_forall(concl th)))))))) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab (b - d1) ((L + Delta) + inv eps)`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_splice")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\y. if apx_sval y < a then (E:real^3->A) y
                  else if apx_sval y <= b then EM y
                  else (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))` THEN
  REWRITE_TAC[apx_eng_tube] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(E:real^3->A) y` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (--inv eps) (a + d1)`)) (concl th) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (concl th))) THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (inv(&8 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab (b - d1) ((L + Delta) + inv eps)`)) (concl th) &&
      can (find_term (fun t -> t = `EM:real^3->A`)) (concl th))) THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab ((L + Delta) - inv(&8 * eps)) ((L + Delta) + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  (* the image *)
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < a` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(EM:real^3->A) y IN
                    IMAGE EM {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
        is_eq (concl th) && is_comb(rhs(concl th)) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (rhs(concl th)) &&
        not (is_forall (concl th)))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                     `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                     `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                     `d0:real`; `w1:real`; `w2:real`; `g:real^3->real^3`;
                     `g':real^3->real^3`; `y:real^3`] APX_STEP_END_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN
  ASM_CASES_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) < a` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_LOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN
    SUBGOAL_THEN `(Ei:A->real^3) p = y` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `apx_sval(y:real^3) < a` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) < a` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) <= b` THENL
   [SUBGOAL_THEN `(p:A) IN
                  IMAGE EM {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`
    MP_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
        is_eq (concl th) && is_comb(rhs(concl th)) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (rhs(concl th)) &&
        not (is_forall (concl th)))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
    SUBGOAL_THEN `~(apx_sval(y:real^3) < a)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_HIGH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ei':A->real^3) p = v` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `v:real^3`] APX_RADIAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0) /\ abs(apx_sval v) < inv eps` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(radial_ext (g':real^3->real^3) v = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `exp((L + Delta) / sqrt(&2)) % radial_ext (g':real^3->real^3) v` THEN
  ASM_SIMP_TAC[APX_SVAL_EXP_SCALE; APX_SLAB_SVAL; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
  SUBGOAL_THEN `~((L + Delta) + apx_sval(v:real^3) < a) /\
                ~((L + Delta) + apx_sval(v:real^3) <= b) /\
                --inv eps < (L + Delta) + apx_sval v /\
                (L + Delta) + apx_sval v < (L + Delta) + inv eps`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) =
                 apx_sval((ei':A->real^3) p) + L + Delta` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) <= b)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APX_EXP_SCALE_COMPOSE] THEN
  REWRITE_TAC[REAL_ARITH `--(L + Delta) + L + Delta = &0`; real_div; REAL_MUL_LZERO;
              REAL_EXP_0; VECTOR_MUL_LID] THEN
  ASM_REWRITE_TAC[]);;

(* The inductive step: a step datum extends the tube by the next neck. *)


let APXC_TUBE_STEP = prove
 (`!u top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 e0 rho kappa Ds C.
        SMT_PRODUCT2_STATEMENT (u:A->bool) /\
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e0 y) /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE en (rfs_neck_dom eps)
             ==> !k. abs(sqrt(&2) * (ein(e' v) dot frechet_derivative (ein o e') (at v) k) /
                         (ein(e' v) dot ein(e' v)) -
                         rho * sqrt(&2) * (v dot k) / (v dot v))
                     <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        C * d0 < (w2 - w1) * min (rho - kappa) (&1)
        ==> ?E'. apx_eng_tube top atlas eps e0 e' E' (L + Delta) /\
                 (!y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps)
                      ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (E' y) =
                          apx_sval y) /\
                 IMAGE E' (apx_slab (--inv eps) ((L + Delta) + inv eps)) =
                 IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                 IMAGE e' (rfs_neck_dom eps) /\
                 (!y. apx_sval y < w1 + L + Delta - d0 - &2 ==> E' y = E y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `eps:real`; `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `rho:real`; `kappa:real`;
                 `Ds:real->real`; `C:real`; `w1 + L + Delta - d0 - &2`;
                 `w2 + L + Delta + d0 + &2`; `sqrt(&2) * log(&3 / &2)`]
                APX_STEP_PRODUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `EM:real^3->A` (X_CHOOSE_THEN `g:real^3->real^3`
    (X_CHOOSE_THEN `g':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `eps:real`; `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `e0:real^3->A`; `EM:real^3->A`;
                 `g:real^3->real^3`; `g':real^3->real^3`; `w1 + L + Delta - d0 - &2`;
                 `w2 + L + Delta + d0 + &2`; `sqrt(&2) * log(&3 / &2)`]
                APXC_STEP_GLUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;


(* The chain step of pc_apx_engine (same proof), also exporting the growth  *)
(* L' >= L + 1/(2 eps) and agreement of the new tube with the old one below *)
(* L + 1/(8 eps) + 1.                                                         *)

let APXC_CHAIN_STEP = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !u top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) Ds C m E L c.
           SMT_PRODUCT2_STATEMENT (u:A->bool) /\
           &0 < eps /\ eps <= eps1 /\ &96 * eps <= &1 /\ hausdorff_space top /\
           riemannian_metric atlas g /\
           apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e /\
           (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
           &0 < C /\ sqrt alpha1 <= &1 / &2560 /\ C * sqrt alpha1 <= &1 / &2560 /\
           m < n /\
           apx_eng_tube top atlas eps (e(&0)) (e(&m)) E L /\
           IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
           UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m} /\
           apx_eng_cmp top atlas eps E L e c m (&80 * sqrt alpha1 * inv eps)
           ==> ?E' L' c'. apx_eng_tube top atlas eps (e(&0)) (e(&(m + 1))) E' L' /\
                          IMAGE E' (apx_slab (--inv eps) (L' + inv eps)) =
                          UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m + 1} /\
                          apx_eng_cmp top atlas eps E' L' e c' (m + 1)
                                      (&80 * sqrt alpha1 * inv eps) /\
                          L + inv(&2 * eps) <= L' /\
                          (!y. apx_sval y < L + inv(&8 * eps) + &1 ==> E' y = E y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_PAIR_STRUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ps")] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_NO_TRIPLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "nt")] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1")
    (LABEL_TAC "c2"))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A)(&m))
                         ((e:int->real^3->A)(&m)) /\
                rfs_neck (top,atlas) g eps (x(&(m + 1))) (e(&(m + 1)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) ((e:int->real^3->A)(&m)) /\
                mfd_param top atlas (rfs_neck_dom eps) (e(&(m + 1)))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A)(&m)`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ein:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A)(&(m + 1))`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) (E:real^3->A)`
  ASSUME_TAC THENL [ASM_MESON_TAC[apx_eng_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `apx_slab (--inv eps) (L + inv eps)`; `E:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ei:A->real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "c1" (MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "ps" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(x:int->A)(&m)`; `(e:int->real^3->A)(&m)`;
    `(x:int->A)(&(m + 1))`; `(e:int->real^3->A)(&(m + 1))`; `ein:A->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `d0 = &80 * sqrt alpha1 * inv eps` THEN
  SUBGOAL_THEN `&0 < inv eps /\ &96 <= inv eps /\ &0 <= sqrt alpha1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `inv eps = &1 / eps` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d0 /\ &32 * d0 <= inv eps /\ d0 < inv(&2 * eps)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 <= sqrt alpha1 * inv eps /\
                  sqrt alpha1 * inv eps <= &1 / &2560 * inv eps`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:int->real^3->A)(&m)`; `(e:int->real^3->A)(&(m + 1))`; `ein:A->real^3`;
                 `eps:real`; `Delta:real`; `d0:real`] APX_PAIR_FORWARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `IMAGE ((e:int->real^3->A)(&m)) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
      IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (--inv(&2 * eps)))
      SUBSET IMAGE (e(&m)) (rfs_neck_dom eps) INTER IMAGE (e(&(m + 1))) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    DISCH_TAC] THEN
  USE_THEN "nt" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`; `m:num`;
    `E:real^3->A`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `(e:int->real^3->A)(&0)`; `(e:int->real^3->A)(&m)`; `E:real^3->A`;
                 `L:real`; `Ei:A->real^3`] APX_TUBE_EXACT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `w1 = max (inv(&8 * eps) - Delta) (--(&7 * inv(&8 * eps))) + d0 + &3` THEN
  ABBREV_TAC `w2 = min (inv eps - Delta) (--inv(&8 * eps)) - d0 - &3` THEN
  MP_TAC(SPECL [`eps:real`; `Delta:real`; `d0:real`; `w1:real`; `w2:real`]
               APX_WINDOW_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) /
                 mfd_scalar atlas g (x(&(m + 1)))`; `alpha1:real`] APX_RHO_KAPPA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_eng_tube top atlas eps ((e:int->real^3->A)(&0)) (e(&m)) E L` THEN
    REWRITE_TAC[apx_eng_tube] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab (--inv eps) (inv(&8 * eps))
                    ==> (E:real^3->A) y = (e:int->real^3->A)(&0) y` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_eng_tube top atlas eps ((e:int->real^3->A)(&0)) (e(&m)) E L` THEN
    REWRITE_TAC[apx_eng_tube] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps) SUBSET
                IMAGE E (apx_slab (--inv eps) (L + inv eps))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN
    DISCH_TAC THEN EXISTS_TAC `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `m:num` THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps) INTER
                IMAGE (e(&(m + 1))) (rfs_neck_dom eps) SUBSET
                IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (inv(&2 * eps)))` ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps) INTER
      IMAGE (e(&(m + 1))) (rfs_neck_dom eps)
      SUBSET IMAGE (e(&m)) (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
             IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (inv(&2 * eps)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C * d0 < (w2 - w1) *
             min (sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) /
                       mfd_scalar atlas g (x(&(m + 1)))) - &7 * sqrt alpha1) (&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_REG_CONST THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `sqrt alpha1`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_eng_step top atlas eps (E:real^3->A) Ei L ((e:int->real^3->A)(&m)) ein
                  (e(&(m + 1))) ei' Delta d0 w1 w2` ASSUME_TAC THENL
   [REWRITE_TAC[apx_eng_step] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `eps:real`; `E:real^3->A`; `Ei:A->real^3`; `L:real`;
                 `(e:int->real^3->A)(&m)`; `ein:A->real^3`;
                 `(e:int->real^3->A)(&(m + 1))`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `(e:int->real^3->A)(&0)`;
                 `sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) /
                       mfd_scalar atlas g (x(&(m + 1))))`;
                 `&7 * sqrt alpha1`; `Ds:real->real`; `C:real`] APXC_TUBE_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E':real^3->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `L + inv(&2 * eps) <= L + Delta /\
                (!y. apx_sval y < L + inv(&8 * eps) + &1 ==> (E':real^3->A) y = E y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXPAND_TAC "w1" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`E':real^3->A`; `L + Delta:real`;
                        `\i. if i = m + 1 then L + Delta else (c:num->real) i`] THEN
  ASM_REWRITE_TAC[APX_UNIONS_UPTO_SUC] THEN
  MATCH_MP_TAC APX_CMP_STEP THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `Ei:A->real^3`; `ein:A->real^3`; `ei':A->real^3`;
                        `w1:real`; `w2:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(j:num) <= m` THEN UNDISCH_TAC `(m:num) < n` THEN ARITH_TAC;
      SIMP_TAC[rfs_neck]];
    UNDISCH_TAC `&32 * d0 <= inv eps` THEN REWRITE_TAC[REAL_INV_MUL] THEN
    REAL_ARITH_TAC]);;


(* The initial finite segments of a one-sided infinite chain are chains.     *)

let APXC_SUBCHAIN_UPTO = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) n.
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e
     ==> apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX21_SUBCHAIN THEN
  EXISTS_TAC `{i:int | &0 <= i}` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[apx_int_interval; IN_ELIM_THM] THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&0:int` THEN
    REWRITE_TAC[INT_POS; INT_LE_REFL];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]]);;

(* The sequence of glued tubes of the initial segments: each extends the    *)
(* previous one, agreeing with it below level L_m + 1/(8 eps) + 1, and the   *)
(* lengths grow by at least 1/(2 eps) (dependent choice over the steps of   *)
(* APXC_CHAIN_STEP, starting from the first neck).                          *)

let APXC_SEQ = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !u top atlas (g:A->real^3^3) eps x (e:int->real^3->A) Ds C.
           SMT_PRODUCT2_STATEMENT (u:A->bool) /\
           &0 < eps /\ eps <= eps1 /\ &96 * eps <= &1 /\ hausdorff_space top /\
           riemannian_metric atlas g /\
           apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
           (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
           &0 < C /\ sqrt alpha1 <= &1 / &2560 /\ C * sqrt alpha1 <= &1 / &2560
           ==> ?EE LL cc.
                 !m. apx_eng_tube top atlas eps (e(&0)) (e(&m)) ((EE:num->real^3->A) m)
                                  ((LL:num->real) m) /\
                     IMAGE (EE m) (apx_slab (--inv eps) (LL m + inv eps)) =
                     UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m} /\
                     apx_eng_cmp top atlas eps (EE m) (LL m) e ((cc:num->num->real) m) m
                                 (&80 * sqrt alpha1 * inv eps) /\
                     LL m + inv(&2 * eps) <= LL(SUC m) /\
                     (!y. apx_sval y < LL m + inv(&8 * eps) + &1 ==> EE (SUC m) y = EE m y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APXC_CHAIN_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "st")] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ct")] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\m:num (s:(real^3->A)#real#(num->real)).
       apx_eng_tube top atlas eps ((e:int->real^3->A)(&0)) (e(&m)) (FST s) (FST(SND s)) /\
       IMAGE (FST s) (apx_slab (--inv eps) (FST(SND s) + inv eps)) =
       UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m} /\
       apx_eng_cmp top atlas eps (FST s) (FST(SND s)) e (SND(SND s)) m
                   (&80 * sqrt alpha1 * inv eps)`;
    `\m:num (s:(real^3->A)#real#(num->real)) (s':(real^3->A)#real#(num->real)).
       FST(SND s) + inv(&2 * eps) <= FST(SND s') /\
       (!v. apx_sval v < FST(SND s) + inv(&8 * eps) + &1 ==> FST s' v = FST s v)`]
   DEPENDENT_CHOICE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ct" (MP_TAC o SPECL [`u:A->bool`; `top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `0`;
        `x:int->A`; `e:int->real^3->A`; `Ds:real->real`; `C:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXC_SUBCHAIN_UPTO THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_REFL] THEN
      DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
        (X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `(E:real^3->A),(L:real),(c:num->real)` THEN
      ASM_REWRITE_TAC[FST; SND];
      MAP_EVERY X_GEN_TAC [`m:num`; `s:(real^3->A)#real#(num->real)`] THEN
      STRIP_TAC THEN
      USE_THEN "st" (MP_TAC o SPECL [`u:A->bool`; `top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `m + 1`;
        `x:int->A`; `e:int->real^3->A`; `Ds:real->real`; `C:real`; `m:num`;
        `FST(s:(real^3->A)#real#(num->real))`;
        `FST(SND(s:(real^3->A)#real#(num->real)))`;
        `SND(SND(s:(real^3->A)#real#(num->real)))`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `m < m + 1`] THEN
        MATCH_MP_TAC APXC_SUBCHAIN_UPTO THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `E':real^3->A` (X_CHOOSE_THEN `L':real`
        (X_CHOOSE_THEN `c':num->real` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `(E':real^3->A),(L':real),(c':num->real)` THEN
      ASM_REWRITE_TAC[FST; SND; ADD1]];
    DISCH_THEN(X_CHOOSE_THEN `f:num->(real^3->A)#real#(num->real)` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`\m. FST((f:num->(real^3->A)#real#(num->real)) m)`;
                          `\m. FST(SND((f:num->(real^3->A)#real#(num->real)) m))`;
                          `\m. SND(SND((f:num->(real^3->A)#real#(num->real)) m))`] THEN
    BETA_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[]]);;

(* Agreement of a sequence of maps below increasing levels, and the limit   *)
(* map E y = E_m y for any m with s(y) below level m.                       *)

let APXC_AGREE = prove
 (`!(EE:num->real^3->A) (B:num->real).
     (!m. B m <= B(SUC m)) /\
     (!m y. apx_sval y < B m ==> EE (SUC m) y = EE m y)
     ==> !m n y. m <= n /\ apx_sval y < B m ==> EE n y = EE m y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\m n. (B:num->real) m <= B n /\
                      !v. apx_sval v < B m ==> (EE:num->real^3->A) n v = EE m v`
         TRANSITIVE_STEPWISE_LE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL];
      MAP_EVERY X_GEN_TAC [`p:num`; `q:num`; `r:num`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `apx_sval v < (B:num->real) q` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
      GEN_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    MESON_TAC[]]);;

let APXC_LIMIT_EQ = prove
 (`!(EE:num->real^3->A) (B:num->real) m y.
     (!m. B m <= B(SUC m)) /\
     (!m y. apx_sval y < B m ==> EE (SUC m) y = EE m y) /\
     apx_sval y < B m
     ==> EE (@m. apx_sval y < B m) y = EE m y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`EE:num->real^3->A`; `B:num->real`] APXC_AGREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `m0 = @m. apx_sval(y:real^3) < (B:num->real) m` THEN
  SUBGOAL_THEN `apx_sval(y:real^3) < (B:num->real) m0` ASSUME_TAC THENL
   [EXPAND_TAC "m0" THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`m:num`; `m0:num`] LE_CASES) THEN ASM_MESON_TAC[]);;

(* Points of the k-th neck are reached by the tube of stage m >= k + 2      *)
(* below the level L + 1/(8 eps) + 1.                                       *)

let APXC_CMP_REACH = prove
 (`!top atlas eps (E:real^3->A) L e c m d0 k z.
     apx_eng_cmp top atlas eps E L e c m d0 /\ &0 < eps /\
     &2 * d0 <= inv(&8 * eps) + &1 /\ k + 2 <= m /\ z IN rfs_neck_dom eps
     ==> ?y. y IN apx_slab (--inv eps) (L + inv(&8 * eps) + &1) /\ E y = e(&k) z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[apx_eng_cmp] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gr") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "re") (K ALL_TAC)))))))) THEN
  REMOVE_THEN "re" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:num->real`; `m:num`; `eps:real`] APX_CMP_GROWTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `inv eps <= (c:num->real) m - c k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(m - k) * inv(&2 * eps)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv eps = &2 * inv(&2 * eps)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
  REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The region beyond a sphere in terms of the s-value, and its exhaustion   *)
(* by slabs with levels B m >= m.                                            *)

let APXC_OUTER_SVAL = prove
 (`!a y:real^3. exp(a / sqrt(&2)) < norm y <=> ~(y = vec 0) /\ a < apx_sval y`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THENL
   [MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_EXP_LT_NORM; apx_sval] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let APXC_SLAB_UNIONS = prove
 (`!a (B:num->real).
     (!m. &m <= B m)
     ==> (!y:real^3. exp(a / sqrt(&2)) < norm y <=> ?m. y IN apx_slab a (B m)) /\
         UNIONS {apx_slab a (B m) | m IN (:num)} = {y:real^3 | exp(a / sqrt(&2)) < norm y}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y:real^3. exp(a / sqrt(&2)) < norm y <=> ?m. y IN apx_slab a ((B:num->real) m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APXC_OUTER_SVAL; APX_SLAB_SVAL] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `apx_sval(y:real^3) + &1` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

(* Membership in the union of a one-sided infinite chain. *)

let APXC_IN_CHAIN_UNION = prove
 (`!eps (e:int->real^3->A) p.
     p IN apx_chain_union eps {i:int | &0 <= i} e <=>
     ?k. p IN IMAGE (e(&k)) (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(SPEC `i:int` INT_OF_NUM_EXISTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
    EXISTS_TAC `k:num` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    EXISTS_TAC `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `&k:int` THEN REWRITE_TAC[INT_POS]]);;

(* The limit of the sequence of glued tubes: one parametrization of the     *)
(* region beyond the inner sphere of the first neck, equal to the first     *)
(* neck there, with image the chain union; the k-th neck lies in the image  *)
(* of a bounded slab.                                                       *)

let APXC_GLUED = prove
 (`!top atlas eps (e:int->real^3->A) (EE:num->real^3->A) LL cc d0.
     smooth_manifold_atlas top atlas /\ &0 < eps /\ eps <= &1 / &96 /\
     &2 * d0 <= inv(&8 * eps) + &1 /\
     (!m. apx_eng_tube top atlas eps (e(&0)) (e(&m)) (EE m) (LL m) /\
          IMAGE (EE m) (apx_slab (--inv eps) (LL m + inv eps)) =
          UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m} /\
          apx_eng_cmp top atlas eps (EE m) (LL m) e ((cc:num->num->real) m) m d0 /\
          LL m + inv(&2 * eps) <= LL(SUC m) /\
          (!y. apx_sval y < LL m + inv(&8 * eps) + &1 ==> EE (SUC m) y = EE m y))
     ==> ?E. mfd_param top atlas {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} E /\
             (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
             IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
             apx_chain_union eps {i:int | &0 <= i} e /\
             (!n. ?rho. apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e SUBSET
                        IMAGE E (apx_slab (--inv eps) rho))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sq"))))) THEN
  SUBGOAL_THEN `&96 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &96`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= inv(&2 * eps) /\ &0 < inv(&8 * eps) /\ inv(&8 * eps) + &1 <= inv eps`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!m. (LL:num->real) m + inv(&2 * eps) <= LL(SUC m)` (LABEL_TAC "gr") THENL
   [GEN_TAC THEN USE_THEN "sq" (MP_TAC o SPEC `m:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m y. apx_sval y < (LL:num->real) m + inv(&8 * eps) + &1
                      ==> (EE:num->real^3->A) (SUC m) y = EE m y` (LABEL_TAC "ag") THENL
   [REPEAT GEN_TAC THEN USE_THEN "sq" (MP_TAC o SPEC `m:num`) THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. (LL:num->real) m + inv(&8 * eps) + &1 <= LL(SUC m) + inv(&8 * eps) + &1`
  (LABEL_TAC "mo") THENL
   [GEN_TAC THEN USE_THEN "gr" (MP_TAC o SPEC `m:num`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!m. &m <= (LL:num->real) m` (LABEL_TAC "nl") THENL
   [INDUCT_TAC THENL
     [USE_THEN "sq" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[apx_eng_tube] THEN SIMP_TAC[];
      USE_THEN "gr" (MP_TAC o SPEC `m:num`) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Einf = \y:real^3. (EE:num->real^3->A)
                       (@m. apx_sval y < (LL:num->real) m + inv(&8 * eps) + &1) y` THEN
  SUBGOAL_THEN `!m y. apx_sval y < (LL:num->real) m + inv(&8 * eps) + &1
                      ==> (Einf:real^3->A) y = (EE:num->real^3->A) m y` (LABEL_TAC "lim") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "Einf" THEN BETA_TAC THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL [`EE:num->real^3->A`;
      `\m. (LL:num->real) m + inv(&8 * eps) + &1`; `m:num`; `y:real^3`] APXC_LIMIT_EQ)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`--inv eps`; `\m. (LL:num->real) m + inv(&8 * eps) + &1`]
    APXC_SLAB_UNIONS)) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN USE_THEN "nl" (MP_TAC o SPEC `m:num`) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ex") (LABEL_TAC "un"))] THEN
  SUBGOAL_THEN `!m y. y IN apx_slab (--inv eps) ((LL:num->real) m + inv(&8 * eps) + &1)
                      ==> ?k z. z IN rfs_neck_dom eps /\
                                (Einf:real^3->A) y = (e:int->real^3->A)(&k) z`
  (LABEL_TAC "ran") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Einf:real^3->A) y = (EE:num->real^3->A) m y` SUBST1_TAC THENL
     [USE_THEN "lim" MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) ((LL:num->real) m + inv(&8 * eps) + &1)` THEN
      SIMP_TAC[APX_SLAB_SVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(EE:num->real^3->A) m y IN
                  UNIONS {IMAGE ((e:int->real^3->A)(&i)) (rfs_neck_dom eps) | i <= m}`
    MP_TAC THENL
     [USE_THEN "sq" (MP_TAC o SPEC `m:num`) THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `apx_slab (--inv eps) ((LL:num->real) m + inv(&8 * eps) + &1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
      UNDISCH_TAC `t = IMAGE ((e:int->real^3->A)(&i)) (rfs_neck_dom eps)` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n k z. k <= n /\ z IN rfs_neck_dom eps
                        ==> ?y. y IN apx_slab (--inv eps)
                                       ((LL:num->real)(n + 2) + inv(&8 * eps) + &1) /\
                                (Einf:real^3->A) y = (e:int->real^3->A)(&k) z`
  (LABEL_TAC "rea") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `(EE:num->real^3->A)(n + 2)`; `(LL:num->real)(n + 2)`; `e:int->real^3->A`;
                   `(cc:num->num->real)(n + 2)`; `n + 2`; `d0:real`; `k:num`; `z:real^3`]
           APXC_CMP_REACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `k + 2 <= n + 2 <=> k <= n`] THEN
      USE_THEN "sq" (MP_TAC o SPEC `n + 2`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Einf:real^3->A) y = (EE:num->real^3->A)(n + 2) y` SUBST1_TAC THENL
     [USE_THEN "lim" MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps)
                                 ((LL:num->real)(n + 2) + inv(&8 * eps) + &1)` THEN
      SIMP_TAC[APX_SLAB_SVAL];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `Einf:real^3->A` THEN
  CONJ_TAC THENL
   [USE_THEN "un" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
       `\m. apx_slab (--inv eps) ((LL:num->real) m + inv(&8 * eps) + &1)`; `Einf:real^3->A`]
       APXC_PARAM_NESTED)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      USE_THEN "mo" (MP_TAC o SPEC `m:num`) THEN REAL_ARITH_TAC;
      X_GEN_TAC `m:num` THEN MATCH_MP_TAC MFD_PARAM_EQ THEN
      EXISTS_TAC `(EE:num->real^3->A) m` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
        EXISTS_TAC `apx_slab (--inv eps) ((LL:num->real) m + inv eps)` THEN
        REPEAT CONJ_TAC THENL
         [USE_THEN "sq" (MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[apx_eng_tube] THEN
          SIMP_TAC[];
          REWRITE_TAC[apx_slab; OPEN_ANNULUS];
          MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC];
        X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
        USE_THEN "lim" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Einf:real^3->A) y = (EE:num->real^3->A) 0 y` SUBST1_TAC THENL
     [USE_THEN "lim" MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (inv(&8 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN USE_THEN "nl" (MP_TAC o SPEC `0`) THEN
      STRIP_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "sq" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[apx_eng_tube] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; APXC_IN_CHAIN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      USE_THEN "ex" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
      USE_THEN "ran" (MP_TAC o SPECL [`m:num`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `z:real^3`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
      USE_THEN "rea" (MP_TAC o SPECL [`k:num`; `k:num`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ex" (fun th -> REWRITE_TAC[th]) THEN
      EXISTS_TAC `k + 2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN EXISTS_TAC `(LL:num->real)(n + 2) + inv(&8 * eps) + &1` THEN
  REWRITE_TAC[APX_CHAIN_UNION_UPTO; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `p:A` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  USE_THEN "rea" (MP_TAC o SPECL [`n:num`; `k:num`; `z:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]);;

(* The constants and the core statement at the chain type (as APX_A13_CORE, *)
(* with the sequence of APXC_SEQ in place of one finite chain).             *)

let APXC_CHART_CORE = prove
 (`!u:A->bool.
     SMT_PRODUCT2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas g eps x e.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas (g:A->real^3^3) /\
              apx_chain (top,atlas) g eps {i:int | &0 <= i} x (e:int->real^3->A)
              ==> ?E. mfd_param top atlas {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} E /\
                      (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                      IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
                      apx_chain_union eps {i:int | &0 <= i} e /\
                      (!n. ?rho. apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e SUBSET
                                 IMAGE E (apx_slab (--inv eps) rho))`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `Ds:real->real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)
    APX_SMOOTH_STEP_DERIV THEN
  MP_TAC(SPEC `C:real` APX_ENGINE_CONSTANTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `alpha1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `u:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `alpha1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  ABBREV_TAC `eps1 = min eps2 alpha1` THEN
  SUBGOAL_THEN `&0 < eps1 /\ eps1 <= alpha1 /\ eps1 <= eps2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APXC_SEQ) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "sq")] THEN
  EXISTS_TAC `min eps1 (&1 / &96)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "sq" (MP_TAC o SPECL [`u:A->bool`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`;
    `x:int->A`; `e:int->real^3->A`; `Ds:real->real`; `C:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `EE:num->real^3->A` (X_CHOOSE_THEN `LL:num->real`
    (X_CHOOSE_THEN `cc:num->num->real` ASSUME_TAC))) THEN
  MATCH_MP_TAC APXC_GLUED THEN
  MAP_EVERY EXISTS_TAC [`EE:num->real^3->A`; `LL:num->real`; `cc:num->num->real`;
                        `&80 * sqrt alpha1 * inv eps`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x
                           (e:int->real^3->A)` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MP_TAC o SPEC `&0:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[IN_ELIM_THM; INT_LE_REFL; rfs_neck] THEN SIMP_TAC[];
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= inv eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt alpha1 * inv eps <= (&1 / &2560) * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= inv eps` THEN
    REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC]);;

