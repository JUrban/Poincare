(* ========================================================================= *)
(* pc_moi_s3032_stmt6: the s32 state with a member invariant.                *)
(* MOI_S32_CLASSIFY (pc_moi_s3032_stmt.ml) is false as stated: moi_s32_state *)
(* forgets where a member came from, so a 4-holed sphere in Int S''_(2i)     *)
(* with 4 essential longitudes of T''_(2i) as boundary can be added to any   *)
(* state at all levels.  The book's count of essential boundary polygons (0  *)
(* or 2) uses that a component C of L lies in T''_(2i+1) (28.6 there).       *)
(* Here:                                                                     *)
(*   moi_s32_essc s2 i c, moi_s32_inessc s2 i c : the components of c       *)
(*     INTER K that are, or are not, essential polygons of T''_(2i) or      *)
(*     T''_(2i+2);                                                          *)
(*   moi_s32_hist s2 i cc c : a history witness, a compact connected        *)
(*     surface c0 (complex cc0) in T''_(2i+1) with boundary c0 INTER K, the *)
(*     same essential polygons as c, and chi + (number of inessential       *)
(*     polygons) equal for c and c0 (Step 1 caps an inessential polygon:   *)
(*     chi + 1, one inessential polygon fewer, essc unchanged);            *)
(*   moi_s32_state3 : moi_s32_state with hist added to the member clause;   *)
(*   MOI_S32_INITIAL_3, MOI_S32_LEVEL_3, MOI_S32_ITERATE_3,                 *)
(*     MOI_S32_CLASSIFY_3 : the statements with moi_s32_state3 (CLASSIFY_3  *)
(*     with the foundation terms of the torus argument);                    *)
(*   MOI_S3S6_STATE3 : |- moi_s32_state3 ==> moi_s32_state;                 *)
(*   MOI_S3S6_HIST_TORUS : a surface inside T''_(2i+1) is its own witness   *)
(*     (the invariant holds for the members of the initial state).          *)
(* LEVEL_3 does not imply LEVEL_2 (a state need not be a state3).           *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt5.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The definitions.                                                          *)
(* ------------------------------------------------------------------------- *)

(* The components of c INTER K that are, or are not, essential polygons of  *)
(* the two even tori of level i.                                             *)

let moi_s32_essc = new_definition
 `moi_s32_essc (s2:int->real^3->bool) (i:int) (c:real^3->bool) =
    {jj | jj IN components (c INTER moi_s32_evens s2) /\
          (moi_s32_ess s2 (&2 * i) jj \/ moi_s32_ess s2 (&2 * i + &2) jj)}`;;

let moi_s32_inessc = new_definition
 `moi_s32_inessc (s2:int->real^3->bool) (i:int) (c:real^3->bool) =
    {jj | jj IN components (c INTER moi_s32_evens s2) /\
          ~(moi_s32_ess s2 (&2 * i) jj \/ moi_s32_ess s2 (&2 * i + &2) jj)}`;;

(* The history witness: c0 is the component of L_i that c came from.  FINITE *)
(* and HAS_SIZE style (CARD of an infinite set is 0).                        *)

let moi_s32_hist = new_definition
 `moi_s32_hist (s2:int->real^3->bool) (i:int) (cc:(real^3->bool)->bool) (c:real^3->bool) <=>
    ?c0 cc0. FINITE cc0 /\ combinatorial_manifold_with_boundary 2 cc0 /\ UNIONS cc0 = c0 /\
             connected c0 /\ c0 SUBSET frontier (s2 (&2 * i + &1)) /\
             surface_boundary cc0 = c0 INTER moi_s32_evens s2 /\
             moi_s32_essc s2 i c = moi_s32_essc s2 i c0 /\
             FINITE (moi_s32_inessc s2 i c) /\ FINITE (moi_s32_inessc s2 i c0) /\
             complex_euler cc + &(CARD (moi_s32_inessc s2 i c)) =
             complex_euler cc0 + &(CARD (moi_s32_inessc s2 i c0))`;;

(* The state with the witness in the member clause (the member clause of     *)
(* moi_s32_state verbatim as the first conjunct; the other four clauses      *)
(* verbatim).                                                                *)

let moi_s32_state3 = new_definition
 `moi_s32_state3 (g:real^3->real^3) (dd:int->real^3->bool) (s2:int->real^3->bool)
                 (lev:int->bool) (fam:(real^3->bool)->bool) <=>
    pairwise DISJOINT fam /\
    (!c. c IN fam
         ==> ?i cc. (c SUBSET moi_s32_lvl g dd i /\
                     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
                     UNIONS cc = c /\ connected c /\ ~(c = {}) /\
                     surface_boundary cc = c INTER moi_s32_evens s2 /\
                     c INTER moi_s32_evens s2 SUBSET
                       frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2)) /\
                     (i IN lev
                      ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i)))
                               ==> moi_s32_ess s2 (&2 * i) jj) /\
                     ((i + &1) IN lev
                      ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i + &2)))
                               ==> moi_s32_ess s2 (&2 * i + &2) jj)) /\
                    moi_s32_hist s2 i cc c) /\
    (!i. FINITE {c | c IN fam /\ c SUBSET moi_s32_lvl g dd i}) /\
    closed_in (subtopology euclidean (moi_s32_open g)) (moi_s32_set g s2 fam) /\
    separates_in (moi_s32_open g) (moi_s32_set g s2 fam)
                 {g moi_s32_qlo} {g moi_s32_qhi}`;;


(* ------------------------------------------------------------------------- *)
(* The restated statements.  The bodies are those of INITIAL, LEVEL_2,       *)
(* ITERATE and CLASSIFY with moi_s32_state3 for moi_s32_state                *)
(* (checked below).  CLASSIFY_3 adds the foundation terms of the torus      *)
(* argument on the witness: SURFACE_PLANAR (Types 2, 3 are annuli),         *)
(* PL_SOLID_TORUS_BASIC (a solid torus is not simply connected, so a        *)
(* polygon carrying its loops bounds no disk), EULER_UNION and EULER_VALUES *)
(* (chi of the witness plus its caps), HOLED_DISK_ANNULUS.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S32_INITIAL_3 =
  mk_imp(list_mk_conj [moi_std_csq (moi_n3 MOI_S30_SURFACE_TRIANG);
                       moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC],
 `!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> ?fam. moi_s32_state3 g dd s2 {} fam /\
               moi_s32_set g s2 fam =
               moi_s32_evens s2 UNION
               (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
                UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION
               {g (vec 0)}`);;

let MOI_S32_LEVEL_3 =
  mk_imp(list_mk_conj [`MOISE_303_STATEMENT`; `MOISE_268_STATEMENT`;
                       moi_n3 MOI_FND_BICOLLAR_CURVE_2;
                       moi_std_csq (moi_n3 MOI_S30_SURFACE_TRIANG)],
 `!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state3 g dd s2 lev fam /\ ~(i IN lev)
     ==> ?fam'. moi_s32_state3 g dd s2 (i INSERT lev) fam' /\
                moi_s32_set g s2 fam' DIFF interior (IMAGE g (revolution (dd (&2 * i)))) =
                moi_s32_set g s2 fam DIFF interior (IMAGE g (revolution (dd (&2 * i)))) /\
                {c | c IN fam' /\
                     DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
                {c | c IN fam /\
                     DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`);;

let MOI_S32_ITERATE_3 =
  mk_imp(list_mk_conj [moi_std_csq MOI_S32_LEVEL_3; moi_n3 MOI_S32_LIMIT],
 `!(g:real^3->real^3) v pp dd s2 fam.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state3 g dd s2 {} fam
     ==> ?fam'. moi_s32_state3 g dd s2 (:int) fam'`);;

let MOI_S32_CLASSIFY_3 =
  mk_imp(list_mk_conj [`MOISE_314_STATEMENT`; `MOISE_286_STATEMENT`;
                       `MOISE_268_STATEMENT`; moi_n3 MOI_FND_BICOLLAR_CURVE_2;
                       moi_n3 MOI_FND_SURFACE_PLANAR; moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC;
                       moi_n3 MOI_FND_EULER_UNION; moi_n3 MOI_FND_EULER_VALUES;
                       moi_n3 MOI_FND_HOLED_DISK_ANNULUS],
 `!(g:real^3->real^3) v pp dd s2 fam.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state3 g dd s2 (:int) fam
     ==> moi_s32_reduced g dd s2 fam`);;


(* ------------------------------------------------------------------------- *)
(* The bridge state3 ==> state; the sanity lemma (a surface in T''_(2i+1),   *)
(* such as a member of the initial state, is its own witness); teeth.        *)
(* LEVEL_3 does not give LEVEL_2: a state need not be a state3 (the 4-holed  *)
(* sphere family below is a state at all levels, not a state3), so there is  *)
(* no bridge LEVEL_3 ==> LEVEL_2; the _3 chain INITIAL_3, ITERATE_3,         *)
(* CLASSIFY_3 is used in place of INITIAL, ITERATE, CLASSIFY in the glue.    *)
(* Teeth (an informal check): for the 4-holed sphere B in Int S''_(2i) with  *)
(* four essential longitudes of T''_(2i) as boundary, a witness c0 would be *)
(* a connected surface in T''_(2i+1) whose boundary contains four polygons  *)
(* essential in T''_(2i) (so, by 31.4, in T''_(2i+1)); by 28.6 a connected  *)
(* subsurface of a torus has at most two essential boundary polygons.  This *)
(* is the torus argument of CLASSIFY_3.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3S6_STATE3 = prove
 (`!(g:real^3->real^3) dd s2 lev fam.
     moi_s32_state3 g dd s2 lev fam ==> moi_s32_state g dd s2 lev fam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_state3; moi_s32_state] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(c:real^3->bool) IN fam`)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  SIMP_TAC[]);;

(* A finite family of connected sets has finitely many components. *)

let MOI_S3S6_FINITE_COMPONENTS = prove
 (`!f:(real^N->bool)->bool.
     FINITE f /\ (!s. s IN f ==> connected s) ==> FINITE (components (UNIONS f))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\s:real^N->bool. connected_component (UNIONS f) (@x. x IN s))
                    {s | s IN f /\ ~(s = {})}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_COMPONENTS] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS f` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET connected_component (UNIONS f) x` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; IN]);;

(* Sanity: a surface in T''_(2i+1) with boundary its trace on K is its own *)
(* history witness (the members of the initial state, INITIAL_3).           *)

let MOI_S3S6_HIST_TORUS = prove
 (`!(s2:int->real^3->bool) i cc c.
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ UNIONS cc = c /\
     connected c /\ c SUBSET frontier (s2 (&2 * i + &1)) /\
     surface_boundary cc = c INTER moi_s32_evens s2
     ==> moi_s32_hist s2 i cc c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s32_hist] THEN
  MAP_EVERY EXISTS_TAC [`c:real^3->bool`; `cc:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `components (surface_boundary (cc:(real^3->bool)->bool))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[surface_boundary] THEN MATCH_MP_TAC MOI_S3S6_FINITE_COMPONENTS THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cc:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (cc:(real^3->bool)->bool)` THEN
      REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
      STRIP_TAC THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]];
    ASM_REWRITE_TAC[moi_s32_inessc] THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Load-time text checks.  Each _3 term is closed, boolean and without type  *)
(* variables; the state3 member clause has the member clause of              *)
(* moi_s32_state as its first conjunct and the other four clauses are those  *)
(* of moi_s32_state; INITIAL_3, LEVEL_3 and the consequents of ITERATE_3,    *)
(* CLASSIFY_3 are the original terms with moi_s32_state3 for moi_s32_state;  *)
(* CLASSIFY_3 keeps the original antecedents; the three theorems have no     *)
(* hypotheses.                                                               *)
(* ------------------------------------------------------------------------- *)

let moi_s3s6_clauses th =
  conjuncts (rhs (snd (strip_forall (concl th))));;

let moi_s3s6_member_body th =
  snd (strip_exists (rand (snd (dest_forall (el 1 (moi_s3s6_clauses th))))));;

let moi_s3s6_st3 = subst [`moi_s32_state3`,`moi_s32_state`];;

let moi_s3s6_check =
  forall (fun t -> frees t = [] && type_of t = bool_ty && type_vars_in_term t = [])
    [MOI_S32_INITIAL_3; MOI_S32_LEVEL_3; MOI_S32_ITERATE_3; MOI_S32_CLASSIFY_3] &&
  aconv (lhand (moi_s3s6_member_body moi_s32_state3)) (moi_s3s6_member_body moi_s32_state) &&
  (let c3 = moi_s3s6_clauses moi_s32_state3 and c = moi_s3s6_clauses moi_s32_state in
   length c3 = 5 && length c = 5 &&
   forall (fun k -> aconv (el k c3) (el k c)) [0; 2; 3; 4]) &&
  aconv MOI_S32_INITIAL_3 (moi_s3s6_st3 MOI_S32_INITIAL) &&
  aconv MOI_S32_LEVEL_3 (moi_s3s6_st3 MOI_S32_LEVEL_2) &&
  aconv (moi_std_csq MOI_S32_ITERATE_3) (moi_s3s6_st3 (moi_std_csq MOI_S32_ITERATE)) &&
  aconv (lhand MOI_S32_ITERATE_3)
        (list_mk_conj [moi_std_csq MOI_S32_LEVEL_3; moi_n3 MOI_S32_LIMIT]) &&
  aconv (moi_std_csq MOI_S32_CLASSIFY_3) (moi_s3s6_st3 (moi_std_csq MOI_S32_CLASSIFY)) &&
  forall (fun t -> exists (aconv t) (conjuncts (lhand MOI_S32_CLASSIFY_3)))
         (conjuncts (lhand MOI_S32_CLASSIFY)) &&
  forall (fun th -> hyp th = [])
    [MOI_S3S6_STATE3; MOI_S3S6_FINITE_COMPONENTS; MOI_S3S6_HIST_TORUS];;

print_string ("S3S6 " ^
   string_of_bool (moi_s3s6_check) ^
   "\n");;

(* ------------------------------------------------------------------------- *)
(* The 32.2 glue over the _3 chain.  MOI_S3S6_322_CORE is MOI_STD_322_CORE   *)
(* (pc_moi_s3032_stmt.ml) with the consequents of INITIAL_3, ITERATE_3 and   *)
(* CLASSIFY_3 (the same proof: the three steps only pass the state along,    *)
(* here moi_s32_state3).  MOI_S3S6_322 is its full form, the closure         *)
(* preferring the _3 statements, then the restated statements of stmt5.      *)
(* moi_s3s6_glue: the nine items of moi_s3s5_glue with MOI_S3S6_322 for      *)
(* 32.2; moi_s3s6_glue_check: none of the original INITIAL, ITERATE,         *)
(* CLASSIFY, LEVEL (nor LEVEL_2, ITERATE_2) among its hypotheses, every      *)
(* hypothesis one of the original glue or a restated term or an antecedent   *)
(* of one.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3S6_322_CORE = prove
 (mk_imp(list_mk_conj
   [moi_std_csq MOI_S32_CHART; MOI_S32_MODEL_V; moi_std_csq MOI_S32_TOWER;
    moi_std_csq MOI_S32_INITIAL_3; moi_std_csq MOI_S32_ITERATE_3;
    moi_std_csq MOI_S32_CLASSIFY_3; moi_std_csq MOI_S32_STEPS24;
    MOI_S32_CELL; MOI_S32_SIDES],
   `MOISE_322_CELLS_STATEMENT`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "chart") (CONJUNCTS_THEN2 (LABEL_TAC "modv")
   (CONJUNCTS_THEN2 (LABEL_TAC "tower") (CONJUNCTS_THEN2 (LABEL_TAC "init")
   (CONJUNCTS_THEN2 (LABEL_TAC "iter") (CONJUNCTS_THEN2 (LABEL_TAC "class")
   (CONJUNCTS_THEN2 (LABEL_TAC "steps") (CONJUNCTS_THEN2 (LABEL_TAC "cell")
    (LABEL_TAC "sides"))))))))) THEN
  REWRITE_TAC[MOISE_322_CELLS_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`c1:real^3->bool`; `c2:real^3->bool`; `dd:real^3->bool`;
    `jj:real^3->bool`; `p:real^3`; `q1:real^3`; `q2:real^3`; `h:real^3->real^3`;
    `w:real^3->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "chart" (MP_TAC o SPECL [`c1:real^3->bool`; `c2:real^3->bool`;
    `dd:real^3->bool`; `jj:real^3->bool`; `p:real^3`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `psi':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`psi:real^3->real^3`; `psi':real^3->real^3`; `h:real^3->real^3`;
    `c1:real^3->bool`; `c2:real^3->bool`; `dd:real^3->bool`; `jj:real^3->bool`;
    `p:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3->bool`] MOI_STD_322_TRANSFER) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REMOVE_THEN "modv" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `w:real^3->bool`; `(psi':real^3->real^3) q1`; `(psi':real^3->real^3) q2`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^3->bool`
    (X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `k2:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(v:real^3->bool) SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC(ASSUME `moi_s32_model ((h:real^3->real^3) o (psi:real^3->real^3)) v`) THEN
    REWRITE_TAC[moi_s32_model] THEN MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "tower" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
                                       `v:real^3->bool`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:int->real^3` (X_CHOOSE_THEN `di:int->real^3->bool`
    (X_CHOOSE_THEN `s2:int->real^3->bool` ASSUME_TAC))) THEN
  REMOVE_THEN "init" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`]) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fam0:(real^3->bool)->bool` (ASSUME_TAC o CONJUNCT1)) THEN
  REMOVE_THEN "iter" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `fam0:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `fam:(real^3->bool)->bool`) THEN
  REMOVE_THEN "class" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  REMOVE_THEN "steps" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:int->real^3->bool` (X_CHOOSE_THEN `bb:int->real^3->bool`
    (X_CHOOSE_THEN `jl:int->real^3->bool` (X_CHOOSE_THEN `jh:int->real^3->bool`
      ASSUME_TAC)))) THEN
  REMOVE_THEN "cell" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `hh:int->real^3->bool`; `bb:int->real^3->bool`;
    `jl:int->real^3->bool`; `jh:int->real^3->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REMOVE_THEN "sides" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `hh:int->real^3->bool`; `bb:int->real^3->bool`;
    `jl:int->real^3->bool`; `jh:int->real^3->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3->bool` (X_CHOOSE_THEN `u2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^3) moi_s32_cyl = c1 UNION c2` ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^3->real^3) (c1 UNION c2) = IMAGE (h o psi) moi_s32_cyl /\
    IMAGE h jj = IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_rim /\
    h p = ((h:real^3->real^3) o (psi:real^3->real^3)) (vec 0) /\
    IMAGE h (frontier c1 DIFF (dd DIFF jj)) =
    IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_lohemi /\
    IMAGE h (frontier c2 DIFF (dd DIFF jj)) =
    IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_hihemi`
  (fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THENL
   [REWRITE_TAC[IMAGE_o; o_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`moi_s32_chainset ((h:real^3->real^3) o (psi:real^3->real^3)) hh bb UNION
     IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_rim`;
    `u1:real^3->bool`; `u2:real^3->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `((h:real^3->real^3) o (psi:real^3->real^3)) (vec 0) INSERT
                  IMAGE (h o psi) v` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior w:real^3->bool` THEN
        REWRITE_TAC[INTERIOR_SUBSET] THEN FIRST_ASSUM ACCEPT_TAC];
      UNDISCH_TAC `w INTER frontier (IMAGE (h:real^3->real^3) (c1 UNION c2)) = IMAGE h jj` THEN
      REWRITE_TAC[ASSUME `IMAGE (h:real^3->real^3) jj =
                          IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_rim`] THEN
      SET_TAC[]];
    SUBGOAL_THEN `(h:real^3->real^3) q1 = (h o psi) ((psi':real^3->real^3) q1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_STD_322_SIDE THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`;
      `moi_s32_chainset ((h:real^3->real^3) o (psi:real^3->real^3)) hh bb`;
      `k1:real^3->bool`; `moi_s32_qlo`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `k1 UNION k2 SUBSET moi_s32_cyl DIFF (vec 0 INSERT (moi_s32_rim UNION v))` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[IN_INSERT]];
    SUBGOAL_THEN `(h:real^3->real^3) q2 = (h o psi) ((psi':real^3->real^3) q2)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_STD_322_SIDE THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`;
      `moi_s32_chainset ((h:real^3->real^3) o (psi:real^3->real^3)) hh bb`;
      `k2:real^3->bool`; `moi_s32_qhi`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `k1 UNION k2 SUBSET moi_s32_cyl DIFF (vec 0 INSERT (moi_s32_rim UNION v))` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[IN_INSERT]]]);;

let moi_s3s6_new_targets =
  [MOI_S32_INITIAL_3; MOI_S32_LEVEL_3; MOI_S32_ITERATE_3; MOI_S32_CLASSIFY_3];;

let moi_s3s6_find_target a =
  let cands = moi_s3s6_new_targets @ map moi_n3 moi_s3s6_new_targets in
  try Some(find (fun t -> aconv (moi_std_csq t) a) cands)
  with Failure _ -> moi_s3s5_find_target a;;

let rec moi_s3s6_closure stop acc tms =
  match tms with
    [] -> acc
  | a::rest ->
      if exists (aconv a) stop || exists (aconv a) acc
      then moi_s3s6_closure stop acc rest else
      match moi_s3s6_find_target a with
        Some t ->
          if exists (aconv t) acc then moi_s3s6_closure stop acc rest else
          let ants = if is_imp t then conjuncts(fst(dest_imp t)) else [] in
          moi_s3s6_closure stop (t::acc) (ants @ rest)
      | None -> moi_s3s6_closure stop (a::acc) rest;;

let moi_s3s6_full core prod =
  let hyps = conjuncts(fst(dest_imp(concl core))) in
  let stop = if is_imp prod then conjuncts(fst(dest_imp prod)) else [] in
  mk_imp(list_mk_conj(rev(moi_s3s6_closure stop [] hyps)), prod);;

let MOI_S3S6_322 = prove
 (moi_s3s6_full MOI_S3S6_322_CORE MOI_PROD_322_CELLS,
  MOI_STD_FULL_TAC MOI_S3S6_322_CORE);;

let moi_s3s6_glue =
  map (fun (n,th,item) -> if n = "MOI_PROD_322_CELLS" then (n,MOI_S3S6_322,item)
                          else (n,th,item)) moi_s3s5_glue;;

let moi_s3s6_glue_check =
  let forbidden = [MOI_S32_INITIAL; MOI_S32_ITERATE; MOI_S32_CLASSIFY; MOI_S32_LEVEL;
                   MOI_S32_LEVEL_2; MOI_S32_ITERATE_2] in
  let forbidden = forbidden @ map moi_n3 forbidden @ moi_s3s5_forbidden in
  let ts = moi_s3s6_new_targets @ map moi_n3 moi_s3s6_new_targets in
  let allowed = ts @ itlist (fun t acc -> (if is_imp t then conjuncts(fst(dest_imp t)) else [])
                                          @ acc) ts [] @ moi_s3s5_allowed_new in
  let hs = conjuncts(lhand(concl MOI_S3S6_322)) in
  let old_hs = conjuncts(lhand(concl MOI_STD_322)) in
  hyp MOI_S3S6_322 = [] && aconv (rand(concl MOI_S3S6_322)) MOI_PROD_322_CELLS &&
  hyp MOI_S3S6_322_CORE = [] &&
  not (exists (fun h -> exists (aconv h) forbidden) hs) &&
  forall (fun h -> exists (aconv h) old_hs || exists (aconv h) allowed) hs &&
  forall (fun (_,th,item) -> hyp th = [] && aconv (rand(concl th)) item) moi_s3s6_glue;;

print_string ("S3S6_GLUE " ^
   string_of_bool (moi_s3s6_glue_check) ^
   " " ^
   string_of_int ((length (conjuncts (lhand (concl MOI_S3S6_322))))) ^
   "\n");;

