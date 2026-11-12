(* ========================================================================= *)
(* pc_moi_s32_level: Step 1 of the proof of Moise 32.1 at one level         *)
(* (GTM 47, pp.225-226).  Main theorem LEVEL_3 : |- MOI_S32_LEVEL_3         *)
(* (pc_moi_s3032_stmt6.ml).  Route: induction on the number of inessential  *)
(* boundary polygons of the members on the even torus                       *)
(* T = frontier (s2 (&2 * i)); an inmost one is removed by the cut          *)
(* and cap of Moise 30.3 inside                                             *)
(* R = interior (IMAGE g (revolution (dd (&2 * i)))).                       *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt3.ml";;
needs "src/pc_moi_s3032_stmt6.ml";;
needs "src/pc_moi_s32_gfacts.ml";;
needs "src/pc_moi_s28_torus.ml";;
needs "src/pc_moi_fnd_sides.ml";;
needs "src/pc_moi_fnd_surfb0.ml";;
needs "src/pc_moi_s28_cut.ml";;
needs "src/pc_moi_s26_surf.ml";;
needs "src/pc_moi_s28_plane.ml";;
needs "src/pc_moi_cells.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_fnd_bicol.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_bcollar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: bookkeeping of the state at one level.  The inessential          *)
(* polygons of the members on T; when there are none, a state at lev is a  *)
(* state at i INSERT lev (the new clauses of moi_s32_state concern exactly  *)
(* the components on T of the members of the levels i and i - 1).          *)
(* ========================================================================= *)

let moi_s3lv_iness = new_definition
 `moi_s3lv_iness (s2:int->real^3->bool) (i:int) (fam:(real^3->bool)->bool) =
    {jj | ?c. c IN fam /\ jj IN components (c INTER frontier (s2 (&2 * i))) /\
              ~moi_s32_ess s2 (&2 * i) jj}`;;

let MOI_S3LV_DONE = prove
 (`!(g:real^3->real^3) dd s2 lev fam i.
     moi_s32_state g dd s2 lev fam /\ moi_s3lv_iness s2 i fam = {}
     ==> moi_s32_state g dd s2 (i INSERT lev) fam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_state; moi_s3lv_iness] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(c:real^3->bool) IN fam`) o SPEC `c:real^3->bool` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_lvl")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i':int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`i':int`; `cc:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`jj:real^3->bool`; `c:real^3->bool`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_ess")) (concl th) &&
          not(can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_lvl"))
                  (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(i':int) = i` THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&2 * (i':int) + &2 = &2 * i` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                                            REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(i':int) + &1 = i` THEN INT_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`jj:real^3->bool`; `c:real^3->bool`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_ess")) (concl th) &&
          not(can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_lvl"))
                  (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Part 2: facts of the tower at level i.  Revolutions of disjoint          *)
(* sets are disjoint; S''_2i lies in R and is a PL solid torus; a level     *)
(* region meets the image of the 2i-th revolved disk only for the levels    *)
(* i - 1 and i; so finitely many members meet it.                           *)
(* ========================================================================= *)

let MOI_S3LV_REV_DISJOINT = prove
 (`!x y:real^3->bool. DISJOINT x y ==> DISJOINT (revolution x) (revolution y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[revolution; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                                  NOT_IN_EMPTY] THEN
  DISCH_TAC THEN X_GEN_TAC `p:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `q':real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `q':real^3 = q` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3LV_TOWER_LEVEL = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> pl_solid_torus (s2 (&2 * i)) /\
         s2 (&2 * i) SUBSET interior (IMAGE g (revolution (dd (&2 * i)))) /\
         (!k. revolution (dd k) SUBSET moi_s32_cyl) /\
         (!i'. ~(DISJOINT (moi_s32_lvl g dd i') (IMAGE g (revolution (dd (&2 * i)))))
               ==> i' = i - &1 \/ i' = i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_model; moi_s32_tower] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. revolution ((dd:int->real^3->bool) k) SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_solid_torus ((s2:int->real^3->bool) (&2 * i)) /\
                s2 (&2 * i) SUBSET interior (IMAGE (g:real^3->real^3)
                                              (revolution ((dd:int->real^3->bool) (&2 * i))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&2 * i:int` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "canonical_configuration"))
          (concl th))) THEN
    REWRITE_TAC[canonical_configuration] THEN
    DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[ARITH; INT_ADD_RID] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i':int` THEN REWRITE_TAC[moi_s32_lvl; DISJOINT] THEN
  SUBGOAL_THEN
   `!k. ~(IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) k)) INTER
          IMAGE g (revolution (dd (&2 * i))) = {})
        ==> abs(k - &2 * i) <= &1`
  MP_TAC THENL
   [X_GEN_TAC `k:int` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[INT_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `DISJOINT ((dd:int->real^3->bool) k) (dd (&2 * i))` MP_TAC THENL
     [ASM_CASES_TAC `&2 * i + &2 <= k:int` THENL
       [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))
        THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))
        THEN ASM_INT_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S3LV_REV_DISJOINT) THEN
    REWRITE_TAC[DISJOINT] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!(g:real^3->real^3) s a b.
        (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\
        a SUBSET s /\ b SUBSET s /\ a INTER b = {}
        ==> IMAGE g a INTER IMAGE g b = {}`) THEN
    EXISTS_TAC `moi_s32_cyl` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "key") THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `~((a UNION b UNION c) INTER (x:real^3->bool) = {})
    ==> ~(a INTER x = {}) \/ ~(b INTER x = {}) \/ ~(c INTER x = {})`)) THEN
  STRIP_TAC THEN
  USE_THEN "key" (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN INT_ARITH_TAC);;

let MOI_S3LV_TOUCH_FINITE = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ moi_s32_state g dd s2 lev fam
     ==> FINITE {c | c IN fam /\ ~(DISJOINT c (IMAGE g (revolution (dd (&2 * i)))))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_TOWER_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s32_state g dd s2 lev (fam:(real^3->bool)->bool)` THEN
  REWRITE_TAC[moi_s32_state] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c | c IN fam /\ c SUBSET moi_s32_lvl (g:real^3->real^3) dd (i - &1)} UNION
              {c | c IN fam /\ c SUBSET moi_s32_lvl g dd i}` THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(c:real^3->bool) IN fam`) o SPEC `c:real^3->bool` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "combinatorial_manifold_with_boundary"))
          (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i':int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `i' = i - &1 \/ i':int = i` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `~(DISJOINT (c:real^3->bool) (IMAGE (g:real^3->real^3)
                     (revolution ((dd:int->real^3->bool) (&2 * i)))))` THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s32_lvl g dd i'` THEN SET_TAC[];
    DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s32_lvl g dd i'` THEN
    ASM_REWRITE_TAC[SUBSET];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s32_lvl g dd i'` THEN
    ASM_REWRITE_TAC[SUBSET]]);;

(* ========================================================================= *)
(* Part 3: the induction of Step 1 at one level.  If every state with      *)
(* (for any invariant P, used with moi_s32_state3)                          *)
(* an inessential polygon on T has a successor state with fewer of them     *)
(* (a proper subset), the same set outside R and the same members missing  *)
(* R, then every state (with finitely many) reaches one with none.          *)
(* ========================================================================= *)

let MOI_S3LV_INDUCT = prove
 (`!(P:((real^3->bool)->bool)->bool) (g:real^3->real^3) dd s2 i.
     (!fam. P fam /\ ~(moi_s3lv_iness s2 i fam = {})
            ==> ?fam1. P fam1 /\
                       moi_s3lv_iness s2 i fam1 PSUBSET moi_s3lv_iness s2 i fam /\
                       moi_s32_set g s2 fam1 DIFF
                         interior (IMAGE g (revolution (dd (&2 * i)))) =
                       moi_s32_set g s2 fam DIFF
                         interior (IMAGE g (revolution (dd (&2 * i)))) /\
                       {c | c IN fam1 /\
                            DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
                       {c | c IN fam /\
                            DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))})
     ==> !fam. P fam /\ FINITE (moi_s3lv_iness s2 i fam)
               ==> ?fam'. P fam' /\ moi_s3lv_iness s2 i fam' = {} /\
                          moi_s32_set g s2 fam' DIFF
                            interior (IMAGE g (revolution (dd (&2 * i)))) =
                          moi_s32_set g s2 fam DIFF
                            interior (IMAGE g (revolution (dd (&2 * i)))) /\
                          {c | c IN fam' /\
                               DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
                          {c | c IN fam /\
                               DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "step") THEN
  SUBGOAL_THEN
   `!n fam. CARD (moi_s3lv_iness s2 i fam) = n /\
            P fam /\ FINITE (moi_s3lv_iness s2 i fam)
            ==> ?fam'. P fam' /\ moi_s3lv_iness s2 i fam' = {} /\
                       moi_s32_set g s2 fam' DIFF
                         interior (IMAGE g (revolution (dd (&2 * i)))) =
                       moi_s32_set g s2 fam DIFF
                         interior (IMAGE g (revolution (dd (&2 * i)))) /\
                       {c | c IN fam' /\
                            DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
                       {c | c IN fam /\
                            DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `fam:(real^3->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `moi_s3lv_iness s2 i (fam:(real^3->bool)->bool) = {}` THENL
   [EXISTS_TAC `fam:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "step" (MP_TAC o SPEC `fam:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fam1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (moi_s3lv_iness s2 i (fam1:(real^3->bool)->bool)) /\
                CARD (moi_s3lv_iness s2 i fam1) < n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `moi_s3lv_iness s2 i (fam:(real^3->bool)->bool)` THEN
      ASM_MESON_TAC[PSUBSET];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "CARD")) (concl th))) THEN
      MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ih" (fun th -> MP_TAC(SPEC `fam1:(real^3->bool)->bool`
    (MP (SPEC `CARD (moi_s3lv_iness s2 i (fam1:(real^3->bool)->bool))` th)
        (ASSUME `CARD (moi_s3lv_iness s2 i (fam1:(real^3->bool)->bool)) < n`)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fam':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `fam':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 4: the polygons of the members on T.  Distinct even tori are       *)
(* disjoint; a member meets T only along whole boundary components, so the *)
(* components of its trace on T are boundary polygons (MOI_FSB_BD_CIRCLES), *)
(* finitely many; the inessential ones bound PL disks in T.                *)
(* ========================================================================= *)

let MOI_S3LV_COMP_SPLIT = prove
 (`!s t t':real^3->bool.
     closed t /\ closed t' /\ DISJOINT t t' /\ s SUBSET t UNION t'
     ==> components (s INTER t) SUBSET components s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `k:real^3->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(k:real^3->bool = {}) /\ connected k /\ k SUBSET s INTER t` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET];
         ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^3` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ABBREV_TAC `k' = connected_component (s:real^3->bool) x` THEN
  SUBGOAL_THEN `(k':real^3->bool) IN components s /\ x IN k'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k'" THEN REWRITE_TAC[components; IN_ELIM_THM] THEN
    CONJ_TAC THENL [EXISTS_TAC `x:real^3` THEN ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k':real^3->bool) SUBSET t` ASSUME_TAC THENL
   [SUBGOAL_THEN `connected(k':real^3->bool) /\ k' SUBSET s` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED] o
      check (fun th -> concl th = `connected(k':real^3->bool)`)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real^3->bool`; `t':real^3->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) = k'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `s INTER t:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `connected(k':real^3->bool) /\ k' SUBSET s` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    ASM SET_TAC[]]);;

let MOI_S3LV_TORI_DISJOINT = prove
 (`!(g:real^3->real^3) v pp dd s2 k k'.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ k + &2 <= k'
     ==> DISJOINT (IMAGE g (revolution (dd k))) (IMAGE g (revolution (dd k')))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_model; moi_s32_tower] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. revolution ((dd:int->real^3->bool) k) SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (revolution ((dd:int->real^3->bool) k)) (revolution (dd k'))` MP_TAC
  THENL
   [MATCH_MP_TAC MOI_S3LV_REV_DISJOINT THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!(g:real^3->real^3) s a b.
      (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\ a SUBSET s /\ b SUBSET s
      ==> DISJOINT a b ==> DISJOINT (IMAGE g a) (IMAGE g b)`) THEN
  EXISTS_TAC `moi_s32_cyl` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 5: the region R = interior (IMAGE g (revolution (dd (2i))))         *)
(* and the even torus T = frontier (s2 (2i)) at one level.  T lies in       *)
(* R, R lies in M = moi_s32_open g and misses the three axis points         *)
(* g qlo, g qhi, g 0; the other even tori miss the closure-side set         *)
(* IMAGE g (revolution (dd (2i))), so K meets it exactly in T; M is         *)
(* open and connected; T is a closed connected orientable combinatorial     *)
(* surface (TORUS_SETUP of pc_moi_s28_torus with its antecedents            *)
(* PL_SOLID_TORUS_BASIC, SURFACE_SIDES_ORIENTABLE_3 and SURF_LOCAL),        *)
(* locally the plane at each point.                                         *)
(* ========================================================================= *)

let MOI_S3LV_AXIS_OUT = prove
 (`!(g:real^3->real^3) v pp dd s2 q k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     q IN moi_s32_axis /\ q IN interior moi_s32_cyl
     ==> ~(g q IN IMAGE g (revolution (dd k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `&0:int`]
               MOI_S3LV_TOWER_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:int`) THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^3) = x` ASSUME_TAC THENL
   [UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                       ==> x = y` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      UNDISCH_TAC `!k. revolution ((dd:int->real^3->bool) k) SUBSET moi_s32_cyl` THEN
      DISCH_THEN(MP_TAC o SPEC `k:int`) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN
  UNDISCH_TAC `revolution ((dd:int->real^3->bool) k) SUBSET v` THEN
  UNDISCH_TAC `(x:real^3) IN revolution ((dd:int->real^3->bool) k)` THEN
  UNDISCH_TAC `(q:real^3) IN moi_s32_axis` THEN UNDISCH_TAC `(q:real^3) = x` THEN
  SET_TAC[]);;

let MOI_S3LV_R_FACTS = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> pl_solid_torus (s2 (&2 * i)) /\ compact (frontier (s2 (&2 * i))) /\
         frontier (s2 (&2 * i)) SUBSET interior (IMAGE g (revolution (dd (&2 * i)))) /\
         interior (IMAGE g (revolution (dd (&2 * i)))) SUBSET moi_s32_open g /\
         ~(g moi_s32_qlo IN IMAGE g (revolution (dd (&2 * i)))) /\
         ~(g moi_s32_qhi IN IMAGE g (revolution (dd (&2 * i)))) /\
         ~(g (vec 0) IN IMAGE g (revolution (dd (&2 * i)))) /\
         (!k. ~(k = i)
              ==> DISJOINT (frontier (s2 (&2 * k))) (IMAGE g (revolution (dd (&2 * i))))) /\
         moi_s32_evens s2 INTER IMAGE g (revolution (dd (&2 * i))) =
         frontier (s2 (&2 * i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
               MOI_S3LV_TOWER_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "tt") THEN
  STRIP_ASSUME_TAC MOI_S3GF_MODEL_POINTS THEN
  SUBGOAL_THEN `compact((s2:int->real^3->bool) (&2 * i))` ASSUME_TAC THENL
   [USE_THEN "tt" (MP_TAC o SPEC `&2 * i:int`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier((s2:int->real^3->bool) (&2 * i)) SUBSET
    interior (IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(s2:int->real^3->bool) (&2 * i)` THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ~(k = i)
        ==> DISJOINT (frontier ((s2:int->real^3->bool) (&2 * k)))
                     (IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i))))`
  (LABEL_TAC "oth") THENL
   [X_GEN_TAC `k:int` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!a b c:real^3->bool. a SUBSET b /\ DISJOINT b c ==> DISJOINT a c`) THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * k)))` THEN
    CONJ_TAC THENL
     [USE_THEN "tt" (MP_TAC o SPEC `&2 * k:int`) THEN SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * k + &2 <= &2 * i \/ &2 * i + &2 <= &2 * k:int` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(k:int = i)` THEN INT_ARITH_TAC;
      MATCH_MP_TAC MOI_S3LV_TORI_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN MATCH_MP_TAC MOI_S3LV_TORI_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_FRONTIER] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s32_open] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3LV_AXIS_OUT THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3LV_AXIS_OUT THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3LV_AXIS_OUT THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s32_evens; EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`tt:real^3->bool`; `k:int`] THEN STRIP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN tt` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `k:int = i` THENL
       [UNDISCH_TAC `(y:real^3) IN frontier((s2:int->real^3->bool) (&2 * k))` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "oth" (MP_TAC o C MP (ASSUME `~(k:int = i)`) o SPEC `k:int`) THEN
      UNDISCH_TAC `(y:real^3) IN frontier((s2:int->real^3->bool) (&2 * k))` THEN
      UNDISCH_TAC `(y:real^3) IN
                   IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))` THEN
      SET_TAC[];
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `frontier((s2:int->real^3->bool) (&2 * i))` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `i:int` THEN REWRITE_TAC[];
        MP_TAC(ISPEC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))`
          INTERIOR_SUBSET) THEN
        UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET
                     interior (IMAGE (g:real^3->real^3)
                                (revolution ((dd:int->real^3->bool) (&2 * i))))` THEN
        UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i))` THEN
        SET_TAC[]]]]);;

let MOI_S3LV_M_FACTS = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v ==> open (moi_s32_open g) /\ connected (moi_s32_open g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
    MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC STARLIKE_IMP_CONNECTED THEN REWRITE_TAC[starlike] THEN
  EXISTS_TAC `vec 0:real^3` THEN REWRITE_TAC[MOI_S3GF_MODEL_POINTS] THEN
  X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[MOI_S3GF_INTERIOR_CYL; IN_ELIM_THM; SUBSET; IN_SEGMENT] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN `!c a:real. &0 <= a /\ c <= &1 ==> c * a <= a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(x:real^3)$1 pow 2 + x$3 pow 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_ADD_LDISTRIB] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs((x:real^3)$2)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs u = u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_POS]]);;

let MOI_S3LV_T_SURFACE = prove
 (`!s:real^3->bool.
     pl_solid_torus s
     ==> ?t. FINITE t /\ combinatorial_manifold 2 t /\ UNIONS t = frontier s /\
             connected (frontier s) /\ orientable_surface_complex t /\
             (!y. y IN frontier s ==> moi_s28_locally_r2 (frontier s) y)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MP TORUS_SETUP (CONJ (INST_TYPE [`:3`,`:N`] PL_SOLID_TORUS_BASIC)
                              (CONJ SURFACE_SIDES_ORIENTABLE_3
                                    (INST_TYPE [`:3`,`:N`] SURF_LOCAL)))) THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:(real^3->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `y:real^3`] MOI_S8TA_CM_ALL_R2) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 6: the trace polygons on T.  A member c of a state with              *)
(* triangulation cc meets K only in its boundary, which lies on the two     *)
(* even tori of its level; these are disjoint closed sets, so the           *)
(* components of c INTER T are boundary circles of cc (MOI_FSB_BD_CIRCLES,  *)
(* pc_moi_fnd_surfb0): finitely many PL 1-spheres.  The trace polygons of   *)
(* the state (moi_s3lv_tr) are finitely many and pairwise disjoint; the     *)
(* inessential ones bound PL disks in T.                                    *)
(* ========================================================================= *)

let moi_s3lv_tr = new_definition
 `moi_s3lv_tr (s2:int->real^3->bool) (i:int) (fam:(real^3->bool)->bool) =
    {jj | ?c. c IN fam /\ jj IN components (c INTER frontier (s2 (&2 * i)))}`;;

let MOI_S3LV_TORI_FRONTIERS = prove
 (`!(g:real^3->real^3) v pp dd s2 i k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ ~(k = i)
     ==> DISJOINT (frontier (s2 (&2 * k))) (frontier (s2 (&2 * i))) /\
         closed (frontier (s2 (&2 * i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_R_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:int` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))`
    INTERIOR_SUBSET) THEN
  UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET
               interior (IMAGE (g:real^3->real^3)
                          (revolution ((dd:int->real^3->bool) (&2 * i))))` THEN
  SET_TAC[]);;

let MOI_S3LV_TRACE = prove
 (`!(g:real^3->real^3) v pp dd s2 i i' (c:real^3->bool) (cc:(real^3->bool)->bool).
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ UNIONS cc = c /\
     surface_boundary cc = c INTER moi_s32_evens s2 /\
     c INTER moi_s32_evens s2 SUBSET
       frontier (s2 (&2 * i')) UNION frontier (s2 (&2 * i' + &2))
     ==> components (c INTER frontier (s2 (&2 * i))) SUBSET
         components (surface_boundary cc) /\
         FINITE (components (c INTER frontier (s2 (&2 * i)))) /\
         (!jj. jj IN components (c INTER frontier (s2 (&2 * i)))
               ==> pl_sphere 1 jj /\ jj SUBSET c /\ jj SUBSET frontier (s2 (&2 * i)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "model") (CONJUNCTS_THEN2 (LABEL_TAC "tower")
    (CONJUNCTS_THEN2 (LABEL_TAC "fin") (CONJUNCTS_THEN2 (LABEL_TAC "cm")
    (CONJUNCTS_THEN2 (LABEL_TAC "un") (CONJUNCTS_THEN2 (LABEL_TAC "sb") (LABEL_TAC "lev"))))))) THEN
  MP_TAC(ISPEC `cc:(real^3->bool)->bool` MOI_FSB_BD_CIRCLES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bfin") (LABEL_TAC "bsph")) THEN
  SUBGOAL_THEN `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s32_evens; SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `frontier((s2:int->real^3->bool) (&2 * i))` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:int` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i)) =
    surface_boundary cc INTER frontier (s2 (&2 * i))`
  (LABEL_TAC "ct") THENL
   [USE_THEN "sb" SUBST1_TAC THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (frontier ((s2:int->real^3->bool) (&2 * i'))) /\
    closed (frontier (s2 (&2 * (i' + &1)))) /\
    DISJOINT (frontier (s2 (&2 * i'))) (frontier (s2 (&2 * (i' + &1)))) /\
    surface_boundary cc SUBSET frontier (s2 (&2 * i')) UNION frontier (s2 (&2 * (i' + &1)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i':int`; `i' + &1:int`]
                 MOI_S3LV_TORI_FRONTIERS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i' + &1:int`; `i':int`]
                 MOI_S3LV_TORI_FRONTIERS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "sb" SUBST1_TAC THEN
    USE_THEN "lev" MP_TAC THEN
    REWRITE_TAC[INT_ARITH `&2 * i' + &2 = &2 * (i' + &1):int`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `components (surface_boundary cc INTER frontier ((s2:int->real^3->bool) (&2 * i))) SUBSET
    components (surface_boundary cc)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `i:int = i'` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_S3LV_COMP_SPLIT THEN
      EXISTS_TAC `frontier ((s2:int->real^3->bool) (&2 * (i' + &1)))` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `i:int = i' + &1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_S3LV_COMP_SPLIT THEN
      EXISTS_TAC `frontier ((s2:int->real^3->bool) (&2 * i'))` THEN
      ONCE_REWRITE_TAC[UNION_COMM] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `surface_boundary cc INTER frontier ((s2:int->real^3->bool) (&2 * i)) = {}`
    SUBST1_TAC THENL
     [MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                    `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i':int`]
                   MOI_S3LV_TORI_FRONTIERS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                    `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i' + &1:int`]
                   MOI_S3LV_TORI_FRONTIERS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; STRIP_TAC] THEN
      UNDISCH_TAC `surface_boundary cc SUBSET
                   frontier ((s2:int->real^3->bool) (&2 * i')) UNION
                   frontier (s2 (&2 * (i' + &1)))` THEN
      UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i')))
                            (frontier (s2 (&2 * i)))` THEN
      UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * (i' + &1))))
                            (frontier (s2 (&2 * i)))` THEN
      SET_TAC[];
      REWRITE_TAC[COMPONENTS_EMPTY; EMPTY_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `components ((c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))) SUBSET
    components (surface_boundary cc)`
  (LABEL_TAC "sub") THENL
   [USE_THEN "ct" SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "sub" ACCEPT_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components (surface_boundary (cc:(real^3->bool)->bool))` THEN
    CONJ_TAC THENL [USE_THEN "bfin" ACCEPT_TAC; USE_THEN "sub" ACCEPT_TAC];
    X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(jj:real^3->bool) IN components (surface_boundary cc)` ASSUME_TAC THENL
     [USE_THEN "sub" (MP_TAC o REWRITE_RULE[SUBSET]) THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(jj:real^3->bool) SUBSET
                  (c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "bsph" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(jj:real^3->bool) SUBSET
                   (c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      SET_TAC[]]]);;

(* ========================================================================= *)
(* Part 7: bookkeeping of the trace polygons.  Each member's traces         *)
(* are finitely many PL 1-spheres; the trace polygons of the state on T are *)
(* finitely many (only members meeting the 2i-th revolved image count) and  *)
(* pairwise disjoint, and they cover the trace of every member; an          *)
(* inessential one bounds a PL disk in T.                                   *)
(* ========================================================================= *)

let MOI_S3LV_MEMBER_TRACE = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i (c:real^3->bool).
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ c IN fam
     ==> FINITE (components (c INTER frontier (s2 (&2 * i)))) /\
         (!jj. jj IN components (c INTER frontier (s2 (&2 * i)))
               ==> pl_sphere 1 jj /\ jj SUBSET c /\ jj SUBSET frontier (s2 (&2 * i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s32_state]) THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i':int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i':int`;
                `c:real^3->bool`; `cc:(real^3->bool)->bool`] MOI_S3LV_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]);;

let MOI_S3LV_TR_FINITE = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ moi_s32_state g dd s2 lev fam
     ==> FINITE (moi_s3lv_tr s2 i fam)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\c:real^3->bool. components (c INTER frontier
                                      ((s2:int->real^3->bool) (&2 * i))))
                  {c | c IN fam /\
                       ~(DISJOINT c (IMAGE (g:real^3->real^3)
                                       (revolution ((dd:int->real^3->bool) (&2 * i)))))})` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                  `fam:(real^3->bool)->bool`; `i:int`] MOI_S3LV_TOUCH_FINITE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `c:real^3->bool` THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                  `fam:(real^3->bool)->bool`; `i:int`; `c:real^3->bool`]
                 MOI_S3LV_MEMBER_TRACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[SUBSET; moi_s3lv_tr; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `jj:real^3->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_R_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`(c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                   `jj:real^3->bool`] IN_COMPONENTS_NONEMPTY) THEN
    MP_TAC(ISPECL [`(c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                   `jj:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))`
      INTERIOR_SUBSET) THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET
                 interior (IMAGE (g:real^3->real^3)
                            (revolution ((dd:int->real^3->bool) (&2 * i))))` THEN
    SET_TAC[]]);;

let MOI_S3LV_INESS_TR = prove
 (`!(s2:int->real^3->bool) i fam. moi_s3lv_iness s2 i fam SUBSET moi_s3lv_tr s2 i fam`,
  REWRITE_TAC[moi_s3lv_iness; moi_s3lv_tr; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S3LV_INESS_FINITE = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ moi_s32_state g dd s2 lev fam
     ==> FINITE (moi_s3lv_iness s2 i fam)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `moi_s3lv_tr s2 i (fam:(real^3->bool)->bool)` THEN
  REWRITE_TAC[MOI_S3LV_INESS_TR] THEN MATCH_MP_TAC MOI_S3LV_TR_FINITE THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                        `dd:int->real^3->bool`; `lev:int->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3LV_INESS_DISK = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i jj.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ jj IN moi_s3lv_iness s2 i fam
     ==> (?c. c IN fam /\ jj IN components (c INTER frontier (s2 (&2 * i)))) /\
         pl_sphere 1 jj /\ jj SUBSET frontier (s2 (&2 * i)) /\
         ?d. d SUBSET frontier (s2 (&2 * i)) /\ pl_cell_with_boundary 2 d jj`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(jj:real^3->bool) IN moi_s3lv_iness s2 i fam` THEN
  REWRITE_TAC[moi_s3lv_iness; IN_ELIM_THM; moi_s32_ess] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`; `c:real^3->bool`]
               MOI_S3LV_MEMBER_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `jj:real^3->bool` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_S3LV_TR_DISJOINT = prove
 (`!(s2:int->real^3->bool) i fam jj jj'.
     pairwise DISJOINT fam /\
     jj IN moi_s3lv_tr s2 i fam /\ jj' IN moi_s3lv_tr s2 i fam /\ ~(jj = jj')
     ==> DISJOINT jj jj'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3lv_tr; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c':real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  ASM_CASES_TAC `c:real^3->bool = c'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[DISJOINT] THEN
    MP_TAC(ISPECL [`(c':real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                   `jj:real^3->bool`; `jj':real^3->bool`] COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                 `jj:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
  MP_TAC(ISPECL [`(c':real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                 `jj':real^3->bool`] IN_COMPONENTS_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
  REWRITE_TAC[pairwise] THEN DISCH_THEN(MP_TAC o SPECL [`c:real^3->bool`; `c':real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S3LV_TR_COVER = prove
 (`!(s2:int->real^3->bool) i fam (c:real^3->bool) x.
     c IN fam /\ x IN c /\ x IN frontier (s2 (&2 * i))
     ==> ?jj. jj IN moi_s3lv_tr s2 i fam /\ jj IN components (c INTER frontier (s2 (&2 * i))) /\
              x IN jj`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`
    UNIONS_COMPONENTS) THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `jj:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_s3lv_tr; IN_ELIM_THM] THEN
  EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 8: PL disks.  The face complex of a 2-simplex is a                 *)
(* combinatorial disk with boundary its relative frontier; hence (by       *)
(* SURF_INVARIANT) every triangulation of a PL 2-cell is a combinatorial   *)
(* surface with boundary the boundary of the cell; interior points of a    *)
(* cell are locally the plane in it, boundary points are not.  In a set    *)
(* that is locally the plane at the interior points of a cell, the cell   *)
(* minus its boundary is open (invariance of domain, MOI_S8CU_IOD), and no *)
(* neighbourhood of a boundary point lies in the cell.  A disk with an     *)
(* annulus glued along one end is a disk (MOI_S3LV_DISK_ANN).              *)
(* ========================================================================= *)

(* The statement and proof of MOI_FRB_FACE_COMPLEX_CMWB2 of                  *)
(* pc_moi_fnd_rnb2.ml, repeated here to keep the load closure small.         *)

let MOI_S3LV_FACE_COMPLEX_CMWB2 = prove
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

let MOI_S3LV_FACE_SB = prove
 (`!k:real^N->bool.
     &2 simplex k ==> surface_boundary {f | f face_of k} = relative_frontier k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `polytope (k:real^N->bool) /\ convex k /\ aff_dim k = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
  REWRITE_TAC[surface_boundary; facet_of; IN_ELIM_THM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_CASES_TAC `(s:real^N->bool) face_of k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `aff_dim(s:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{r:real^N->bool | r face_of k /\ aff_dim r = &2 /\ s SUBSET r} = {k}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_CASES_TAC `r:real^N->bool = k` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `k:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    ASM_REWRITE_TAC[CARD_SING]]);;

let MOI_S3LV_SURF_INV = prove
 (inst [`:N`,`:M`] MOI_S28_SURF_INVARIANT_BODY,
  ACCEPT_TAC(INST_TYPE [`:N`,`:M`]
    (MP SURF_INVARIANT (CONJ (INST_TYPE [`:M`,`:N`] SURF_CHARTS) SURF_LOCAL))));;

let MOI_S3LV_DISK_COMPLEX = prove
 (`!(d:real^N->bool) b.
     pl_cell_with_boundary 2 d b
     ==> ?t. FINITE t /\ simplicial_complex t /\
             combinatorial_manifold_with_boundary 2 t /\
             UNIONS t = d /\ surface_boundary t = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^N->bool)` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN
  MP_TAC(ISPECL [`&2:int`; `k:real^N->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`{s:real^N->bool | s face_of k}`; `t:(real^N->bool)->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_S3LV_SURF_INV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S3LV_FACE_COMPLEX_CMWB2] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[simplicial_complex]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3LV_FACE_SB] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex]);;

let MOI_S3LV_DISK_CHARTS = prove
 (`!(d:real^N->bool) b.
     pl_cell_with_boundary 2 d b
     ==> compact d /\ compact b /\ b SUBSET d /\ pl_polyhedron d /\ connected d /\
         (!y. y IN d DIFF b ==> moi_s28_locally_r2 d y) /\
         (!y. y IN b ==> ~moi_s28_locally_r2 d y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_CEL_CELL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S3LV_DISK_COMPLEX) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` SURF_CHARTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^N->bool) b` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
    STRIP_TAC THEN UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S3LV_DISK_OPEN = prove
 (`!(x:real^N->bool) d b.
     pl_cell_with_boundary 2 d b /\ d SUBSET x /\
     (!y. y IN d DIFF b ==> moi_s28_locally_r2 x y)
     ==> open_in (subtopology euclidean x) (d DIFF b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2"))) THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `f':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `homeomorphism (k0,d) ((f:real^N->real^N) o (h:real^2->real^N),
                          (h':real^N->real^2) o (f':real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (k0,k) (h:real^2->real^N,h')` THEN
      SIMP_TAC[pl_homeomorphism];
      UNDISCH_TAC `pl_homeomorphism (k,d) (f:real^N->real^N,f')` THEN
      SIMP_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  ABBREV_TAC `G = (f:real^N->real^N) o (h:real^2->real^N)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (k0,d) ((G:real^2->real^N),
                                      (h':real^N->real^2) o (f':real^N->real^N))`)) THEN
  SUBGOAL_THEN `compact (k0:real^2->bool) /\ ~(interior k0 = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    MP_TAC(ISPEC `k0:real^2->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    REWRITE_TAC[DIMINDEX_2] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (k0:real^2->bool) = k0 DIFF interior k0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `b = IMAGE (G:real^2->real^N) (k0 DIFF interior k0)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `IMAGE (h:real^2->real^N) (relative_frontier k0) = relative_frontier k` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF b = IMAGE (G:real^2->real^N) (interior k0)` SUBST1_TAC THENL
   [UNDISCH_TAC `b = IMAGE (G:real^2->real^N) (k0 DIFF interior k0)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `!x. x IN k0
                     ==> ((h':real^N->real^2) o (f':real^N->real^N)) ((G:real^2->real^N) x) = x` THEN
    UNDISCH_TAC `IMAGE (G:real^2->real^N) k0 = d` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8CU_IOD THEN REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET];
    MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `!x. x IN k0
                     ==> ((h':real^N->real^2) o (f':real^N->real^N)) ((G:real^2->real^N) x) = x` THEN
    SET_TAC[];
    MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `IMAGE (G:real^2->real^N) k0 = d` THEN
    UNDISCH_TAC `(d:real^N->bool) SUBSET x` THEN SET_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN
    DISJ1_TAC THEN USE_THEN "r2" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN IMAGE (G:real^2->real^N) (interior k0)` THEN
    MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `!x. x IN k0
                     ==> ((h':real^N->real^2) o (f':real^N->real^N)) ((G:real^2->real^N) x) = x` THEN
    UNDISCH_TAC `IMAGE (G:real^2->real^N) k0 = d` THEN
    UNDISCH_TAC `b = IMAGE (G:real^2->real^N) (k0 DIFF interior k0)` THEN SET_TAC[]]);;

let MOI_S3LV_DISK_BD = prove
 (`!(x:real^N->bool) d b y u.
     pl_cell_with_boundary 2 d b /\ d SUBSET x /\ moi_s28_locally_r2 x y /\ y IN b /\
     open_in (subtopology euclidean x) u /\ y IN u
     ==> ~(u SUBSET d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LV_DISK_CHARTS) THEN
  SUBGOAL_THEN `moi_s28_locally_r2 (d:real^N->bool) y` MP_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`x:real^N->bool`; `u:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Part 9: a disk with an annulus glued along one end is a disk (the        *)
(* statement of MOI_S5C_DISK_ANN of pc_moi_s35_minc.ml, proved here to keep *)
(* the load closure small).  Route: the square Q1 is a PL cell with         *)
(* boundary its relative frontier (PL ball and invariance of the frontier); *)
(* extend the inner end of the annulus over Q1 (MOI_CEL_CELL_EXTENSION),    *)
(* glue (MOI_PL2_PL_HOMEOMORPHISM_UNION) to a PL homeomorphism of Q2 = Q1   *)
(* UNION ann, and read off the cell through the translated model square     *)
(* (SQUARE_CELL of pc_moi_s28_plane).                                       *)
(* ========================================================================= *)

let MOI_S3LV_BALL2_CELL = prove
 (`!s:real^2->bool.
     pl_ball 2 s /\ closed s /\ ~(interior s = {})
     ==> pl_cell_with_boundary 2 s (relative_frontier s)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(interior (k:real^2->bool) = {}) /\ compact k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `k:real^2->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
      REWRITE_TAC[DIMINDEX_2] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOI_FPS_HOMEOMORPHISM_FRONTIER THEN EXISTS_TAC `g:real^2->real^2` THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  UNDISCH_TAC `pl_homeomorphism (k,s) (f:real^2->real^2,g)` THEN
  SIMP_TAC[pl_homeomorphism]);;

let MOI_S3LV_Q1_CELL = prove
 (`pl_cell_with_boundary 2 (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
     (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  MATCH_MP_TAC MOI_S3LV_BALL2_CELL THEN
  REWRITE_TAC[CLOSED_INTERVAL; GSYM MOI_FPS_VEC1_2; MOI_S8PL_SQUARE_BALL] THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
              VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S3LV_TRANSLATE_PLH = prove
 (`!(s:real^N->bool) a.
     locally_polyhedral s
     ==> pl_homeomorphism (s,IMAGE (\x. a + x) s) ((\x. a + x),(\x. --a + x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE; GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[VECTOR_ARITH `--a + a + x:real^N = x`;
                VECTOR_ARITH `a + --a + a + x:real^N = a + x`; IMAGE_ID] THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^N. (\y:real^N. y) x + a` THEN
    CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
                    ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_ID]]);;

let MOI_S3LV_Q2_MODEL = prove
 (`pl_homeomorphism (holed_disk_model 0,interval[--vector[&2;&2]:real^2,vector[&2;&2]])
     ((\x. --vector[&2;&2] + x),(\x. --(--vector[&2;&2]) + x)) /\
   IMAGE (\x:real^2. --vector[&2;&2] + x) (frontier (holed_disk_model 0)) =
   relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])`,
  SUBGOAL_THEN `interval[--vector[&2;&2]:real^2,vector[&2;&2]] =
                IMAGE (\x:real^2. --vector[&2;&2] + x) (holed_disk_model 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOI_FD_HOLED_DISK_MODEL_0; GSYM(CONJUNCT1 INTERVAL_TRANSLATION);
                VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `--vector[&2;&2] + vector[&4;&4] = vector[&2;&2]:real^2` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_NEG_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_TRANSLATE_PLH THEN
    REWRITE_TAC[MOI_FD_HOLED_DISK_MODEL_0] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN REWRITE_TAC[POLYTOPE_INTERVAL];
    REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[MOI_FD_HOLED_DISK_MODEL_0; INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY;
                DIMINDEX_2; FORALL_2; VEC_COMPONENT; VECTOR_2] THEN
    REAL_ARITH_TAC]);;

let MOI_S3LV_ANN_MODEL = prove
 (`interval[--vector[&1;&1]:real^2,vector[&1;&1]] INTER moi_fps_ann =
   relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
   interval[--vector[&1;&1]:real^2,vector[&1;&1]] UNION moi_fps_ann =
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] /\
   relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET moi_fps_ann /\
   relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET moi_fps_ann /\
   DISJOINT (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))
            (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  REWRITE_TAC[EXTENSION; SUBSET; DISJOINT; IN_INTER; IN_UNION; MOI_FPS_ANN; MOI_S8PL_RF12;
              IN_ELIM_THM; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3LV_DISK_ANN = prove
 (`!(d0:real^N->bool) j0 a j1.
     pl_cell_with_boundary 2 d0 j0 /\ pl_annulus_with_ends a j0 j1 /\ d0 INTER a = j0
     ==> pl_cell_with_boundary 2 (d0 UNION a) j1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "d0") (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "da"))) THEN
  REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "fa") (CONJUNCTS_THEN2 (LABEL_TAC "j0") (LABEL_TAC "j1"))))) THEN
  STRIP_ASSUME_TAC MOI_S3LV_ANN_MODEL THEN
  SUBGOAL_THEN `compact (a:real^N->bool)` ASSUME_TAC THENL
   [USE_THEN "fa" (STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      REWRITE_RULE[pl_homeomorphism]) THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S8PL_ANN_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (d0:real^N->bool)` ASSUME_TAC THENL
   [USE_THEN "d0" (MP_TAC o MATCH_MP MOI_CEL_CELL_COMPACT) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]),j0)
                     (f:real^2->real^N,g)`
  ASSUME_TAC THENL
   [USE_THEN "j0" SUBST1_TAC THEN MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_fps_ann`; `a:real^N->bool`] THEN
    CONJ_TAC THENL [USE_THEN "fa" ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER THEN REWRITE_TAC[POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `interval[--vector[&1;&1]:real^2,vector[&1;&1]]`;
                 `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;
                 `d0:real^N->bool`; `j0:real^N->bool`; `f:real^2->real^N`;
                 `g:real^N->real^2`] MOI_CEL_CELL_EXTENSION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_S3LV_Q1_CELL] THEN CONJ_TAC THENL
     [USE_THEN "d0" ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F1:real^2->real^N` (X_CHOOSE_THEN `G1:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`interval[--vector[&1;&1]:real^2,vector[&1;&1]]`; `moi_fps_ann`;
                 `d0:real^N->bool`; `a:real^N->bool`;
                 `F1:real^2->real^N`; `G1:real^N->real^2`; `f:real^2->real^N`;
                 `g:real^N->real^2`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_INTERVAL; MOI_S8PL_ANN_CLOSED; COMPACT_IMP_CLOSED] THEN
    MATCH_MP_TAC(SET_RULE
     `!(ff:real^2->real^N) f s. (!x. x IN s ==> ff x = f x) ==> IMAGE ff s = IMAGE f s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`d0 UNION a:real^N->bool`;
                 `(\x. if x IN interval[--vector[&1;&1]:real^2,vector[&1;&1]]
                       then (F1:real^2->real^N) x else f x) o
                  (\x:real^2. --vector[&2;&2] + x)`;
                 `(\x:real^2. --(--vector[&2;&2]) + x) o
                  (\y. if y IN d0 then (G1:real^N->real^2) y else g y)`] SQUARE_CELL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[--vector[&2;&2]:real^2,vector[&2;&2]]` THEN
    ASM_REWRITE_TAC[MOI_S3LV_Q2_MODEL];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMAGE_o; MOI_S3LV_Q2_MODEL] THEN USE_THEN "j1" SUBST1_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!(ff:real^2->real^N) f s t. DISJOINT s t
         ==> IMAGE (\x. if x IN t then ff x else f x) s = IMAGE f s`) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* Part 10: an inmost inessential polygon (Moise p.226).  In a set x        *)
(* that is locally the plane everywhere, a connected set missing the       *)
(* boundary of a PL disk d inside x and meeting d lies in d; a polygon     *)
(* inside d and off its boundary bounds a smaller disk (DISK_POLYGON) not  *)
(* containing the boundary of d (invariance of domain).  Minimizing the    *)
(* number of trace polygons inside the disk of an inessential polygon J    *)
(* gives a disk D with boundary J in T meeting the members only in J.      *)
(* ========================================================================= *)

let MOI_S3LV_CONNECTED_SPLIT = prove
 (`!(x:real^N->bool) u v s.
     open_in (subtopology euclidean x) u /\ open_in (subtopology euclidean x) v /\
     DISJOINT u v /\ connected s /\ s SUBSET u UNION v
     ==> s SUBSET u \/ s SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `V:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3LV_CONNECTED_IN_DISK = prove
 (`!(x:real^N->bool) d b s.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     pl_cell_with_boundary 2 d b /\ d SUBSET x /\
     connected s /\ s SUBSET x /\ DISJOINT s b /\ ~(DISJOINT s d)
     ==> s SUBSET d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LV_DISK_CHARTS) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `d DIFF b:real^N->bool`; `x DIFF d:real^N->bool`;
                 `s:real^N->bool`] MOI_S3LV_CONNECTED_SPLIT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3LV_DISK_OPEN THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(d:real^N->bool) SUBSET x` THEN
      UNDISCH_TAC `!y:real^N. y IN x ==> moi_s28_locally_r2 x y` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(s:real^N->bool) SUBSET x` THEN
      UNDISCH_TAC `DISJOINT (s:real^N->bool) b` THEN SET_TAC[]];
    UNDISCH_TAC `~DISJOINT (s:real^N->bool) d` THEN SET_TAC[]]);;

let MOI_S3LV_INNER_DISK = prove
 (`!(x:real^N->bool) d b j.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     pl_cell_with_boundary 2 d b /\ d SUBSET x /\ ~(b = {}) /\
     pl_sphere 1 j /\ j SUBSET d /\ DISJOINT j b
     ==> ?d'. d' SUBSET d /\ pl_cell_with_boundary 2 d' j /\ ~(b SUBSET d')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `b:real^N->bool`; `j:real^N->bool`] DISK_POLYGON) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s28_bounds_disk] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d':real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(b:real^N->bool = {})`)) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `d:real^N->bool`; `b:real^N->bool`; `y:real^N`;
                 `d' DIFF j:real^N->bool`] MOI_S3LV_DISK_BD) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_S3LV_DISK_OPEN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(d':real^N->bool) SUBSET d` THEN UNDISCH_TAC `(d:real^N->bool) SUBSET x` THEN
    UNDISCH_TAC `!y:real^N. y IN x ==> moi_s28_locally_r2 x y` THEN SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3LV_INMOST = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ ~(moi_s3lv_iness s2 i fam = {})
     ==> ?J D C. C IN fam /\ J IN components (C INTER frontier (s2 (&2 * i))) /\
                 J IN moi_s3lv_iness s2 i fam /\
                 D SUBSET frontier (s2 (&2 * i)) /\ pl_cell_with_boundary 2 D J /\
                 (!c. c IN fam ==> c INTER D SUBSET J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_R_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `(s2:int->real^3->bool) (&2 * i)` MOI_S3LV_T_SURFACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`] MOI_S3LV_TR_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state (g:real^3->real^3) dd s2 lev fam` THEN
    SIMP_TAC[moi_s32_state];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?n J D. J IN moi_s3lv_iness s2 i fam /\
            D SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) /\
            pl_cell_with_boundary 2 D J /\
            CARD {jj | jj IN moi_s3lv_tr s2 i fam /\ jj SUBSET D} = n`
  MP_TAC THENL
   [UNDISCH_TAC `~(moi_s3lv_iness s2 i (fam:(real^3->bool)->bool) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `J:real^3->bool`) THEN
    MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                  `fam:(real^3->bool)->bool`; `i:int`; `J:real^3->bool`]
                 MOI_S3LV_INESS_DISK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `D:real^3->bool` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    MAP_EVERY EXISTS_TAC
     [`CARD {jj | jj IN moi_s3lv_tr s2 i fam /\ jj SUBSET (D:real^3->bool)}`;
      `J:real^3->bool`; `D:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `J:real^3->bool` (X_CHOOSE_THEN `D:real^3->bool` STRIP_ASSUME_TAC))
    (LABEL_TAC "min"))) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`; `J:real^3->bool`]
               MOI_S3LV_INESS_DISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `C:real^3->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`J:real^3->bool`; `D:real^3->bool`; `C:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(J:real^3->bool) IN moi_s3lv_tr s2 i fam` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3LV_INESS_TR; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (D:real^3->bool) /\ (J:real^3->bool) SUBSET D /\ ~(J = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT]; ALL_TAC] THEN
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_INTER] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s2:int->real^3->bool`; `i:int`; `fam:(real^3->bool)->bool`;
                `c:real^3->bool`; `x:real^3`] MOI_S3LV_TR_COVER) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `jj:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `jj:real^3->bool = J` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (jj:real^3->bool) J` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_TR_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`s2:int->real^3->bool`; `i:int`; `fam:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`; `c:real^3->bool`]
               MOI_S3LV_MEMBER_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `jj:real^3->bool` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(jj:real^3->bool) SUBSET D` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_CONNECTED_IN_DISK THEN
    MAP_EVERY EXISTS_TAC [`frontier((s2:int->real^3->bool) (&2 * i))`; `J:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier((s2:int->real^3->bool) (&2 * i))`; `D:real^3->bool`;
                 `J:real^3->bool`; `jj:real^3->bool`] MOI_S3LV_INNER_DISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D':real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "min" (MP_TAC o SPEC
    `CARD {jj' | jj' IN moi_s3lv_tr s2 i fam /\ jj' SUBSET (D':real^3->bool)}`) THEN
  MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> ~b) ==> c`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "n")) THEN
    MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        UNDISCH_TAC `(D':real^3->bool) SUBSET D` THEN SET_TAC[];
        MATCH_MP_TAC(SET_RULE `!a b (x:real^3->bool). x IN b /\ ~(x IN a) ==> ~(a = b)`) THEN
        EXISTS_TAC `J:real^3->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `moi_s3lv_tr s2 i (fam:(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    MAP_EVERY EXISTS_TAC [`jj:real^3->bool`; `D':real^3->bool`] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s3lv_iness; IN_ELIM_THM] THEN EXISTS_TAC `c:real^3->bool` THEN
      ASM_REWRITE_TAC[moi_s32_ess] THEN EXISTS_TAC `D':real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

(* ========================================================================= *)
(* Part 11: the outer side of a bicollared disk boundary.  For a PL         *)
(* disk d with boundary b in a set x that is locally the plane, and a       *)
(* bicollar p of b in x, the two open sides of the bicollar are connected   *)
(* and miss b, so each lies in d minus b or outside d; they cannot both lie *)
(* in d (no neighbourhood of a boundary point lies in d) nor both outside   *)
(* (b lies in the closure of d minus b).  The half bicollar on the outer    *)
(* side up to level 1/2 is an annulus (PRODUCT_ANNULUS); with d it gives a  *)
(* larger disk d2 containing d in its interior relative to x.              *)
(* ========================================================================= *)

let MOI_S3LV_SPHERE1_FACTS = prove
 (`!j:real^N->bool. pl_sphere 1 j ==> compact j /\ connected j`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `compact (k:real^N->bool) /\ convex k /\ aff_dim k = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) (relative_frontier k) = j` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    INT_ARITH_TAC]);;

let MOI_S3LV_DISK_CLOSURE = prove
 (`!(d:real^N->bool) b. pl_cell_with_boundary 2 d b ==> d SUBSET closure (d DIFF b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF b = IMAGE (f:real^N->real^N) (relative_interior k)` SUBST1_TAC THENL
   [UNDISCH_TAC `b = IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `!x. x IN k ==> (g:real^N->real^N) (f x) = x` THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
  SUBGOAL_THEN `k = closure (relative_interior (k:real^N->bool))`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED]);;

let MOI_S3LV_BICOLLAR_COMPACT = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q a c.
     moi_s26_bicollar m w p q /\ compact m /\ -- &1 <= a /\ c <= &1
     ==> compact (IMAGE p (m PCROSS {t:real^1 | a <= drop t /\ drop t <= c}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[MOI_S8CU_SLAB_INTERVAL] THEN
    REWRITE_TAC[COMPACT_INTERVAL]]);;

let MOI_S3LV_BICOLLAR_NBHD = prove
 (`!(x:real^N->bool) m w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q /\ compact m /\ w SUBSET x /\
     m SUBSET (subtopology euclidean x) interior_of w
     ==> ?V. open_in (subtopology euclidean x) V /\ m SUBSET V /\
             V SUBSET IMAGE p (m PCROSS {t:real^1 | --(&1 / &2) < drop t /\ drop t < &1 / &2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `K = IMAGE (p:real^(N,1)finite_sum->real^N)
          (m PCROSS ({t:real^1 | -- &1 <= drop t /\ drop t <= --(&1 / &2)} UNION
                     {t:real^1 | &1 / &2 <= drop t /\ drop t <= &1}))` THEN
  SUBGOAL_THEN `compact (K:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[PCROSS_UNION; IMAGE_UNION] THEN
    MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S3LV_BICOLLAR_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`w:real^N->bool`; `q:real^N->real^(N,1)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`;
                 `interval[--vec 1:real^1,vec 1]`;
                 `{t:real^1 | -- &1 <= drop t /\ drop t <= --(&1 / &2)} UNION
                  {t:real^1 | &1 / &2 <= drop t /\ drop t <= &1}`]
                MOI_S8CU_BICOLLAR_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`;
                 `{lift(&0)}`;
                 `{t:real^1 | -- &1 <= drop t /\ drop t <= --(&1 / &2)} UNION
                  {t:real^1 | &1 / &2 <= drop t /\ drop t <= &1}`]
                MOI_S8CU_BICOLLAR_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC; IN_SING] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; LIFT_DROP] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`] MOI_S8CU_BICOLLAR_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `IMAGE (p:real^(N,1)finite_sum->real^N)
                  (m PCROSS interval[--vec 1:real^1,vec 1]) = w` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s26_bicollar (m:real^N->bool) w p q` THEN
    SIMP_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  EXISTS_TAC `(subtopology euclidean x) interior_of (w:real^N->bool) DIFF K` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(subtopology euclidean x) interior_of (w:real^N->bool) DIFF K =
                  (subtopology euclidean x) interior_of w DIFF (x INTER K)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (x:real^N->bool)`; `w:real^N->bool`]
        INTERIOR_OF_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_INTERIOR_OF] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS {lift(&0)}) INTER K =
                 IMAGE p (m PCROSS ({lift(&0)} INTER
                   ({t:real^1 | -- &1 <= drop t /\ drop t <= --(&1 / &2)} UNION
                    {t:real^1 | &1 / &2 <= drop t /\ drop t <= &1})))` THEN
    SUBGOAL_THEN `{lift(&0)} INTER
                  ({t:real^1 | -- &1 <= drop t /\ drop t <= --(&1 / &2)} UNION
                   {t:real^1 | &1 / &2 <= drop t /\ drop t <= &1}) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY] THEN
      GEN_TAC THEN ASM_CASES_TAC `x' = lift(&0)` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(m:real^N->bool) SUBSET (subtopology euclidean x) interior_of w` THEN
    SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(w:real^N->bool) DIFF K` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (x:real^N->bool)`; `w:real^N->bool`]
        INTERIOR_OF_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (m PCROSS interval[--vec 1:real^1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM; IN_INTERVAL_1;
                DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Part 12: the outer disk d2.  One open side of the bicollar of the        *)
(* boundary b of the disk d lies outside d and the other in d minus b       *)
(* (MOI_S3LV_BICOLLAR_SIDES2); the half bicollar on the outer side up to    *)
(* level 1/2 is an annulus with ends b and the level 1/2 (PRODUCT_ANNULUS,  *)
(* swapped by MOI_S3LV_ANN_SYM on the negative side), so d2 = d UNION B is  *)
(* a disk (MOI_S3LV_DISK_ANN) containing d in its interior relative to x.   *)
(* ========================================================================= *)

let MOI_S3LV_ANN_SYM = prove
 (`!(a:real^N->bool) j0 j1. pl_annulus_with_ends a j0 j1 ==> pl_annulus_with_ends a j1 j0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  X_CHOOSE_THEN `sw:real^2->real^2` (X_CHOOSE_THEN `sw':real^2->real^2` STRIP_ASSUME_TAC)
    MOI_S8PL_ANN_SWAP THEN
  MAP_EVERY EXISTS_TAC [`(f:real^2->real^N) o (sw:real^2->real^2)`;
                        `(sw':real^2->real^2) o (g:real^N->real^2)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `moi_fps_ann` THEN ASM_REWRITE_TAC[]);;

let MOI_S3LV_BICOLLAR_SIDES2 = prove
 (`!(x:real^N->bool) d b w (p:real^(N,1)finite_sum->real^N) q.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     pl_cell_with_boundary 2 d b /\ d SUBSET x /\ pl_sphere 1 b /\ ~(b = {}) /\
     moi_s26_bicollar b w p q /\ w SUBSET x /\
     b SUBSET (subtopology euclidean x) interior_of w
     ==> (IMAGE p (b PCROSS {t | &0 < drop t /\ drop t < &1}) SUBSET x DIFF d /\
          IMAGE p (b PCROSS {t | --(&1) < drop t /\ drop t < &0}) SUBSET d DIFF b) \/
         (IMAGE p (b PCROSS {t | --(&1) < drop t /\ drop t < &0}) SUBSET x DIFF d /\
          IMAGE p (b PCROSS {t | &0 < drop t /\ drop t < &1}) SUBSET d DIFF b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LV_SPHERE1_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LV_DISK_CHARTS) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `b:real^N->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`]
                MOI_S3LV_BICOLLAR_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`] MOI_S8CU_BICOLLAR_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `&0`; `&1`] MOI_S8CU_SIDE_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `--(&1)`; `&0`] MOI_S8CU_SIDE_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^(N,1)finite_sum->real^N)
      (b PCROSS {t:real^1 | --(&1 / &2) < drop t /\ drop t < &1 / &2}) SUBSET
    IMAGE p (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `sp = IMAGE (p:real^(N,1)finite_sum->real^N)
                         (b PCROSS {t:real^1 | &0 < drop t /\ drop t < &1})` THEN
  ABBREV_TAC `sm = IMAGE (p:real^(N,1)finite_sum->real^N)
                         (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0})` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean x) (d DIFF b:real^N->bool) /\
                open_in (subtopology euclidean x) (x DIFF d:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3LV_DISK_OPEN THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(d:real^N->bool) SUBSET x` THEN
      UNDISCH_TAC `!y:real^N. y IN x ==> moi_s28_locally_r2 x y` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. connected s /\ s SUBSET x /\ s INTER b = {}
                                 ==> s SUBSET d DIFF b \/ s SUBSET x DIFF d`
  (LABEL_TAC "split") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3LV_CONNECTED_SPLIT THEN
    EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sp:real^N->bool) SUBSET x /\ (sm:real^N->bool) SUBSET x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N->bool) SUBSET x` THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) SUBSET w` THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) =
                 ((sm:real^N->bool) UNION b) UNION sp` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:real^N->bool) SUBSET sm UNION b UNION sp` ASSUME_TAC THENL
   [UNDISCH_TAC `(V:real^N->bool) SUBSET
                 IMAGE (p:real^(N,1)finite_sum->real^N)
                   (b PCROSS {t:real^1 | --(&1 / &2) < drop t /\ drop t < &1 / &2})` THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (b PCROSS {t:real^1 | --(&1 / &2) < drop t /\ drop t < &1 / &2}) SUBSET
                 IMAGE p (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1})` THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) =
                 ((sm:real^N->bool) UNION b) UNION sp` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. y IN b` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((sp:real^N->bool) SUBSET d DIFF b /\ (sm:real^N->bool) SUBSET d DIFF b)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^N->bool`; `d:real^N->bool`; `b:real^N->bool`; `y:real^N`;
                   `V:real^N->bool`] MOI_S3LV_DISK_BD) THEN
    REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((sp:real^N->bool) SUBSET x DIFF d /\ (sm:real^N->bool) SUBSET x DIFF d)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`d:real^N->bool`; `b:real^N->bool`] MOI_S3LV_DISK_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `open_in (subtopology euclidean x) (V:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `d DIFF b:real^N->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((U:real^N->bool) INTER closure (d DIFF b) = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "split" (MP_TAC o SPEC `sp:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "split" (MP_TAC o SPEC `sm:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_S3LV_OUTER_FROM_ANN = prove
 (`!(x:real^N->bool) d b bb b2 V.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     pl_cell_with_boundary 2 d b /\ d SUBSET x /\
     pl_annulus_with_ends bb b b2 /\ d INTER bb = b /\
     open_in (subtopology euclidean x) V /\ b SUBSET V /\ V SUBSET d UNION bb
     ==> pl_cell_with_boundary 2 (d UNION bb) b2 /\
         d SUBSET (subtopology euclidean x) interior_of (d UNION bb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_DISK_ANN THEN EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(d DIFF b) UNION (V:real^N->bool)` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3LV_DISK_OPEN THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(d:real^N->bool) SUBSET x` THEN
  UNDISCH_TAC `!y:real^N. y IN x ==> moi_s28_locally_r2 x y` THEN SET_TAC[]);;

let MOI_S3LV_OUTER_DISK = prove
 (`!(x:real^N->bool) d b w (p:real^(N,1)finite_sum->real^N) q.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     pl_cell_with_boundary 2 d b /\ d SUBSET x /\ pl_sphere 1 b /\ ~(b = {}) /\
     moi_s26_bicollar b w p q /\ w SUBSET x /\
     b SUBSET (subtopology euclidean x) interior_of w
     ==> ?d2 b2. pl_cell_with_boundary 2 d2 b2 /\ d SUBSET d2 /\ d2 SUBSET d UNION w /\
                 DISJOINT b2 d /\ d SUBSET (subtopology euclidean x) interior_of d2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LV_SPHERE1_FACTS) THEN
  SUBGOAL_THEN `(b:real^N->bool) SUBSET d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `d:real^N->bool`; `b:real^N->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`]
                MOI_S3LV_BICOLLAR_SIDES2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `b:real^N->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`]
                MOI_S3LV_BICOLLAR_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`] MOI_S8CU_BICOLLAR_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `IMAGE (p:real^(N,1)finite_sum->real^N)
                  (b PCROSS interval[--vec 1:real^1,vec 1]) = w` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s26_bicollar (b:real^N->bool) w p q` THEN
    SIMP_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!S. S SUBSET interval[--vec 1:real^1,vec 1]
        ==> IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS S) SUBSET w`
  (LABEL_TAC "inw") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (b PCROSS interval[--vec 1:real^1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`b:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`; `&0`; `&1 / &2`] PRODUCT_ANNULUS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s26_level] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N->bool`; `d:real^N->bool`; `b:real^N->bool`;
                   `IMAGE (p:real^(N,1)finite_sum->real^N)
                      (b PCROSS {x:real^1 | &0 <= drop x /\ drop x <= &1 / &2})`;
                   `IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(&1 / &2)})`;
                   `V:real^N->bool`] MOI_S3LV_OUTER_FROM_ANN) THEN
    SUBGOAL_THEN
     `IMAGE (p:real^(N,1)finite_sum->real^N)
        (b PCROSS {x:real^1 | &0 <= drop x /\ drop x <= &1 / &2}) SUBSET
      IMAGE p (b PCROSS {lift(&0)}) UNION IMAGE p (b PCROSS {t:real^1 | &0 < drop t /\ drop t < &1}) /\
      IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(&1 / &2)}) SUBSET
      IMAGE p (b PCROSS {t:real^1 | &0 < drop t /\ drop t < &1}) /\
      IMAGE (p:real^(N,1)finite_sum->real^N)
        (b PCROSS {t:real^1 | --(&1 / &2) < drop t /\ drop t < &1 / &2}) SUBSET
      IMAGE p (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0}) UNION
      IMAGE p (b PCROSS {x:real^1 | &0 <= drop x /\ drop x <= &1 / &2}) /\
      IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(&0)}) SUBSET
      IMAGE p (b PCROSS {x:real^1 | &0 <= drop x /\ drop x <= &1 / &2})`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION; GSYM PCROSS_UNION] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_UNION; IN_ELIM_THM; IN_SING] THEN
      REWRITE_TAC[FORALL_UNWIND_THM2; LIFT_DROP; GSYM DROP_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`d UNION IMAGE (p:real^(N,1)finite_sum->real^N)
                 (b PCROSS {x:real^1 | &0 <= drop x /\ drop x <= &1 / &2})`;
      `IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(&1 / &2)})`] THEN
    ASM_REWRITE_TAC[SUBSET_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b c:real^N->bool. b SUBSET c ==> a UNION b SUBSET a UNION c`) THEN
      USE_THEN "inw" MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    MP_TAC(ISPECL [`b:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`; `--(&1 / &2)`; `&0`] PRODUCT_ANNULUS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s26_level] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_S3LV_ANN_SYM) THEN
    MP_TAC(ISPECL [`x:real^N->bool`; `d:real^N->bool`; `b:real^N->bool`;
                   `IMAGE (p:real^(N,1)finite_sum->real^N)
                      (b PCROSS {x:real^1 | --(&1 / &2) <= drop x /\ drop x <= &0})`;
                   `IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(--(&1 / &2))})`;
                   `V:real^N->bool`] MOI_S3LV_OUTER_FROM_ANN) THEN
    SUBGOAL_THEN
     `IMAGE (p:real^(N,1)finite_sum->real^N)
        (b PCROSS {x:real^1 | --(&1 / &2) <= drop x /\ drop x <= &0}) SUBSET
      IMAGE p (b PCROSS {lift(&0)}) UNION IMAGE p (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0}) /\
      IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(--(&1 / &2))}) SUBSET
      IMAGE p (b PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0}) /\
      IMAGE (p:real^(N,1)finite_sum->real^N)
        (b PCROSS {t:real^1 | --(&1 / &2) < drop t /\ drop t < &1 / &2}) SUBSET
      IMAGE p (b PCROSS {t:real^1 | &0 < drop t /\ drop t < &1}) UNION
      IMAGE p (b PCROSS {x:real^1 | --(&1 / &2) <= drop x /\ drop x <= &0}) /\
      IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(&0)}) SUBSET
      IMAGE p (b PCROSS {x:real^1 | --(&1 / &2) <= drop x /\ drop x <= &0})`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION; GSYM PCROSS_UNION] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_UNION; IN_ELIM_THM; IN_SING] THEN
      REWRITE_TAC[FORALL_UNWIND_THM2; LIFT_DROP; GSYM DROP_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`d UNION IMAGE (p:real^(N,1)finite_sum->real^N)
                 (b PCROSS {x:real^1 | --(&1 / &2) <= drop x /\ drop x <= &0})`;
      `IMAGE (p:real^(N,1)finite_sum->real^N) (b PCROSS {lift(--(&1 / &2))})`] THEN
    ASM_REWRITE_TAC[SUBSET_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b c:real^N->bool. b SUBSET c ==> a UNION b SUBSET a UNION c`) THEN
      USE_THEN "inw" MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN REAL_ARITH_TAC;
      ASM SET_TAC[]]]);;

(* ========================================================================= *)
(* Part 13: the collar of a boundary polygon J of a member C.  The          *)
(* one-sided boundary collar of a compact PL surface is                     *)
(* MOI_FCB_BOUNDARY_COLLAR_2 (pc_moi_fnd_bcollar), used here through the    *)
(* local term moi_s3lv_collar2 (its text at real^3) as an explicit          *)
(* hypothesis, discharged in Part 22; restricted to J by                    *)
(* MOI_FBC_COLLAR_RESTRICT, it is an annulus A with ends J and J1           *)
(* (MOI_S3LV_SLAB_ANNULUS) meeting the boundary of C exactly in J and       *)
(* containing J in its interior relative to C.                              *)
(* ========================================================================= *)

(* Adapted from the proof of PRODUCT_ANNULUS of pc_moi_s28_plane.ml: the    *)
(* slab of a one-sided product is an annulus.                               *)

let MOI_S3LV_SLAB_ANNULUS = prove
 (`!(j:real^N->bool) X (p:real^(N,1)finite_sum->real^N) q a b.
     pl_sphere 1 j /\ pl_homeomorphism (j PCROSS interval[lift a,lift b],X) (p,q) /\ a < b
     ==> pl_annulus_with_ends X (IMAGE p (j PCROSS {lift a})) (IMAGE p (j PCROSS {lift b}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  X_CHOOSE_TAC `phi:real^(2,1)finite_sum->real^2` MOI_FPS_PSI_PLH THEN
  MP_TAC(ISPECL [`moi_fps_sq`; `j:real^N->bool`] MOI_S8PL_SPHERE1_PLH) THEN
  ASM_REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2->real^N` (X_CHOOSE_THEN `u':real^N->real^2`
    ASSUME_TAC)) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] MOI_S8PL_INTERVAL_PLH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `lam':real^1->real^1`) THEN
  ABBREV_TAC `lam = \t:real^1. (b - a) % t + lift(&2 * a - b)` THEN
  MP_TAC(ISPECL [`moi_fps_sq`; `j:real^N->bool`; `interval[lift(&1),lift(&2)]`;
                 `interval[lift a,lift b]`; `u:real^2->real^N`; `u':real^N->real^2`;
                 `lam:real^1->real^1`; `lam':real^1->real^1`] MOI_S8PL_PLH_PCROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON] THEN
    SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL];
    DISCH_TAC] THEN
  SUBGOAL_THEN `IMAGE (u:real^2->real^N) moi_fps_sq = j` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_fps_sq,j) (u:real^2->real^N,u')` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = \z:real^(2,1)finite_sum.
                      pastecart ((u:real^2->real^N) (fstcart z))
                                ((lam:real^1->real^1) (sndcart z))` THEN
  ABBREV_TAC `Lam' = \z:real^(N,1)finite_sum.
                       pastecart ((u':real^N->real^2) (fstcart z))
                                 ((lam':real^1->real^1) (sndcart z))` THEN
  MAP_EVERY EXISTS_TAC
   [`(p:real^(N,1)finite_sum->real^N) o
     (Lam:real^(2,1)finite_sum->real^(N,1)finite_sum) o moi_fps_psi`;
    `((phi:real^(2,1)finite_sum->real^2) o
      (Lam':real^(N,1)finite_sum->real^(2,1)finite_sum)) o
     (q:real^N->real^(N,1)finite_sum)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(j:real^N->bool) PCROSS interval[lift a,lift b]` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[lift(&1),lift(&2)]` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE moi_fps_psi (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) =
    moi_fps_sq PCROSS {lift(&1)} /\
    IMAGE moi_fps_psi (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) =
    moi_fps_sq PCROSS {lift(&2)}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S8PL_RF12] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S8PL_PSI_LEVEL THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. IMAGE (Lam:real^(2,1)finite_sum->real^(N,1)finite_sum) (moi_fps_sq PCROSS {lift r}) =
        j PCROSS {(b - a) % lift r + lift(&2 * a - b)}`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Lam" THEN REWRITE_TAC[MOI_S8PL_IMAGE_PCROSS_MAP] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN EXPAND_TAC "lam" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b - a) % lift(&1) + lift(&2 * a - b) = lift a /\
                (b - a) % lift(&2) + lift(&2 * a - b) = lift b`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]);;

let MOI_S3LV_CM_COMPACT = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> compact (UNIONS c) /\ compact (surface_boundary c) /\
         surface_boundary c SUBSET UNIONS c`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS c:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]);;

let MOI_S3LV_COLLAR_SUB = prove
 (`!(b:real^N->bool) sb w (p:real^(N,1)finite_sum->real^N) q.
     homeomorphism (b PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
     (!x. x IN b ==> p(pastecart x (vec 0)) = x) /\ sb SUBSET b
     ==> IMAGE p (sb PCROSS {lift(&0)}) = sb /\
         IMAGE p (sb PCROSS interval[vec 0,vec 1]) INTER b = sb /\
         DISJOINT (IMAGE p (sb PCROSS {lift(&1)})) b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hom") (CONJUNCTS_THEN2 (LABEL_TAC "id")
    (MP_TAC o REWRITE_RULE[SUBSET]))) THEN
  DISCH_THEN(LABEL_TAC "sbb") THEN
  USE_THEN "hom" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!y t z. y IN b /\ t IN interval[vec 0:real^1,vec 1] /\ z IN b /\
            (p:real^(N,1)finite_sum->real^N) (pastecart y t) = z
            ==> y = z /\ t = vec 0`
  (LABEL_TAC "inj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^(N,1)finite_sum->real^N) (pastecart z (vec 0)) = z` ASSUME_TAC THENL
     [USE_THEN "id" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `pastecart (y:real^N) (t:real^1) IN b PCROSS interval[vec 0,vec 1] /\
                  pastecart (z:real^N) (vec 0:real^1) IN b PCROSS interval[vec 0,vec 1]`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
    SUBGOAL_THEN `pastecart (y:real^N) (t:real^1) = pastecart z (vec 0)` MP_TAC THENL
     [UNDISCH_TAC `!x. x IN b PCROSS interval[vec 0:real^1,vec 1]
                       ==> (q:real^N->real^(N,1)finite_sum) ((p:real^(N,1)finite_sum->real^N) x) = x` THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `pastecart (y:real^N) (t:real^1)` th) THEN
                           MP_TAC(SPEC `pastecart (z:real^N) (vec 0:real^1)` th)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REWRITE_TAC[PASTECART_INJ]];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_NUM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; IN_SING] THEN
      MAP_EVERY X_GEN_TAC [`y:real^N`; `t:real^1`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p:real^(N,1)finite_sum->real^N) (pastecart y (vec 0)) = y` SUBST1_TAC THENL
       [USE_THEN "id" MATCH_MP_TAC THEN USE_THEN "sbb" MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`z:real^N`; `vec 0:real^1`] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "id" MATCH_MP_TAC THEN
      USE_THEN "sbb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`y:real^N`; `t:real^1`] THEN REPEAT DISCH_TAC THEN
      USE_THEN "inj" (MP_TAC o SPECL [`y:real^N`; `t:real^1`;
        `(p:real^(N,1)finite_sum->real^N) (pastecart y t)`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "sbb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [ALL_TAC; REWRITE_TAC[SUBSET] THEN USE_THEN "sbb" ACCEPT_TAC] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`z:real^N`; `vec 0:real^1`] THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "id" MATCH_MP_TAC THEN USE_THEN "sbb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[SET_RULE `DISJOINT (s:real^N->bool) t <=> !x. x IN s ==> ~(x IN t)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `t:real^1`] THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "inj" (MP_TAC o SPECL [`y:real^N`; `t:real^1`;
      `(p:real^(N,1)finite_sum->real^N) (pastecart y t)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      USE_THEN "sbb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[VEC_EQ; ARITH_EQ]]]);;

let moi_s3lv_collar2 =
 `!(c:(real^3->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ surface_boundary c SUBSET v
     ==> ?w (p:real^(3,1)finite_sum->real^3) q.
           pl_homeomorphism (surface_boundary c PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           surface_boundary c SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN surface_boundary c ==> p(pastecart x (vec 0)) = x`;;

let MOI_S3LV_INNER_COLLAR = prove
 (mk_imp(moi_s3lv_collar2,
  `!(cc:(real^3->bool)->bool) J.
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
     J IN components (surface_boundary cc)
     ==> ?A J1. pl_annulus_with_ends A J J1 /\ A SUBSET UNIONS cc /\
                J SUBSET (subtopology euclidean (UNIONS cc)) interior_of A /\
                A INTER surface_boundary cc = J /\ DISJOINT J1 J`),
  DISCH_THEN(LABEL_TAC "col") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc:(real^3->bool)->bool` MOI_S3LV_CM_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `cc:(real^3->bool)->bool` MOI_FSB_BD_CIRCLES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (J:real^3->bool) /\ J SUBSET surface_boundary cc`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LV_SPHERE1_FACTS) THEN
  USE_THEN "col" (MP_TAC o SPECL [`cc:(real^3->bool)->bool`; `UNIONS cc:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_IN_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (X_CHOOSE_THEN `p:real^(3,1)finite_sum->real^3`
    (X_CHOOSE_THEN `q:real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`UNIONS cc:real^3->bool`; `surface_boundary cc:real^3->bool`;
                 `J:real^3->bool`; `w:real^3->bool`; `p:real^(3,1)finite_sum->real^3`;
                 `q:real^3->real^(3,1)finite_sum`] MOI_FBC_COLLAR_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `surface_boundary cc DIFF (J:real^3->bool) =
                    UNIONS (components (surface_boundary cc) DELETE J)`
      SUBST1_TAC THENL
       [MP_TAC(ISPEC `surface_boundary (cc:(real^3->bool)->bool)` UNIONS_COMPONENTS) THEN
        MP_TAC(ISPEC `surface_boundary (cc:(real^3->bool)->bool)` COMPONENTS_NONOVERLAP) THEN
        UNDISCH_TAC `(J:real^3->bool) IN components (surface_boundary cc)` THEN
        REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_DELETE] THEN MESON_TAC[IN_INTER;
          NOT_IN_EMPTY];
        ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
      ASM_MESON_TAC[MOI_S3LV_SPHERE1_FACTS; COMPACT_IMP_CLOSED];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (surface_boundary cc PCROSS interval[vec 0:real^1,vec 1],w)
                                   (p:real^(3,1)finite_sum->real^3,q)`)) THEN
  MP_TAC(ISPECL [`surface_boundary cc:real^3->bool`; `J:real^3->bool`; `w:real^3->bool`;
                 `p:real^(3,1)finite_sum->real^3`; `q:real^3->real^(3,1)finite_sum`]
                MOI_S3LV_COLLAR_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[homeomorphism]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (p:real^(3,1)finite_sum->real^3) (J PCROSS interval[vec 0,vec 1])`;
    `IMAGE (p:real^(3,1)finite_sum->real^3) (J PCROSS {lift(&1)})`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`J:real^3->bool`;
                   `IMAGE (p:real^(3,1)finite_sum->real^3) (J PCROSS interval[vec 0,vec 1])`;
                   `p:real^(3,1)finite_sum->real^3`; `q':real^3->real^(3,1)finite_sum`;
                   `&0`; `&1`] MOI_S3LV_SLAB_ANNULUS) THEN
    ASM_REWRITE_TAC[LIFT_NUM; REAL_LT_01] THEN
    UNDISCH_TAC `IMAGE (p:real^(3,1)finite_sum->real^3) (J PCROSS {lift(&0)}) = J` THEN
    REWRITE_TAC[LIFT_NUM] THEN SIMP_TAC[];
    ASM SET_TAC[];
    UNDISCH_TAC `DISJOINT (IMAGE (p:real^(3,1)finite_sum->real^3) (J PCROSS {lift(&1)}))
                          (surface_boundary cc)` THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET surface_boundary cc` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Part 14: lemmas for the new member.  The boundary of a PL 2-cell        *)
(* is a PL 1-sphere; the ends of an annulus are disjoint PL 1-spheres in   *)
(* it; finite locally finite complexes are simplicial complexes; the        *)
(* identity of a polyhedron is a PL homeomorphism.                           *)
(* ========================================================================= *)

let MOI_S3LV_CELL_BD_SPHERE = prove
 (`!(d:real^N->bool) b. pl_cell_with_boundary 2 d b ==> pl_sphere 1 b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_sphere] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CEL_PLH_SIMPLEX_RF THEN
  EXISTS_TAC `2` THEN EXISTS_TAC `d:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S3LV_ANN_ENDS = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> DISJOINT j0 j1 /\ j0 SUBSET a /\ j1 SUBSET a /\ compact a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  STRIP_ASSUME_TAC MOI_S3LV_ANN_MODEL THEN
  SUBGOAL_THEN
   `DISJOINT (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
             (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S8PL_RF12; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `!x. x IN moi_fps_ann ==> (g:real^N->real^2) ((f:real^2->real^N) x) = x` THEN
    UNDISCH_TAC `DISJOINT (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
                          (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
                 moi_fps_ann` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
                 moi_fps_ann` THEN
    SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
                 moi_fps_ann` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
                 moi_fps_ann` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S8PL_ANN_CLOSED]]);;

let MOI_S3LV_LF_SC = prove
 (`!c:(real^N->bool)->bool. FINITE c /\ lf_simplicial_complex c ==> simplicial_complex c`,
  REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN MESON_TAC[]);;

let MOI_S3LV_ID_PLH = prove
 (`!s:real^N->bool. pl_polyhedron s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  REWRITE_TAC[HOMEOMORPHISM_ID; GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_S3LV_CELL_BALL = prove
 (`!(d:real^N->bool) b. pl_cell_with_boundary 2 d b ==> pl_ball 2 d`,
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Part 15: the new member C' = (C DIFF (a1 DIFF j1)) UNION delta1 is       *)
(* a combinatorial surface with the boundary of C minus J and Euler         *)
(* characteristic chi(C) + 1.  Glue the disk D to C along J                 *)
(* (MOI_S6G_SURF_GLUE_BODY): a surface Y = C UNION D with chi(C) + 1.  The  *)
(* disk P = D UNION a1 with boundary j1 lies off the boundary of Y, so      *)
(* P DIFF j1 is open in Y and E = Y DIFF (P DIFF j1) = C DIFF (a1 DIFF j1)  *)
(* is a polyhedron (MOI_S8CU_REMOVE_OPEN).  The identity on E and a PL      *)
(* cell extension P -> delta1 fixing j1 glue to a PL homeomorphism of Y     *)
(* onto C' (MOI_PL2_PL_HOMEOMORPHISM_UNION), so any triangulation of C' is  *)
(* combinatorial with the same boundary (SURF_INVARIANT) and the same chi   *)
(* (COMPLEX_EULER_PL_INVARIANT).                                             *)
(* ========================================================================= *)

let MOI_S3LV_NEW_SURFACE = prove
 (`!(cc:(real^N->bool)->bool) J D A a1 j1 delta1.
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
     J IN components (surface_boundary cc) /\
     pl_cell_with_boundary 2 D J /\ UNIONS cc INTER D = J /\
     A SUBSET UNIONS cc /\ A INTER surface_boundary cc = J /\
     pl_annulus_with_ends a1 J j1 /\ a1 SUBSET A UNION D /\ a1 INTER D = J /\
     pl_cell_with_boundary 2 delta1 j1 /\ delta1 INTER UNIONS cc = j1
     ==> ?cc'. FINITE cc' /\ simplicial_complex cc' /\
               combinatorial_manifold_with_boundary 2 cc' /\
               UNIONS cc' = (UNIONS cc DIFF (a1 DIFF j1)) UNION delta1 /\
               surface_boundary cc' = surface_boundary cc DIFF J /\
               complex_euler cc' = complex_euler cc + &1 /\
               (connected (UNIONS cc) ==> connected (UNIONS cc'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc:(real^N->bool)->bool` MOI_S3LV_CM_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET surface_boundary cc /\ ~(J = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^N->bool`; `J:real^N->bool`; `j1:real^N->bool`] MOI_S3LV_ANN_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(a1:real^N->bool) SUBSET A /\ (J:real^N->bool) SUBSET A /\
                a1 SUBSET UNIONS cc` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^N->bool`; `J:real^N->bool`] MOI_S3LV_DISK_CHARTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`delta1:real^N->bool`; `j1:real^N->bool`] MOI_S3LV_DISK_CHARTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (j1:real^N->bool) /\ pl_polyhedron (J:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; MOI_S3LV_CELL_BD_SPHERE]; ALL_TAC] THEN
  (* the glued surface Y = C UNION D *)
  MP_TAC(ISPECL [`D:real^N->bool`; `J:real^N->bool`] MOI_S3LV_DISK_COMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dD:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`cc:(real^N->bool)->bool`; `dD:(real^N->bool)->bool`; `J:real^N->bool`]
                MOI_S6G_SURF_GLUE_BODY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THEN X_GEN_TAC `bb:real^N->bool` THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`surface_boundary (cc:(real^N->bool)->bool)`; `bb:real^N->bool`;
                     `J:real^N->bool`] COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `complex_euler (dD:(real^N->bool)->bool) = &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `dD:(real^N->bool)->bool` COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_CMB_DIM THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S3LV_CELL_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS e = UNIONS cc UNION (D:real^N->bool)` (LABEL_TAC "Ye") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `surface_boundary e = surface_boundary cc DIFF (J:real^N->bool)`
  (LABEL_TAC "be") THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (e:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_LF_SC THEN ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  (* the disk P = D UNION a1 *)
  SUBGOAL_THEN `pl_cell_with_boundary 2 (D UNION a1:real^N->bool) j1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_DISK_ANN THEN EXISTS_TAC `J:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D UNION a1:real^N->bool`; `j1:real^N->bool`] MOI_S3LV_DISK_CHARTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS e)) ((D UNION a1) DIFF (j1:real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_DISK_OPEN THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "Ye" SUBST1_TAC THEN UNDISCH_TAC `(a1:real^N->bool) SUBSET UNIONS cc` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `e:(real^N->bool)->bool` SURF_CHARTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN USE_THEN "Ye" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "be" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN (D UNION a1) DIFF j1` THEN
    UNDISCH_TAC `UNIONS cc INTER D = (J:real^N->bool)` THEN
    UNDISCH_TAC `(a1:real^N->bool) SUBSET A` THEN
    UNDISCH_TAC `(A:real^N->bool) INTER surface_boundary cc = J` THEN
    UNDISCH_TAC `(a1:real^N->bool) SUBSET UNIONS cc` THEN
    UNDISCH_TAC `surface_boundary cc SUBSET UNIONS (cc:(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS e DIFF ((D UNION a1) DIFF j1) = UNIONS cc DIFF (a1 DIFF (j1:real^N->bool))`
  (LABEL_TAC "Eeq") THENL
   [USE_THEN "Ye" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `UNIONS cc INTER D = (J:real^N->bool)` THEN
    UNDISCH_TAC `(a1:real^N->bool) INTER D = J` THEN
    UNDISCH_TAC `DISJOINT (J:real^N->bool) j1` THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET a1` THEN
    UNDISCH_TAC `(j1:real^N->bool) SUBSET a1` THEN
    UNDISCH_TAC `(a1:real^N->bool) SUBSET UNIONS cc` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:(real^N->bool)->bool`; `D UNION a1:real^N->bool`; `j1:real^N->bool`]
                MOI_S8CU_REMOVE_OPEN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "Ye" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `(a1:real^N->bool) SUBSET UNIONS cc` THEN
    UNDISCH_TAC `(j1:real^N->bool) SUBSET a1` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eE:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  USE_THEN "Eeq" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS cc DIFF (a1 DIFF (j1:real^N->bool)))` ASSUME_TAC THENL
   [REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
    EXISTS_TAC `eE:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(UNIONS cc DIFF (a1 DIFF j1)) INTER (D UNION a1) = (j1:real^N->bool) /\
    (UNIONS cc DIFF (a1 DIFF j1)) INTER delta1 = j1 /\
    (UNIONS cc DIFF (a1 DIFF j1)) UNION (D UNION a1) = UNIONS cc UNION D /\
    surface_boundary cc DIFF J SUBSET UNIONS cc DIFF (a1 DIFF (j1:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS cc INTER D = (J:real^N->bool)` THEN
      UNDISCH_TAC `DISJOINT (J:real^N->bool) j1` THEN
      UNDISCH_TAC `(J:real^N->bool) SUBSET a1` THEN
      UNDISCH_TAC `(j1:real^N->bool) SUBSET a1` THEN
      UNDISCH_TAC `(a1:real^N->bool) SUBSET UNIONS cc` THEN SET_TAC[];
      UNDISCH_TAC `delta1 INTER UNIONS cc = (j1:real^N->bool)` THEN
      UNDISCH_TAC `(j1:real^N->bool) SUBSET a1` THEN
      UNDISCH_TAC `(a1:real^N->bool) SUBSET UNIONS cc` THEN SET_TAC[];
      UNDISCH_TAC `(a1:real^N->bool) SUBSET UNIONS cc` THEN SET_TAC[];
      UNDISCH_TAC `surface_boundary cc SUBSET UNIONS (cc:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(a1:real^N->bool) SUBSET A` THEN
      UNDISCH_TAC `(A:real^N->bool) INTER surface_boundary cc = J` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the triangulation of C' *)
  SUBGOAL_THEN
   `pl_polyhedron ((UNIONS cc DIFF (a1 DIFF j1)) UNION delta1:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cc':(real^N->bool)->bool` THEN
  SUBGOAL_THEN `FINITE (cc':(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the PL homeomorphism Y -> C' *)
  MP_TAC(ISPECL [`2`; `D UNION a1:real^N->bool`; `j1:real^N->bool`; `delta1:real^N->bool`;
                 `j1:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] MOI_CEL_CELL_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3LV_ID_PLH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F1:real^N->real^N` (X_CHOOSE_THEN `G1:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`UNIONS cc DIFF (a1 DIFF j1):real^N->bool`; `D UNION a1:real^N->bool`;
                 `UNIONS cc DIFF (a1 DIFF j1):real^N->bool`; `delta1:real^N->bool`;
                 `\x:real^N. x`; `\x:real^N. x`; `F1:real^N->real^N`; `G1:real^N->real^N`]
                MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S3LV_ID_PLH; COMPACT_IMP_CLOSED; PL_POLYHEDRON_IMP_COMPACT; IMAGE_ID] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `phi = \x:real^N. if x IN UNIONS cc DIFF (a1 DIFF j1) then x
                                else (F1:real^N->real^N) x` THEN
  ABBREV_TAC `psi = \y:real^N. if y IN UNIONS cc DIFF (a1 DIFF j1) then y
                                else (G1:real^N->real^N) y` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `pl_homeomorphism (UNIONS e,UNIONS cc') (phi:real^N->real^N,psi)` ASSUME_TAC THENL
   [USE_THEN "Ye" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`e:(real^N->bool)->bool`; `cc':(real^N->bool)->bool`;
                 `phi:real^N->real^N`; `psi:real^N->real^N`] MOI_S3LV_SURF_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && can (find_term ((=) `surface_boundary (cc':(real^N->bool)->bool)`))
                                       (rhs(concl th)))) THEN
    USE_THEN "be" SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^N->real^N) s t. s SUBSET t /\ (!x. x IN t ==> f x = x)
                           ==> IMAGE f s = s`) THEN
    EXISTS_TAC `UNIONS cc DIFF (a1 DIFF (j1:real^N->bool))` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "phi" THEN SIMP_TAC[];
    MP_TAC(ISPECL [`e:(real^N->bool)->bool`; `cc':(real^N->bool)->bool`;
                   `phi:real^N->real^N`; `psi:real^N->real^N`] COMPLEX_EULER_PL_INVARIANT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S8TA_CMB_DIM THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
        concl th = `pl_homeomorphism (UNIONS cc UNION D,
                                      UNIONS cc DIFF (a1 DIFF j1) UNION delta1)
                                     (phi:real^N->real^N,psi)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) &&
      lhand(concl th) = `IMAGE (phi:real^N->real^N) (UNIONS cc UNION D)`)) THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 16: the neighbourhood U of the inmost disk D for Moise 30.3.        *)
(* Remove from R the other members meeting the 2i-th revolved image         *)
(* (finitely many, compact), the part of C outside the C-interior of the    *)
(* collar A, and the part of T outside the T-interior of d2: U is open,     *)
(* contains D, lies in R, and meets the barrier set only in D UNION A UNION *)
(* d2.  Also: removing one component J from s leaves components of s.       *)
(* ========================================================================= *)

let MOI_S3LV_COMPONENTS_DIFF = prove
 (`!(s:real^N->bool) j.
     j IN components s ==> components (s DIFF j) SUBSET components s DELETE j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_DELETE] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(k:real^N->bool = {}) /\ connected k /\ k SUBSET s DIFF j`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`] EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(X_CHOOSE_THEN `k':real^N->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `~(k':real^N->bool = j)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(k':real^N->bool) INTER j = {}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN `connected (k':real^N->bool) /\ k' SUBSET s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) = k'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `s DIFF j:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3LV_NBHD_U = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i C (cc:(real^3->bool)->bool) J D A d2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\
     C IN fam /\ FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ UNIONS cc = C /\
     D SUBSET frontier (s2 (&2 * i)) /\ (!c. c IN fam ==> c INTER D SUBSET J) /\
     J SUBSET C /\
     A SUBSET C /\ J SUBSET (subtopology euclidean C) interior_of A /\
     d2 SUBSET frontier (s2 (&2 * i)) /\
     D SUBSET (subtopology euclidean (frontier (s2 (&2 * i)))) interior_of d2
     ==> ?U. open U /\ D SUBSET U /\
             U SUBSET interior (IMAGE g (revolution (dd (&2 * i)))) /\
             U INTER moi_s32_set g s2 fam SUBSET (D UNION A) UNION d2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_R_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`] MOI_S3LV_TOUCH_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool) /\
                (!c. c IN fam ==> compact (c:real^3->bool))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state (g:real^3->real^3) dd s2 lev fam` THEN
    REWRITE_TAC[moi_s32_state] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^3->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t &&
                               fst(dest_const t) = "combinatorial_manifold_with_boundary"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i0:int` (X_CHOOSE_THEN `cc0:(real^3->bool)->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPEC `cc0:(real^3->bool)->bool` MOI_S3LV_CM_COMPACT) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))` THEN
  ABBREV_TAC `FF = UNIONS {c:real^3->bool | c IN fam /\ ~(c = C) /\ ~DISJOINT c X}` THEN
  ABBREV_TAC `KC = (C:real^3->bool) DIFF (subtopology euclidean C) interior_of A` THEN
  ABBREV_TAC `KT = frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                   (subtopology euclidean (frontier (s2 (&2 * i)))) interior_of d2` THEN
  SUBGOAL_THEN `compact (C:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (FF:real^3->bool) /\ closed (KC:real^3->bool) /\
                closed (KT:real^3->bool)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "FF" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{c:real^3->bool | c IN fam /\ ~DISJOINT c X}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
      EXPAND_TAC "KC" THEN MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
      EXISTS_TAC `C:real^3->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL; OPEN_IN_INTERIOR_OF];
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      EXPAND_TAC "KT" THEN MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
      EXISTS_TAC `frontier ((s2:int->real^3->bool) (&2 * i))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL; OPEN_IN_INTERIOR_OF];
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]];
    ALL_TAC] THEN
  EXISTS_TAC `interior (X:real^3->bool) DIFF (FF UNION KC UNION KT)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
    ASM_SIMP_TAC[CLOSED_UNION];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(D:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET interior X` THEN
      UNDISCH_TAC `(y:real^3) IN D` THEN SET_TAC[];
      EXPAND_TAC "FF" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN
      DISCH_THEN(MP_TAC o SPECL [`c:real^3->bool`; `C:real^3->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real^3->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `D:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET C` THEN UNDISCH_TAC `(y:real^3) IN c` THEN
      UNDISCH_TAC `(y:real^3) IN D` THEN SET_TAC[];
      EXPAND_TAC "KC" THEN REWRITE_TAC[IN_DIFF] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `C:real^3->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `D:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET (subtopology euclidean C) interior_of A` THEN
      UNDISCH_TAC `(y:real^3) IN D` THEN SET_TAC[];
      EXPAND_TAC "KT" THEN REWRITE_TAC[IN_DIFF] THEN
      UNDISCH_TAC `(D:real^3->bool) SUBSET
                   (subtopology euclidean (frontier ((s2:int->real^3->bool) (&2 * i))))
                   interior_of d2` THEN
      UNDISCH_TAC `(y:real^3) IN D` THEN SET_TAC[]];
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    REWRITE_TAC[moi_s32_set; SUBSET; IN_INTER; IN_DIFF; IN_UNION; IN_SING; DE_MORGAN_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [DISJ2_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i))` ASSUME_TAC THENL
       [MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `moi_s32_evens s2 INTER (X:real^3->bool) =
                     frontier ((s2:int->real^3->bool) (&2 * i))` THEN
        UNDISCH_TAC `(y:real^3) IN moi_s32_evens s2` THEN
        UNDISCH_TAC `(y:real^3) IN interior X` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`subtopology euclidean (frontier ((s2:int->real^3->bool) (&2 * i)))`;
                     `d2:real^3->bool`] INTERIOR_OF_SUBSET) THEN
      UNDISCH_TAC `~((y:real^3) IN KT)` THEN EXPAND_TAC "KT" THEN
      UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i))` THEN SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN UNIONS fam` THEN REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `c:real^3->bool = C` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISJ1_TAC THEN DISJ2_TAC THEN
        MP_TAC(ISPECL [`subtopology euclidean (C:real^3->bool)`; `A:real^3->bool`]
          INTERIOR_OF_SUBSET) THEN
        UNDISCH_TAC `~((y:real^3) IN KC)` THEN EXPAND_TAC "KC" THEN
        UNDISCH_TAC `(y:real^3) IN C` THEN SET_TAC[];
        UNDISCH_TAC `~((y:real^3) IN FF)` THEN EXPAND_TAC "FF" THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `c:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(y:real^3) IN c` THEN UNDISCH_TAC `(y:real^3) IN interior X` THEN
        SET_TAC[]];
      UNDISCH_TAC `(y:real^3) IN interior X` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN X)` THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* Part 17: the member invariant of moi_s32_state3 (pc_moi_s3032_stmt6)      *)
(* under the cap.  DONE for state3; removing a component; the cap removes   *)
(* the inessential trace polygon J from the components of the trace on K,   *)
(* so essc is unchanged and inessc loses J, while chi grows by one: C'      *)
(* keeps the history witness of C.                                           *)
(* ========================================================================= *)

let MOI_S3LV_DONE3 = prove
 (`!(g:real^3->real^3) dd s2 lev fam i.
     moi_s32_state3 g dd s2 lev fam /\ moi_s3lv_iness s2 i fam = {}
     ==> moi_s32_state3 g dd s2 (i INSERT lev) fam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_state3; moi_s3lv_iness] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(c:real^3->bool) IN fam`) o SPEC `c:real^3->bool` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_lvl")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i':int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`i':int`; `cc:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`jj:real^3->bool`; `c:real^3->bool`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_ess")) (concl th) &&
          not(can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_lvl"))
                  (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(i':int) = i` THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&2 * (i':int) + &2 = &2 * i` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                                            REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(i':int) + &1 = i` THEN INT_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`jj:real^3->bool`; `c:real^3->bool`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_ess")) (concl th) &&
          not(can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_lvl"))
                  (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

let MOI_S3LV_COMPONENTS_DIFF_EQ = prove
 (`!(s:real^N->bool) j.
     j IN components s ==> components (s DIFF j) = components s DELETE j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[MOI_S3LV_COMPONENTS_DIFF] THEN
  REWRITE_TAC[SUBSET; IN_DELETE] THEN X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k:real^N->bool = {}) /\ connected k /\ k SUBSET s /\ k INTER j = {}`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET;
                  COMPONENTS_NONOVERLAP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s DIFF j:real^N->bool`; `k:real^N->bool`] EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(X_CHOOSE_THEN `k':real^N->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(k:real^N->bool) = k'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected (k':real^N->bool) /\ k' SUBSET s DIFF j` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S3LV_ESSC_CAP = prove
 (`!(s2:int->real^3->bool) i i' (C:real^3->bool) C' J.
     J IN components (C INTER moi_s32_evens s2) /\
     C' INTER moi_s32_evens s2 = (C INTER moi_s32_evens s2) DIFF J /\
     ~moi_s32_ess s2 (&2 * i) J /\ J SUBSET frontier (s2 (&2 * i)) /\ ~(J = {}) /\
     (i' = i \/ i' + &1 = i) /\
     DISJOINT (frontier (s2 (&2 * i'))) (frontier (s2 (&2 * i' + &2)))
     ==> moi_s32_essc s2 i' C' = moi_s32_essc s2 i' C /\
         moi_s32_inessc s2 i' C' = moi_s32_inessc s2 i' C DELETE J /\
         J IN moi_s32_inessc s2 i' C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lv") ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `~(moi_s32_ess s2 (&2 * i') J \/ moi_s32_ess s2 (&2 * i' + &2) J)`
  ASSUME_TAC THENL
   [USE_THEN "lv" (DISJ_CASES_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s32_ess] THEN
      UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                            (frontier (s2 (&2 * i + &2)))` THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      UNDISCH_TAC `~(J:real^3->bool = {})` THEN SET_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[INT_ARITH `&2 * (i' + &1) = &2 * i' + &2:int`]) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s32_ess] THEN
      UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i')))
                            (frontier (s2 (&2 * i' + &2)))` THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i' + &2))` THEN
      UNDISCH_TAC `~(J:real^3->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[moi_s32_essc; moi_s32_inessc; MOI_S3LV_COMPONENTS_DIFF_EQ] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `jj:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
    ASM_CASES_TAC `jj:real^3->bool = J` THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `jj:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
    ASM_CASES_TAC `jj:real^3->bool = J` THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3LV_HIST_CAP = prove
 (`!(s2:int->real^3->bool) i' (cc:(real^3->bool)->bool) cc' (C:real^3->bool) C' J.
     moi_s32_hist s2 i' cc C /\
     moi_s32_essc s2 i' C' = moi_s32_essc s2 i' C /\
     moi_s32_inessc s2 i' C' = moi_s32_inessc s2 i' C DELETE J /\
     J IN moi_s32_inessc s2 i' C /\
     complex_euler cc' = complex_euler cc + &1
     ==> moi_s32_hist s2 i' cc' C'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_hist] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c0:real^3->bool`
    (X_CHOOSE_THEN `cc0:(real^3->bool)->bool` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`c0:real^3->bool`; `cc0:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[FINITE_DELETE] THEN ASM_SIMP_TAC[CARD_DELETE] THEN
  SUBGOAL_THEN `1 <= CARD (moi_s32_inessc s2 i' (C:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  UNDISCH_TAC `complex_euler (cc:(real^3->bool)->bool) +
               &(CARD (moi_s32_inessc s2 i' (C:real^3->bool))) =
               complex_euler (cc0:(real^3->bool)->bool) +
               &(CARD (moi_s32_inessc s2 i' (c0:real^3->bool)))` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part 18: set bookkeeping of the cap.  With a1 in the collar A of J       *)
(* in C (A meets K only in J) and delta1 meeting the barrier only in j1:    *)
(* the new member C' = (C DIFF (a1 DIFF j1)) UNION delta1 meets K in        *)
(* (C INTER K) DIFF J, and the new barrier set c' of 30.3                  *)
(* is the barrier set of the new family; the trace of C' on a torus Tq of   *)
(* its level has components among those of C.                               *)
(* ========================================================================= *)

let MOI_S3LV_CAP_K = prove
 (`!(C:real^3->bool) K A a1 D J j1 delta1 cs.
     J SUBSET C /\ J SUBSET K /\
     A SUBSET C /\ A INTER (C INTER K) = J /\ a1 SUBSET D UNION A /\ a1 INTER D = J /\
     j1 SUBSET a1 /\ J SUBSET a1 /\ DISJOINT J j1 /\
     delta1 INTER cs = j1 /\ C SUBSET cs /\ K SUBSET cs
     ==> ((C DIFF (a1 DIFF j1)) UNION delta1) INTER K = (C INTER K) DIFF J /\
         delta1 INTER C = j1 /\ a1 SUBSET C /\ a1 INTER K = J /\ j1 SUBSET delta1 /\
         delta1 INTER K = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a1:real^3->bool) SUBSET A /\ a1 SUBSET C` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a1:real^3->bool) INTER K = J` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET delta1 /\ delta1 INTER C = j1` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(delta1:real^3->bool) INTER K = {}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3LV_CAP_SET = prove
 (`!(fam:(real^3->bool)->bool) C K g0 a1 J j1 delta1.
     pairwise DISJOINT fam /\ C IN fam /\
     J SUBSET C /\ J SUBSET K /\ a1 SUBSET C /\ a1 INTER K = J /\ J SUBSET a1 /\
     ~(g0 IN a1)
     ==> ((K UNION UNIONS fam UNION {g0}) DIFF (a1 DIFF (J UNION j1))) UNION delta1 =
         K UNION UNIONS (((C DIFF (a1 DIFF j1)) UNION delta1) INSERT (fam DELETE C)) UNION
         {g0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[UNIONS_INSERT] THEN
  SUBGOAL_THEN `UNIONS fam = UNIONS (fam DELETE C) UNION (C:real^3->bool)` SUBST1_TAC THENL
   [UNDISCH_TAC `(C:real^3->bool) IN fam` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (UNIONS (fam DELETE C)) (C:real^3->bool)` MP_TAC THENL
   [REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC; IN_DELETE] THEN
    UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(C:real^3->bool) IN fam` THEN
    REWRITE_TAC[pairwise; DISJOINT] THEN MESON_TAC[INTER_COMM];
    ALL_TAC] THEN
  UNDISCH_TAC `(J:real^3->bool) SUBSET C` THEN UNDISCH_TAC `(J:real^3->bool) SUBSET K` THEN
  UNDISCH_TAC `(a1:real^3->bool) SUBSET C` THEN UNDISCH_TAC `(a1:real^3->bool) INTER K = J` THEN
  UNDISCH_TAC `(J:real^3->bool) SUBSET a1` THEN UNDISCH_TAC `~((g0:real^3) IN a1)` THEN
  SET_TAC[]);;

let MOI_S3LV_CAP_TRACE = prove
 (`!(C:real^3->bool) C' K J Tq.
     C' INTER K = (C INTER K) DIFF J /\ Tq SUBSET K /\
     (J IN components (C INTER Tq) \/ DISJOINT J Tq)
     ==> components (C' INTER Tq) SUBSET components (C INTER Tq)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(C':real^3->bool) INTER Tq = (C INTER Tq) DIFF J` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`(C:real^3->bool) INTER Tq`; `J:real^3->bool`] MOI_S3LV_COMPONENTS_DIFF) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    SUBGOAL_THEN `(C:real^3->bool) INTER Tq DIFF J = C INTER Tq` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[SUBSET_REFL]]]);;

(* ========================================================================= *)
(* Part 19: the new state after one cap (Moise p.226).  Given the data      *)
(* of the inmost disk, the collar and the output of 30.3 with the new       *)
(* member surface, the family C' INSERT (fam DELETE C) is a state3 at the   *)
(* same levels, with one inessential polygon fewer on T, the same barrier   *)
(* set outside R and the same members missing R.                            *)
(* ========================================================================= *)

let MOI_S3LV_CELL_NONEMPTY = prove
 (`!n (d:real^N->bool) b. pl_cell_with_boundary n d b ==> ~(d = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM AFF_DIM_POS_LE] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN INT_ARITH_TAC);;

let MOI_S3LV_ANN_NONEMPTY = prove
 (`!(a:real^N->bool) j0 j1. pl_annulus_with_ends a j0 j1 ==> ~(j0 = {}) /\ ~(j1 = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `&1` MOI_S8PL_RF_FACTS); MP_TAC(SPEC `&2` MOI_S8PL_RF_FACTS)] THEN
  REWRITE_TAC[REAL_LT_01; REAL_OF_NUM_LT; ARITH] THEN SIMP_TAC[]);;

let MOI_S3LV_NEW_STATE = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam i C i' (cc:(real^3->bool)->bool)
    (cc':(real^3->bool)->bool) J D A U c' a1 j1 delta1.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state3 g dd s2 lev fam /\ C IN fam /\
     C SUBSET moi_s32_lvl g dd i' /\ FINITE cc /\
     combinatorial_manifold_with_boundary 2 cc /\ UNIONS cc = C /\
     surface_boundary cc = C INTER moi_s32_evens s2 /\
     C INTER moi_s32_evens s2 SUBSET
       frontier (s2 (&2 * i')) UNION frontier (s2 (&2 * i' + &2)) /\
     (i' IN lev
      ==> !jj. jj IN components (C INTER frontier (s2 (&2 * i')))
               ==> moi_s32_ess s2 (&2 * i') jj) /\
     ((i' + &1) IN lev
      ==> !jj. jj IN components (C INTER frontier (s2 (&2 * i' + &2)))
               ==> moi_s32_ess s2 (&2 * i' + &2) jj) /\
     moi_s32_hist s2 i' cc C /\
     J IN components (C INTER frontier (s2 (&2 * i))) /\
     J IN moi_s3lv_iness s2 i fam /\
     D SUBSET frontier (s2 (&2 * i)) /\ pl_cell_with_boundary 2 D J /\
     A SUBSET C /\ A INTER surface_boundary cc = J /\
     D SUBSET U /\ U SUBSET interior (IMAGE g (revolution (dd (&2 * i)))) /\
     closed_in (subtopology euclidean (moi_s32_open g)) c' /\
     separates_in (moi_s32_open g) c' {g moi_s32_qlo} {g moi_s32_qhi} /\
     c' DIFF U = moi_s32_set g s2 fam DIFF U /\
     pl_annulus_with_ends a1 J j1 /\ a1 SUBSET (D UNION A) INTER U /\ a1 INTER D = J /\
     delta1 SUBSET U /\ delta1 INTER moi_s32_set g s2 fam = j1 /\
     c' = (moi_s32_set g s2 fam DIFF (a1 DIFF (J UNION j1))) UNION delta1 /\
     FINITE cc' /\ combinatorial_manifold_with_boundary 2 cc' /\
     UNIONS cc' = (C DIFF (a1 DIFF j1)) UNION delta1 /\
     surface_boundary cc' = surface_boundary cc DIFF J /\
     complex_euler cc' = complex_euler cc + &1 /\ connected (UNIONS cc')
     ==> moi_s32_state3 g dd s2 lev (((C DIFF (a1 DIFF j1)) UNION delta1) INSERT
                                     (fam DELETE C)) /\
         moi_s3lv_iness s2 i (((C DIFF (a1 DIFF j1)) UNION delta1) INSERT (fam DELETE C))
           PSUBSET moi_s3lv_iness s2 i fam /\
         moi_s32_set g s2 (((C DIFF (a1 DIFF j1)) UNION delta1) INSERT (fam DELETE C)) DIFF
           interior (IMAGE g (revolution (dd (&2 * i)))) =
         moi_s32_set g s2 fam DIFF interior (IMAGE g (revolution (dd (&2 * i)))) /\
         {c | c IN ((C DIFF (a1 DIFF j1)) UNION delta1) INSERT (fam DELETE C) /\
              DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
         {c | c IN fam /\ DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* -------------------------------------------------------------------- *)
  (* abbreviations and basic facts                                         *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_R_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
               MOI_S3LV_TOWER_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s32_state3 (g:real^3->real^3) dd s2 lev fam` THEN
  REWRITE_TAC[moi_s32_state3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pw") (CONJUNCTS_THEN2 (LABEL_TAC "mem")
    (CONJUNCTS_THEN2 (LABEL_TAC "fin") (CONJUNCTS_THEN2 (LABEL_TAC "cl") (LABEL_TAC "sep"))))) THEN
  ABBREV_TAC `X = IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))` THEN
  ABBREV_TAC `KK = moi_s32_evens (s2:int->real^3->bool)` THEN
  ABBREV_TAC `cs = moi_s32_set (g:real^3->real^3) s2 fam` THEN
  ABBREV_TAC `C' = ((C:real^3->bool) DIFF (a1 DIFF j1)) UNION delta1` THEN
  SUBGOAL_THEN `cs = (KK:real^3->bool) UNION UNIONS fam UNION {(g:real^3->real^3) (vec 0)}`
  (LABEL_TAC "cs") THENL
   [EXPAND_TAC "cs" THEN EXPAND_TAC "KK" THEN REWRITE_TAC[moi_s32_set]; ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3->bool) SUBSET C /\ J SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) /\
                ~(J = {})` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(C:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                   `J:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    MP_TAC(ISPECL [`(C:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                   `J:real^3->bool`] IN_COMPONENTS_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET KK /\
                (J:real^3->bool) SUBSET KK` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(KK:real^3->bool) INTER X = frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^3->bool) SUBSET cs /\ (KK:real^3->bool) SUBSET cs /\
                UNIONS fam SUBSET (cs:real^3->bool)` STRIP_ASSUME_TAC THENL
   [USE_THEN "cs" SUBST1_TAC THEN UNDISCH_TAC `(C:real^3->bool) IN fam` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `J:real^3->bool`; `j1:real^3->bool`] MOI_S3LV_ANN_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `J:real^3->bool`; `j1:real^3->bool`]
                MOI_S3LV_ANN_NONEMPTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(A:real^3->bool) INTER (C INTER KK) = J` ASSUME_TAC THENL
   [UNDISCH_TAC `(A:real^3->bool) INTER surface_boundary cc = J` THEN
    UNDISCH_TAC `surface_boundary cc = (C:real^3->bool) INTER KK` THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real^3->bool`; `KK:real^3->bool`; `A:real^3->bool`; `a1:real^3->bool`;
                 `D:real^3->bool`; `J:real^3->bool`; `j1:real^3->bool`; `delta1:real^3->bool`;
                 `cs:real^3->bool`] MOI_S3LV_CAP_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET (D UNION A) INTER U` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* -------------------------------------------------------------------- *)
  (* the level of C and the region                                         *)
  (* -------------------------------------------------------------------- *)
  SUBGOAL_THEN `(i':int = i - &1 \/ i' = i) /\ X SUBSET moi_s32_lvl (g:real^3->real^3) dd i'`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [SUBGOAL_THEN `~DISJOINT (moi_s32_lvl (g:real^3->real^3) dd i') X` ASSUME_TAC THENL
     [MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(C:real^3->bool) SUBSET moi_s32_lvl g dd i'` THEN
      UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET interior X` THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET C` THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      UNDISCH_TAC `~(J:real^3->bool = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `i':int = i - &1 \/ i' = i` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s32_lvl")) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "X" THEN REWRITE_TAC[moi_s32_lvl] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THENL
     [REWRITE_TAC[INT_ARITH `&2 * (i - &1) + &2 = &2 * i:int`] THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* J on KK, its inessentiality, essc and the history witness             *)
  (* -------------------------------------------------------------------- *)
  SUBGOAL_THEN `(J:real^3->bool) IN components (C INTER KK)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i':int`;
                  `C:real^3->bool`; `cc:(real^3->bool)->bool`] MOI_S3LV_TRACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~moi_s32_ess s2 (&2 * i) J` ASSUME_TAC THENL
   [UNDISCH_TAC `(J:real^3->bool) IN moi_s3lv_iness s2 i fam` THEN
    REWRITE_TAC[moi_s3lv_iness; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i')))
                         (frontier (s2 (&2 * i' + &2)))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i' + &1:int`; `i':int`]
                 MOI_S3LV_TORI_FRONTIERS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `&2 * (i' + &1) = &2 * i' + &2:int`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s2:int->real^3->bool`; `i:int`; `i':int`; `C:real^3->bool`;
                 `C':real^3->bool`; `J:real^3->bool`] MOI_S3LV_ESSC_CAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(i':int = i - &1 \/ i' = i)` THEN INT_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s32_hist s2 i' cc' (C':real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_HIST_CAP THEN
    MAP_EVERY EXISTS_TAC [`cc:(real^3->bool)->bool`; `C:real^3->bool`; `J:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Tq. Tq SUBSET KK /\ (J IN components (C INTER Tq) \/ DISJOINT J Tq)
         ==> components ((C':real^3->bool) INTER Tq) SUBSET components (C INTER Tq)`
  (LABEL_TAC "trq") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3LV_CAP_TRACE THEN
    EXISTS_TAC `KK:real^3->bool` THEN EXISTS_TAC `J:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ~(k = i)
        ==> DISJOINT (J:real^3->bool) (frontier ((s2:int->real^3->bool) (&2 * k)))`
  (LABEL_TAC "jdis") THENL
   [X_GEN_TAC `k:int` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `k:int`]
                 MOI_S3LV_TORI_FRONTIERS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. frontier ((s2:int->real^3->bool) (&2 * k)) SUBSET KK` (LABEL_TAC "tk") THENL
   [GEN_TAC THEN EXPAND_TAC "KK" THEN REWRITE_TAC[moi_s32_evens; SUBSET; IN_UNIONS;
      IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `frontier ((s2:int->real^3->bool) (&2 * k))` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `k:int` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* the new barrier set                                                    *)
  (* -------------------------------------------------------------------- *)
  SUBGOAL_THEN `moi_s32_set (g:real^3->real^3) s2 ((C':real^3->bool) INSERT (fam DELETE C)) = c'`
  (LABEL_TAC "cset1") THENL
   [REWRITE_TAC[moi_s32_set] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cs" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "C'" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_S3LV_CAP_SET THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET (D UNION A) INTER U` THEN
    UNDISCH_TAC `(U:real^3->bool) SUBSET interior X` THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN X)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "cset1" (fun th -> REWRITE_TAC[th]) THEN
  (* -------------------------------------------------------------------- *)
  (* the new member C'                                                      *)
  (* -------------------------------------------------------------------- *)
  SUBGOAL_THEN
   `(C':real^3->bool) SUBSET moi_s32_lvl g dd i' /\ connected C' /\ ~(C' = {}) /\
    surface_boundary cc' = C' INTER KK /\
    C' INTER KK SUBSET frontier ((s2:int->real^3->bool) (&2 * i')) UNION
                        frontier (s2 (&2 * i' + &2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "C'" THEN
      UNDISCH_TAC `(C:real^3->bool) SUBSET moi_s32_lvl g dd i'` THEN
      UNDISCH_TAC `(X:real^3->bool) SUBSET moi_s32_lvl g dd i'` THEN
      UNDISCH_TAC `(delta1:real^3->bool) SUBSET U` THEN
      UNDISCH_TAC `(U:real^3->bool) SUBSET interior X` THEN
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      UNDISCH_TAC `UNIONS cc' = (C':real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "C'" THEN
      UNDISCH_TAC `(j1:real^3->bool) SUBSET delta1` THEN
      UNDISCH_TAC `~(j1:real^3->bool = {})` THEN SET_TAC[];
      UNDISCH_TAC `surface_boundary cc' = surface_boundary cc DIFF (J:real^3->bool)` THEN
      UNDISCH_TAC `surface_boundary cc = (C:real^3->bool) INTER KK` THEN
      UNDISCH_TAC `(C':real^3->bool) INTER KK = C INTER KK DIFF J` THEN
      MESON_TAC[];
      UNDISCH_TAC `(C:real^3->bool) INTER KK SUBSET
                   frontier ((s2:int->real^3->bool) (&2 * i')) UNION
                   frontier (s2 (&2 * i' + &2))` THEN
      UNDISCH_TAC `(C':real^3->bool) INTER KK = C INTER KK DIFF J` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(i' IN lev
     ==> !jj. jj IN components ((C':real^3->bool) INTER frontier (s2 (&2 * i')))
              ==> moi_s32_ess s2 (&2 * i') jj) /\
    ((i' + &1) IN lev
     ==> !jj. jj IN components (C' INTER frontier (s2 (&2 * i' + &2)))
              ==> moi_s32_ess s2 (&2 * i' + &2) jj)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(i':int) IN lev`) o check (fun th ->
        is_imp(concl th) && lhand(concl th) = `(i':int) IN lev`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "trq" (MP_TAC o SPEC `frontier ((s2:int->real^3->bool) (&2 * i'))`) THEN
      ANTS_TAC THENL
       [USE_THEN "tk" (fun th -> REWRITE_TAC[th]) THEN ASM_CASES_TAC `i':int = i` THENL
         [DISJ1_TAC THEN UNDISCH_TAC `i':int = i` THEN DISCH_THEN SUBST1_TAC THEN
          FIRST_ASSUM ACCEPT_TAC;
          DISJ2_TAC THEN USE_THEN "jdis" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(i' + &1:int) IN lev`) o check (fun th ->
        is_imp(concl th) && lhand(concl th) = `(i' + &1:int) IN lev`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "trq" (MP_TAC o SPEC `frontier ((s2:int->real^3->bool) (&2 * i' + &2))`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[INT_ARITH `&2 * i' + &2 = &2 * (i' + &1):int`] THEN
          USE_THEN "tk" (fun th -> REWRITE_TAC[th]);
          ALL_TAC] THEN
        ASM_CASES_TAC `i':int = i - &1` THENL
         [DISJ1_TAC THEN
          SUBGOAL_THEN `&2 * i' + &2 = &2 * i:int` SUBST1_TAC THENL
           [UNDISCH_TAC `i':int = i - &1` THEN INT_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
          DISJ2_TAC THEN
          REWRITE_TAC[INT_ARITH `&2 * i' + &2 = &2 * (i' + &1):int`] THEN
          USE_THEN "jdis" MATCH_MP_TAC THEN
          UNDISCH_TAC `~(i':int = i - &1)` THEN INT_ARITH_TAC];
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* the four conclusions                                                   *)
  (* -------------------------------------------------------------------- *)
  REPEAT CONJ_TAC THENL
   [(* pairwise disjoint *)
    REWRITE_TAC[PAIRWISE_INSERT] THEN CONJ_TAC THENL
     [X_GEN_TAC `c:real^3->bool` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      SUBGOAL_THEN `DISJOINT (C:real^3->bool) c /\ (c:real^3->bool) SUBSET cs`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "pw" (MP_TAC o SPECL [`C:real^3->bool`; `c:real^3->bool`] o
            REWRITE_RULE[pairwise]) THEN
          ASM_MESON_TAC[];
          UNDISCH_TAC `UNIONS fam SUBSET (cs:real^3->bool)` THEN
          UNDISCH_TAC `(c:real^3->bool) IN fam` THEN SET_TAC[]];
        ALL_TAC] THEN
      EXPAND_TAC "C'" THEN
      UNDISCH_TAC `delta1 INTER (cs:real^3->bool) = j1` THEN
      UNDISCH_TAC `(j1:real^3->bool) SUBSET a1` THEN
      UNDISCH_TAC `(a1:real^3->bool) SUBSET C` THEN
      UNDISCH_TAC `DISJOINT (C:real^3->bool) c` THEN
      UNDISCH_TAC `(c:real^3->bool) SUBSET cs` THEN SET_TAC[];
      MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC `fam:(real^3->bool)->bool` THEN
      USE_THEN "pw" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[]];
    (* members *)
    X_GEN_TAC `c:real^3->bool` THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THENL
     [MAP_EVERY EXISTS_TAC [`i':int`; `cc':(real^3->bool)->bool`] THEN ASM_REWRITE_TAC[];
      USE_THEN "mem" (ACCEPT_TAC o C MP (ASSUME `(c:real^3->bool) IN fam`) o
                      SPEC `c:real^3->bool`)];
    (* finitely many per level *)
    X_GEN_TAC `k:int` THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(C':real^3->bool) INSERT {c | c IN fam /\ c SUBSET moi_s32_lvl g dd k}` THEN
    USE_THEN "fin" (fun th -> REWRITE_TAC[FINITE_INSERT; th]) THEN SET_TAC[];
    (* closed and separating *)
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    (* iness *)
    REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; moi_s3lv_iness; IN_ELIM_THM; IN_INSERT; IN_DELETE] THEN
      X_GEN_TAC `jj:real^3->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      ASM_CASES_TAC `c:real^3->bool = C'` THENL
       [EXISTS_TAC `C:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(jj:real^3->bool) IN
                     components (c INTER frontier ((s2:int->real^3->bool) (&2 * i)))` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "trq" (MP_TAC o SPEC `frontier ((s2:int->real^3->bool) (&2 * i))`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
        EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
      GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN REWRITE_TAC[NOT_FORALL_THM] THEN
      EXISTS_TAC `J:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[moi_s3lv_iness; IN_ELIM_THM; IN_INSERT; IN_DELETE] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `c:real^3->bool` THEN
      ASM_CASES_TAC `c:real^3->bool = C'` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`(C:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                       `J:real^3->bool`] MOI_S3LV_COMPONENTS_DIFF) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(C':real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i)) =
                      (C INTER frontier (s2 (&2 * i))) DIFF J` SUBST_ALL_TAC THENL
         [UNDISCH_TAC `(C':real^3->bool) INTER KK = C INTER KK DIFF J` THEN
          UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET KK` THEN SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(J:real^3->bool) IN
                     components ((C INTER frontier ((s2:int->real^3->bool) (&2 * i))) DIFF J)` THEN
        SET_TAC[];
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `DISJOINT (C:real^3->bool) c` ASSUME_TAC THENL
         [USE_THEN "pw" (MP_TAC o SPECL [`C:real^3->bool`; `c:real^3->bool`] o
            REWRITE_RULE[pairwise]) THEN
          ASM_MESON_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`(c:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))`;
                       `J:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `DISJOINT (C:real^3->bool) c` THEN
        UNDISCH_TAC `(J:real^3->bool) SUBSET C` THEN UNDISCH_TAC `~(J:real^3->bool = {})` THEN
        SET_TAC[]]];
    (* the set outside R *)
    UNDISCH_TAC `c' DIFF U = (cs:real^3->bool) DIFF U` THEN
    USE_THEN "cs" SUBST1_TAC THEN
    UNDISCH_TAC `(U:real^3->bool) SUBSET interior X` THEN SET_TAC[];
    (* the members missing R *)
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `c:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; IN_DELETE] THEN
    SUBGOAL_THEN `~DISJOINT (C':real^3->bool) (interior X) /\
                  ~DISJOINT (C:real^3->bool) (interior X)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "C'" THEN
        UNDISCH_TAC `(j1:real^3->bool) SUBSET delta1` THEN
        UNDISCH_TAC `~(j1:real^3->bool = {})` THEN
        UNDISCH_TAC `(j1:real^3->bool) SUBSET a1` THEN
        UNDISCH_TAC `(a1:real^3->bool) SUBSET (D UNION A) INTER U` THEN
        UNDISCH_TAC `(U:real^3->bool) SUBSET interior X` THEN SET_TAC[];
        UNDISCH_TAC `(J:real^3->bool) SUBSET C` THEN
        UNDISCH_TAC `(J:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
        UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET interior X` THEN
        UNDISCH_TAC `~(J:real^3->bool = {})` THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `c:real^3->bool = C'` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `c:real^3->bool = C` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 20: one cap step for moi_s32_state3 (Moise p.226, Step 1).          *)
(* The inmost inessential polygon J on T with its disk D and member C; the  *)
(* inner collar A of J in C (boundary collar, hypothesis moi_s3lv_collar2)  *)
(* gives d1 = D UNION A; the bicollar of J in the orientable torus T        *)
(* (MOI_FND_BICOLLAR_CURVE_2) gives the outer disk d2; the open U around D  *)
(* inside R; Moise 30.3 caps; the new member is a surface (NEW_SURFACE)    *)
(* and the new family a state3 with one inessential polygon fewer          *)
(* (NEW_STATE).                                                              *)
(* ========================================================================= *)

let MOI_S3LV_SEP_FACTS = prove
 (`!(m:real^N->bool) c h k.
     separates_in m c h k
     ==> h SUBSET m /\ k SUBSET m /\ DISJOINT h k /\ DISJOINT c (h UNION k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separates_in] THEN STRIP_TAC THEN
  ASM SET_TAC[]);;

let MOI_S3LV_T_BICOLLAR = prove
 (mk_imp(moi_n3 MOI_FND_BICOLLAR_CURVE_2,
  `!(s:real^3->bool) j.
     pl_solid_torus s /\ pl_sphere 1 j /\ j SUBSET frontier s
     ==> ?w (p:real^(3,1)finite_sum->real^3) q.
           moi_s26_bicollar j w p q /\ w SUBSET frontier s /\
           j SUBSET (subtopology euclidean (frontier s)) interior_of w`),
  DISCH_THEN(LABEL_TAC "bic") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3LV_T_SURFACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `j:real^3->bool` (INST_TYPE [`:3`,`:N`] POLYGON_COMPLEX)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `surface_boundary (t:(real^3->bool)->bool) = {}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:(real^3->bool)->bool` (INST_TYPE [`:3`,`:N`] SURF_LOCAL)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S3LV_LF_SC THEN ASM_MESON_TAC[combinatorial_manifold];
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISJ1_TAC THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN ASM_CASES_TAC `(y:real^3) IN frontier s` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "bic" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                                  `frontier s:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIFF_EMPTY; SUBSET_REFL] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
    ASM_SIMP_TAC[MOI_S8TA_CM_CMB];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s26_bicollar] THEN MESON_TAC[]);;

let MOI_S3LV_STEP3 = prove
 (mk_imp(list_mk_conj [moi_s3lv_collar2; `MOISE_303_STATEMENT`;
                       moi_n3 MOI_FND_BICOLLAR_CURVE_2],
  `!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state3 g dd s2 lev fam /\ ~(moi_s3lv_iness s2 i fam = {})
     ==> ?fam1. moi_s32_state3 g dd s2 lev fam1 /\
                moi_s3lv_iness s2 i fam1 PSUBSET moi_s3lv_iness s2 i fam /\
                moi_s32_set g s2 fam1 DIFF
                  interior (IMAGE g (revolution (dd (&2 * i)))) =
                moi_s32_set g s2 fam DIFF
                  interior (IMAGE g (revolution (dd (&2 * i)))) /\
                {c | c IN fam1 /\
                     DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
                {c | c IN fam /\
                     DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "col") (CONJUNCTS_THEN2 (LABEL_TAC "m303")
    (LABEL_TAC "bic"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s32_state (g:real^3->real^3) dd s2 lev fam` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3S6_STATE3 THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* the inmost inessential polygon J, its disk D, its member C           *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`] MOI_S3LV_INMOST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^3->bool` (X_CHOOSE_THEN `D:real^3->bool`
    (X_CHOOSE_THEN `C:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "inm"))))))))) THEN
  MP_TAC(CONJUNCT1(CONJUNCT2(REWRITE_RULE[moi_s32_state3]
    (ASSUME `moi_s32_state3 (g:real^3->real^3) dd s2 lev fam`)))) THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(C:real^3->bool) IN fam`) o SPEC `C:real^3->bool`) THEN
  DISCH_THEN(X_CHOOSE_THEN `i':int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean (moi_s32_open g))
              (moi_s32_set (g:real^3->real^3) s2 fam) /\
    separates_in (moi_s32_open g) (moi_s32_set g s2 fam) {g moi_s32_qlo} {g moi_s32_qhi}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `moi_s32_state3 (g:real^3->real^3) dd s2 lev fam`) THEN
    REWRITE_TAC[moi_s32_state3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_R_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3LV_M_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `(s2:int->real^3->bool) (&2 * i)` MOI_S3LV_T_SURFACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`moi_s32_open (g:real^3->real^3)`; `moi_s32_set (g:real^3->real^3) s2 fam`;
                 `{(g:real^3->real^3) moi_s32_qlo}`; `{(g:real^3->real^3) moi_s32_qhi}`]
                MOI_S3LV_SEP_FACTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* J on the boundary of C                                                *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i':int`;
                `C:real^3->bool`; `cc:(real^3->bool)->bool`] MOI_S3LV_TRACE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "trs") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "trj"))) THEN
  SUBGOAL_THEN `(J:real^3->bool) IN components (surface_boundary cc)` ASSUME_TAC THENL
   [USE_THEN "trs" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "trj" (MP_TAC o SPEC `J:real^3->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(J:real^3->bool = {})` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_NONEMPTY THEN
    EXISTS_TAC `(C:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `D:real^3->bool`; `J:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(C:real^3->bool) INTER D = J` ASSUME_TAC THENL
   [USE_THEN "inm" (MP_TAC o C MP (ASSUME `(C:real^3->bool) IN fam`) o SPEC `C:real^3->bool`) THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET C` THEN UNDISCH_TAC `(J:real^3->bool) SUBSET D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* sets of the barrier                                                   *)
  (* -------------------------------------------------------------------- *)
  SUBGOAL_THEN
   `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2 /\
    moi_s32_evens s2 SUBSET moi_s32_set (g:real^3->real^3) s2 fam /\
    (C:real^3->bool) SUBSET moi_s32_set g s2 fam`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_s32_evens s2 INTER IMAGE (g:real^3->real^3)
                     (revolution ((dd:int->real^3->bool) (&2 * i))) =
                   frontier ((s2:int->real^3->bool) (&2 * i))` THEN SET_TAC[];
      REWRITE_TAC[moi_s32_set] THEN SET_TAC[];
      REWRITE_TAC[moi_s32_set] THEN UNDISCH_TAC `(C:real^3->bool) IN fam` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* the inner collar A of J in C and the disk d1 = D UNION A             *)
  (* -------------------------------------------------------------------- *)
  USE_THEN "col" (fun th -> MP_TAC(SPECL [`cc:(real^3->bool)->bool`; `J:real^3->bool`]
    (MP MOI_S3LV_INNER_COLLAR th))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3->bool` (X_CHOOSE_THEN `J1:real^3->bool`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `UNIONS (cc:(real^3->bool)->bool) = C`]))) THEN
  MP_TAC(ISPECL [`A:real^3->bool`; `J:real^3->bool`; `J1:real^3->bool`] MOI_S3LV_ANN_ENDS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((D:real^3->bool) UNION A) J1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3LV_DISK_ANN THEN EXISTS_TAC `J:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `(C:real^3->bool) INTER D = J` THEN UNDISCH_TAC `(A:real^3->bool) SUBSET C` THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET D` THEN UNDISCH_TAC `(J:real^3->bool) SUBSET A` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* the outer disk d2 in T                                                *)
  (* -------------------------------------------------------------------- *)
  USE_THEN "bic" (fun th -> MP_TAC(SPECL [`(s2:int->real^3->bool) (&2 * i)`; `J:real^3->bool`]
    (MP MOI_S3LV_T_BICOLLAR th))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (X_CHOOSE_THEN `p:real^(3,1)finite_sum->real^3`
    (X_CHOOSE_THEN `q:real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i))`; `D:real^3->bool`;
                 `J:real^3->bool`; `w:real^3->bool`; `p:real^(3,1)finite_sum->real^3`;
                 `q:real^3->real^(3,1)finite_sum`] MOI_S3LV_OUTER_DISK) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `b2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(d2:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(d2:real^3->bool) SUBSET D UNION w` THEN
    UNDISCH_TAC `(D:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* the open U around D                                                   *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`; `C:real^3->bool`;
                `cc:(real^3->bool)->bool`; `J:real^3->bool`; `D:real^3->bool`;
                `A:real^3->bool`; `d2:real^3->bool`] MOI_S3LV_NBHD_U) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* -------------------------------------------------------------------- *)
  (* the hypotheses of 30.3                                                *)
  (* -------------------------------------------------------------------- *)
  SUBGOAL_THEN
   `closed_in (subtopology euclidean (moi_s32_open g)) {(g:real^3->real^3) moi_s32_qlo} /\
    closed_in (subtopology euclidean (moi_s32_open g)) {(g:real^3->real^3) moi_s32_qhi}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_SING] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((D:real^3->bool) UNION A) INTER d2 = D` ASSUME_TAC THENL
   [UNDISCH_TAC `(D:real^3->bool) SUBSET d2` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2` THEN
    UNDISCH_TAC `(A:real^3->bool) SUBSET C` THEN
    UNDISCH_TAC `(A:real^3->bool) INTER surface_boundary cc = J` THEN
    UNDISCH_TAC `surface_boundary (cc:(real^3->bool)->bool) = C INTER moi_s32_evens s2` THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET D` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((D:real^3->bool) UNION A) UNION d2 SUBSET moi_s32_set (g:real^3->real^3) s2 fam`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(D:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2` THEN
    UNDISCH_TAC `moi_s32_evens s2 SUBSET moi_s32_set (g:real^3->real^3) s2 fam` THEN
    UNDISCH_TAC `(A:real^3->bool) SUBSET C` THEN
    UNDISCH_TAC `(C:real^3->bool) SUBSET moi_s32_set (g:real^3->real^3) s2 fam` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(D:real^3->bool) SUBSET
    (subtopology euclidean (moi_s32_set (g:real^3->real^3) s2 fam)) interior_of
    ((D UNION A) UNION d2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s32_set (g:real^3->real^3) s2 fam INTER U` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(D:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2` THEN
      UNDISCH_TAC `moi_s32_evens s2 SUBSET moi_s32_set (g:real^3->real^3) s2 fam` THEN
      UNDISCH_TAC `(D:real^3->bool) SUBSET U` THEN SET_TAC[];
      MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
       [UNDISCH_TAC `(U:real^3->bool) INTER moi_s32_set (g:real^3->real^3) s2 fam SUBSET
                     ((D UNION A) UNION d2)` THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (D:real^3->bool) J1 /\ DISJOINT (D:real^3->bool) b2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(J1:real^3->bool) SUBSET A` THEN UNDISCH_TAC `(A:real^3->bool) SUBSET C` THEN
      UNDISCH_TAC `(C:real^3->bool) INTER D = J` THEN
      UNDISCH_TAC `DISJOINT (J:real^3->bool) J1` THEN SET_TAC[];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(U:real^3->bool) SUBSET moi_s32_open g /\
    DISJOINT U ({(g:real^3->real^3) moi_s32_qlo} UNION {g moi_s32_qhi})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))`
      INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(U:real^3->bool) SUBSET
                 interior (IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i))))` THEN
    UNDISCH_TAC `interior (IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i))))
                 SUBSET moi_s32_open g` THEN
    UNDISCH_TAC `~((g:real^3->real^3) moi_s32_qlo IN
                   IMAGE g (revolution ((dd:int->real^3->bool) (&2 * i))))` THEN
    UNDISCH_TAC `~((g:real^3->real^3) moi_s32_qhi IN
                   IMAGE g (revolution ((dd:int->real^3->bool) (&2 * i))))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* Moise 30.3                                                            *)
  (* -------------------------------------------------------------------- *)
  USE_THEN "m303" (MP_TAC o SPECL
    [`moi_s32_open (g:real^3->real^3)`; `{(g:real^3->real^3) moi_s32_qlo}`;
     `{(g:real^3->real^3) moi_s32_qhi}`; `moi_s32_set (g:real^3->real^3) s2 fam`;
     `D:real^3->bool`; `J:real^3->bool`; `(D:real^3->bool) UNION A`; `J1:real^3->bool`;
     `d2:real^3->bool`; `b2:real^3->bool`; `U:real^3->bool`] o
    REWRITE_RULE[MOISE_303_STATEMENT]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` (X_CHOOSE_THEN `a1:real^3->bool`
    (X_CHOOSE_THEN `j1:real^3->bool` (X_CHOOSE_THEN `delta1:real^3->bool`
    STRIP_ASSUME_TAC)))) THEN
  (* -------------------------------------------------------------------- *)
  (* the new member surface                                                *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(ISPECL [`a1:real^3->bool`; `J:real^3->bool`; `j1:real^3->bool`] MOI_S3LV_ANN_ENDS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`2`; `delta1:real^3->bool`; `j1:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(a1:real^3->bool) SUBSET A UNION D /\ (delta1:real^3->bool) INTER C = j1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(a1:real^3->bool) SUBSET (D UNION A) INTER U` THEN SET_TAC[];
      UNDISCH_TAC `(a1:real^3->bool) SUBSET (D UNION A) INTER U` THEN
      UNDISCH_TAC `(a1:real^3->bool) INTER D = J` THEN
      UNDISCH_TAC `DISJOINT (J:real^3->bool) j1` THEN
      UNDISCH_TAC `(j1:real^3->bool) SUBSET a1` THEN
      UNDISCH_TAC `(A:real^3->bool) SUBSET C` THEN
      UNDISCH_TAC `(delta1:real^3->bool) INTER moi_s32_set (g:real^3->real^3) s2 fam = j1` THEN
      UNDISCH_TAC `(C:real^3->bool) SUBSET moi_s32_set (g:real^3->real^3) s2 fam` THEN
      UNDISCH_TAC `(j1:real^3->bool) SUBSET delta1` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `J:real^3->bool`; `D:real^3->bool`;
                 `A:real^3->bool`; `a1:real^3->bool`; `j1:real^3->bool`;
                 `delta1:real^3->bool`] MOI_S3LV_NEW_SURFACE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASSUME `UNIONS (cc:(real^3->bool)->bool) = C`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc':(real^3->bool)->bool`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `UNIONS (cc:(real^3->bool)->bool) = C`])) THEN
  SUBGOAL_THEN `connected (UNIONS (cc':(real^3->bool)->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `connected (C:real^3->bool) ==> connected (UNIONS (cc':(real^3->bool)->bool))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* the new state                                                         *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                `fam:(real^3->bool)->bool`; `i:int`; `C:real^3->bool`; `i':int`;
                `cc:(real^3->bool)->bool`; `cc':(real^3->bool)->bool`; `J:real^3->bool`;
                `D:real^3->bool`; `A:real^3->bool`; `U:real^3->bool`; `c':real^3->bool`;
                `a1:real^3->bool`; `j1:real^3->bool`; `delta1:real^3->bool`]
               MOI_S3LV_NEW_STATE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(((C:real^3->bool) DIFF (a1 DIFF j1)) UNION delta1) INSERT (fam DELETE C)` THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* Part 21: LEVEL_3 from the boundary collar.  Induction on the finite      *)
(* set of inessential polygons on T (MOI_S3LV_INDUCT with the invariant     *)
(* moi_s32_state3 at lev and the cap step MOI_S3LV_STEP3); when none is     *)
(* left the state3 holds at i INSERT lev (MOI_S3LV_DONE3).  The 2D boundary *)
(* collar moi_s3lv_collar2 (MOI_FCB_BOUNDARY_COLLAR_2 at :3) is the         *)
(* only extra hypothesis; MOISE_268 and SURFACE_TRIANG are not used.        *)
(* ========================================================================= *)

let MOI_S3LV_LEVEL_3_COLLAR = prove
 (mk_imp(moi_s3lv_collar2, MOI_S32_LEVEL_3),
  DISCH_THEN(LABEL_TAC "col") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m303") (CONJUNCTS_THEN2 (LABEL_TAC "m268")
    (CONJUNCTS_THEN2 (LABEL_TAC "bic") (LABEL_TAC "tri")))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s32_state3 (g:real^3->real^3) dd s2 lev`; `g:real^3->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3LV_INDUCT) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `fam0:(real^3->bool)->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(MP MOI_S3LV_STEP3
      (CONJ (ASSUME moi_s3lv_collar2) (CONJ (ASSUME `MOISE_303_STATEMENT`)
                                            (ASSUME (moi_n3 MOI_FND_BICOLLAR_CURVE_2))))) THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `fam:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3LV_INESS_FINITE THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`; `lev:int->bool`] THEN
    ASM_SIMP_TAC[MOI_S3S6_STATE3];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fam':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `fam':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3LV_DONE3 THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 22: the theorem LEVEL_3.  The 2D boundary collar moi_s3lv_collar2   *)
(* is MOI_FCB_BOUNDARY_COLLAR_2 (pc_moi_fnd_bcollar) at N = 3, so           *)
(* MOI_S3LV_LEVEL_3_COLLAR gives LEVEL_3 without hypotheses.                *)
(* ========================================================================= *)

let LEVEL_3 = prove
 (MOI_S32_LEVEL_3,
  MATCH_MP_TAC MOI_S3LV_LEVEL_3_COLLAR THEN
  ACCEPT_TAC(INST_TYPE [`:3`,`:N`] MOI_FCB_BOUNDARY_COLLAR_2));;

