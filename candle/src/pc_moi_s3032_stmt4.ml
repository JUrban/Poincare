(* ========================================================================= *)
(* pc_moi_s3032_stmt4: HANDLES restated with a vertex condition.             *)
(* MOI_S32_HANDLES (pc_moi_s3032_stmt.ml) is false: nothing keeps an end of  *)
(* an edge out of the slab of that edge.  Counterexample: a single edge      *)
(* [a,b] with a of degree 1, the chart point of a in the lower half slab     *)
(* near the axis, and ee e the graph of a PL function lying below that point *)
(* and the half edge from a to the midpoint (meeting the graph only at the   *)
(* midpoint); all edge facts hold, h a lies in uu2 e, so the pieces of a and *)
(* b coincide and the vertex clause of 32.3 fails.  MOI_S32_HANDLES_2 adds   *)
(* to the inner antecedent the vertex condition moi_s3s4_vsep: nb v contains *)
(* the image of no other vertex.  Then the slab of an edge, which lies in g  *)
(* (av e) INTER g (bv e), contains no vertex of the graph.                   *)
(*   MOI_S3S4_HANDLES_WEAKER : |- MOI_S32_HANDLES ==> MOI_S32_HANDLES_2;   *)
(*   MOI_S3S4_323_RESTR: the 32.3 glue of pc_moi_s3032_stmt.ml (section    *)
(*   6.9) with HANDLES_2, for neighbourhoods with the vertex condition;     *)
(*   MOI_S3S4_323_SHRINK: the general case, applying RESTR to nb1 v = nb v  *)
(*   minus the images of the other vertices (open, contains h(C_v) by       *)
(*   GRAPH_TUBE, and c v SUBSET nb1 v SUBSET nb v);                         *)
(*   MOI_S3S4_323_CORE, MOI_S3S4_323 (full form; used in place of            *)
(*   MOI_STD_323).                                                           *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_s3s4_vsep =
 `!v w. {v} IN (l:(real^3->bool)->bool) /\ {w} IN l /\ ~(v = w)
        ==> ~((h:real^3->real^3) w IN (nb:real^3->real^3->bool) v)`;;

let MOI_S32_HANDLES_2 =
  let vs,hyp,ev,cv,b2 = moi_s32_323_parts in
  let eev = `ee:(real^3->bool)->real^3->bool` in
  let concl1 = rhs(concl(TOP_DEPTH_CONV BETA_CONV
                 (vsubst [eev,ev; moi_s32_pieces,cv] b2))) in
  let extra = [`(!v. {v} IN l ==> (g:real^3->real^3->bool) v =
                                  {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v})`;
               `moi_s35_charts t l g av bv (psi:(real^3->bool)->real^3->real^3)`;
               moi_s32_edge_facts; moi_s3s4_vsep] in
  let allv = vs @ [`g:real^3->real^3->bool`; `av:(real^3->bool)->real^3`;
                   `bv:(real^3->bool)->real^3`;
                   `psi:(real^3->bool)->real^3->real^3`;
                   `ww:(real^3->bool)->real^3->bool`; eev;
                   `uu1:(real^3->bool)->real^3->bool`;
                   `uu2:(real^3->bool)->real^3->bool`] in
  mk_imp(list_mk_conj [moi_n3 MOI_FND_GRAPH_TUBE; MOI_FND_GRAPH_TUBE_FRONTIER_3;
                       moi_n3 MOI_S35_TUBE_TRIPLE; moi_n3 MOI_FND_DERIVED_NBHD_BASIC],
         list_mk_forall(allv, mk_imp(list_mk_conj (hyp :: extra), concl1)));;

(* The text check: HANDLES_2 is HANDLES with exactly one more conjunct, the *)
(* vertex condition, at the end of the inner antecedent (conjuncts compared *)
(* up to alpha: separately parsed set comprehensions differ in the name of  *)
(* their generated bound variable).                                         *)

let moi_s3s4_text_ok =
  let a2,b2 = dest_imp MOI_S32_HANDLES_2 and a1,b1 = dest_imp MOI_S32_HANDLES in
  let vs2,i2 = strip_forall b2 and vs1,i1 = strip_forall b1 in
  let h2,c2 = dest_imp i2 and h1,c1 = dest_imp i1 in
  let l1 = conjuncts h1 @ [moi_s3s4_vsep] and l2 = conjuncts h2 in
  aconv a1 a2 && vs1 = vs2 && aconv c1 c2 &&
  length l1 = length l2 && forall2 aconv l1 l2 &&
  type_of MOI_S32_HANDLES_2 = bool_ty && frees MOI_S32_HANDLES_2 = [];;

if not moi_s3s4_text_ok then failwith "moi_s3s4_text_ok";;

let MOI_S3S4_HANDLES_WEAKER = prove
 (mk_imp(MOI_S32_HANDLES,MOI_S32_HANDLES_2),
  DISCH_THEN(fun th -> DISCH_THEN(fun a -> MP_TAC(MP th a))) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_THEN(fun a -> MATCH_MP_TAC th THEN MP_TAC a)) THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 32.3 glue with HANDLES_2 for neighbourhoods with the vertex          *)
(* condition: the proof of MOI_STD_323_CORE (pc_moi_s3032_stmt.ml, section *)
(* 6.9) with the vertex condition passed to HANDLES_2 (kept in the goal    *)
(* until HANDLES_2 is applied, and HANDLES_2 itself bound by a closure, not *)
(* an assumption, so the MESON calls do not see its large clause form).     *)
(* ------------------------------------------------------------------------- *)

let moi_s3s4_restr =
  let tm = rhs(concl MOISE_323_STATEMENT) in
  let vs,body = strip_forall tm in
  let hyp,cncl = dest_imp body in
  list_mk_forall(vs, mk_imp(mk_conj(hyp, moi_s3s4_vsep), cncl));;

let moi_s3s4_ants =
  [`MOISE_322_CELLS_STATEMENT`; moi_n3 MOI_FND_GRAPH_TUBE;
   moi_std_csq (moi_n3 MOI_S35_CHARTS); moi_std_csq MOI_S32_SLAB_W;
   moi_std_csq MOI_S32_HANDLES_2];;

let MOI_S3S4_323_RESTR = prove
 (mk_imp(list_mk_conj moi_s3s4_ants, moi_s3s4_restr),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "322") (CONJUNCTS_THEN2 (LABEL_TAC "tube")
   (CONJUNCTS_THEN2 (LABEL_TAC "charts") (CONJUNCTS_THEN2 (LABEL_TAC "slab")
    (fun handles ->
  REMOVE_THEN "322" (LABEL_TAC "322" o REWRITE_RULE[MOISE_322_CELLS_STATEMENT]) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `nb:real^3->real^3->bool`] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN ASSUME_TAC(CONJUNCT1 th) THEN
                       STRIP_ASSUME_TAC(CONJUNCT1 th)) THEN
  USE_THEN "tube" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "tv")
    (CONJUNCTS_THEN2 (LABEL_TAC "te") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `!v. {v} IN l ==> derived_dual_cell t l v SUBSET UNIONS (t:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "tv" (MP_TAC o CONJUNCT1 o C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3`) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "charts" (MP_TAC o BETA_RULE o SPECL
    [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
     `\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v}`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `derived_dual_cell t l v SUBSET UNIONS (t:(real^3->bool)->bool) /\
                    IMAGE (h:real^3->real^3) (derived_dual_cell t l v) SUBSET nb v`
      MP_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `av:(real^3->bool)->real^3`
    (X_CHOOSE_THEN `bv:(real^3->bool)->real^3`
      (X_CHOOSE_THEN `psi:(real^3->bool)->real^3->real^3` ASSUME_TAC))) THEN
  SUBGOAL_THEN moi_std_edge_ex MP_TAC THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ASSUME `moi_s35_charts t l
                     (\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v})
                     av bv psi`) THEN
    REWRITE_TAC[moi_s35_charts] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `moi_s35_edge l (e:real^3->bool)`) o
               SPEC `e:real^3->bool` o CONJUNCT1) THEN
    STRIP_TAC THEN
    USE_THEN "te" (MP_TAC o SPECL [`(av:(real^3->bool)->real^3) e`;
                                   `(bv:(real^3->bool)->real^3) e`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `moi_s35_edge l (e:real^3->bool)` THEN REWRITE_TAC[moi_s35_edge] THEN
      UNDISCH_TAC `e = segment[(av:(real^3->bool)->real^3) e,(bv:(real^3->bool)->real^3) e]` THEN
      MESON_TAC[];
      STRIP_TAC] THEN
    USE_THEN "slab" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v}`;
      `av:(real^3->bool)->real^3`; `bv:(real^3->bool)->real^3`;
      `psi:(real^3->bool)->real^3->real^3`; `e:real^3->bool`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "322" (MP_TAC o SPECL
      [`IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo`;
       `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_hi`;
       `derived_dual_cell t l ((av:(real^3->bool)->real^3) e) INTER
        derived_dual_cell t l ((bv:(real^3->bool)->real^3) e)`;
       `derived_dual_cell t l ((av:(real^3->bool)->real^3) e) INTER
        derived_dual_cell t l ((bv:(real^3->bool)->real^3) e) INTER derived_frontier t l`;
       `midpoint((av:(real^3->bool)->real^3) e,(bv:(real^3->bool)->real^3) e)`;
       `(psi:(real^3->bool)->real^3->real^3) e moi_s32_slo`;
       `(psi:(real^3->bool)->real^3->real^3) e moi_s32_shi`;
       `h:real^3->real^3`; `w:real^3->bool`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo UNION
                     IMAGE (psi e) moi_s32_slab_hi SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
        UNDISCH_TAC `!x y. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^3->real^3) x = h y
                           ==> x = y` THEN
        REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e0:real^3->bool` (X_CHOOSE_THEN `a0:real^3->bool`
      (X_CHOOSE_THEN `b0:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w:real^3->bool`; `e0:real^3->bool`; `a0:real^3->bool`;
                          `b0:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ww:(real^3->bool)->real^3->bool`
    (X_CHOOSE_THEN `ee:(real^3->bool)->real^3->bool`
      (X_CHOOSE_THEN `uu1:(real^3->bool)->real^3->bool`
        (X_CHOOSE_THEN `uu2:(real^3->bool)->real^3->bool` ASSUME_TAC)))) THEN
  DISCH_TAC THEN
  MP_TAC(BETA_RULE(SPECL
    [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
     `nb:real^3->real^3->bool`;
     `\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v}`;
     `av:(real^3->bool)->real^3`; `bv:(real^3->bool)->real^3`;
     `psi:(real^3->bool)->real^3->real^3`; `ww:(real^3->bool)->real^3->bool`;
     `ee:(real^3->bool)->real^3->bool`; `uu1:(real^3->bool)->real^3->bool`;
     `uu2:(real^3->bool)->real^3->bool`] handles)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ee:(real^3->bool)->real^3->bool`; moi_s32_pieces] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN FIRST_ASSUM ACCEPT_TAC))))));;

(* ------------------------------------------------------------------------- *)
(* The general case.  For any nb, nb1 v = nb v minus the images of the      *)
(* other vertices is open (finitely many vertices), contains h(C_v) (C_v    *)
(* contains no other vertex of t, h is injective on UNIONS t) and has the  *)
(* vertex condition; RESTR for nb1 gives the pieces, inside nb1 v SUBSET    *)
(* nb v.  The facts about nb1 are a separate lemma, proved in a small       *)
(* context.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3S4_NB1_FACTS = prove
 (mk_imp(moi_n3 MOI_FND_GRAPH_TUBE,
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) (nb:real^3->real^3->bool).
     FINITE t /\ graph_in_complex t l /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     (!v. {v} IN l ==> open (nb v) /\ IMAGE h (derived_dual_cell t l v) SUBSET nb v)
     ==> (!v. {v} IN l
              ==> open (nb v DIFF IMAGE h {u | {u} IN l /\ ~(u = v)}) /\
                  IMAGE h (derived_dual_cell t l v) SUBSET
                  nb v DIFF IMAGE h {u | {u} IN l /\ ~(u = v)}) /\
         (!v w. {v} IN l /\ {w} IN l /\ ~(v = w)
                ==> ~(h w IN nb v DIFF IMAGE h {u | {u} IN l /\ ~(u = v)}))`),
  DISCH_THEN(fun tube ->
    MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                         `h:real^3->real^3`; `nb:real^3->real^3->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] tube)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `l SUBSET (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^3->bool)->bool) l` THEN
    SIMP_TAC[graph_in_complex; simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. {v} IN l ==> derived_dual_cell t l v SUBSET UNIONS t`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `derived_dual_cell:((real^3->bool)->bool)->((real^3->bool)->bool)->real^3->real^3->bool`)) (concl th) &&
                       can (find_term ((=) `pl_cell_with_boundary:num->(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w:real^3. {v} IN l /\ {w} IN l /\ ~(w = v)
                             ==> ~(w IN derived_dual_cell t l v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
                  C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `pl_cell_with_boundary:num->(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
    SUBGOAL_THEN `{w:real^3} IN t` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `pl_cell_with_boundary:num->(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
  SUBGOAL_THEN `FINITE {w:real^3 | {w} IN l}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^3. {w}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [SET_TAC[]; ASM_MESON_TAC[FINITE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v u x:real^3. {v} IN l /\ {u} IN l /\ ~(u = v) /\
                               x IN derived_dual_cell t l v
                               ==> ~((h:real^3->real^3) x = h u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN UNIONS t /\ (u:real^3) IN UNIONS t` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET];
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^3}` THEN
        REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[SUBSET]];
      ALL_TAC] THEN
    SUBGOAL_THEN `x:real^3 = u` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC FINITE_IMP_CLOSED THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{w:real^3 | {w} IN l}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      SUBGOAL_THEN `IMAGE (h:real^3->real^3) (derived_dual_cell t l v) SUBSET nb v`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `!v u x:real^3. {v} IN l /\ {u} IN l /\ ~(u = v) /\
                                  x IN derived_dual_cell t l v
                                  ==> ~((h:real^3->real^3) x = h u)` THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; FORALL_IN_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[]];
    REWRITE_TAC[IN_DIFF; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_S3S4_323_SHRINK = prove
 (mk_imp(moi_n3 MOI_FND_GRAPH_TUBE, mk_imp(moi_s3s4_restr, `MOISE_323_STATEMENT`)),
  DISCH_THEN(fun tube -> DISCH_THEN(fun restr ->
    REWRITE_TAC[MOISE_323_STATEMENT] THEN
    MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                         `h:real^3->real^3`; `nb:real^3->real^3->bool`] THEN
    DISCH_THEN(fun hyp -> STRIP_ASSUME_TAC hyp THEN
      MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                    `h:real^3->real^3`; `nb:real^3->real^3->bool`]
                   (MP MOI_S3S4_NB1_FACTS tube)) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      STRIP_TAC THEN
      MP_TAC(BETA_RULE(SPECL
        [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
         `\v:real^3. (nb:real^3->real^3->bool) v DIFF
                     IMAGE (h:real^3->real^3) {u | {u} IN l /\ ~(u = v)}`] restr))))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->real^3->bool`
    (X_CHOOSE_THEN `c:real^3->real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "cv") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  USE_THEN "cv" (MP_TAC o C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3`) THEN
  DISCH_THEN(fun th -> REPEAT CONJ_TAC THENL
    [ACCEPT_TAC(CONJUNCT1 th); ACCEPT_TAC(CONJUNCT1(CONJUNCT2 th));
     MP_TAC(CONJUNCT2(CONJUNCT2 th)) THEN SET_TAC[]]));;
(* The core glue with HANDLES_2 and its full form (the dependency closure    *)
(* computed as in pc_moi_s3032_stmt.ml section 6, with HANDLES_2 among the   *)
(* statements).                                                              *)

let MOI_S3S4_323_CORE = prove
 (mk_imp(list_mk_conj moi_s3s4_ants, `MOISE_323_STATEMENT`),
  DISCH_THEN(fun th ->
    MATCH_MP_TAC(MP MOI_S3S4_323_SHRINK (CONJUNCT1(CONJUNCT2 th))) THEN
    ACCEPT_TAC(MP MOI_S3S4_323_RESTR th)));;

let moi_s3s4_find_target a =
  if aconv (moi_std_csq MOI_S32_HANDLES_2) a then Some MOI_S32_HANDLES_2
  else moi_std_find_target a;;

let rec moi_s3s4_closure stop acc tms =
  match tms with
    [] -> acc
  | a::rest ->
      if exists (aconv a) stop || exists (aconv a) acc
      then moi_s3s4_closure stop acc rest else
      match moi_s3s4_find_target a with
        Some t ->
          if exists (aconv t) acc then moi_s3s4_closure stop acc rest else
          let ants = if is_imp t then conjuncts(fst(dest_imp t)) else [] in
          moi_s3s4_closure stop (t::acc) (ants @ rest)
      | None -> moi_s3s4_closure stop (a::acc) rest;;

let moi_s3s4_full core prod =
  let hyps = conjuncts(fst(dest_imp(concl core))) in
  let stop = if is_imp prod then conjuncts(fst(dest_imp prod)) else [] in
  mk_imp(list_mk_conj(rev(moi_s3s4_closure stop [] hyps)), prod);;

let MOI_S3S4_323 = prove
 (moi_s3s4_full MOI_S3S4_323_CORE MOI_PROD_323,
  MOI_STD_FULL_TAC MOI_S3S4_323_CORE);;

(* Checks: the glue concludes MOI_PROD_323 with no hypotheses; its          *)
(* hypotheses are those of MOI_STD_323 with HANDLES replaced by HANDLES_2   *)
(* (same foundation antecedents, no new input term).                        *)

let moi_s3s4_check =
  let h_old = conjuncts(lhand(concl MOI_STD_323))
  and h_new = conjuncts(lhand(concl MOI_S3S4_323)) in
  hyp MOI_S3S4_323 = [] && aconv (rand(concl MOI_S3S4_323)) MOI_PROD_323 &&
  hyp MOI_S3S4_323_CORE = [] && hyp MOI_S3S4_HANDLES_WEAKER = [] &&
  length h_old = length h_new &&
  forall (fun a -> exists (aconv a) h_new || aconv a MOI_S32_HANDLES) h_old &&
  forall (fun a -> exists (aconv a) h_old || aconv a MOI_S32_HANDLES_2) h_new &&
  exists (aconv MOI_S32_HANDLES_2) h_new;;

print_string ("S3S4 " ^
   string_of_bool (moi_s3s4_check) ^
   " " ^
   string_of_int ((length(conjuncts(lhand(concl MOI_S3S4_323))))) ^
   "\n");;

