(* ========================================================================= *)
(* pc_moi_glue2: the chart-gluing chain on compact triangulations.          *)
(* pc_moi_glue applies the open-source approximation to arbitrary second    *)
(* countable PL 3-manifolds and so needs locally finite triangulations of   *)
(* all of them (PL_TRIANGULATION_LF_STATEMENT).  Here each gluing step      *)
(* first triangulates a compact neighbourhood S of the part already done    *)
(* (Moise Secs 7-8, compact case) and applies the approximation only on     *)
(* O = (interior of S) INTER (new chart domain), whose locally finite       *)
(* triangulation comes from Moise Thm 8.2 (an open subset of a finite       *)
(* complex).  The leaves are the two cores MOISE_352_COMPLEX and            *)
(* COMBINATORIAL_SMOOTHING (statement constants) and four PL leaves (the    *)
(* MOI_LEAF constants below) proved in pc_moi_ptri, pc_moi_cone with        *)
(* pc_moi_lfopen, and pc_moi_comb.  The per-space predicates moi_352_space  *)
(* and moi_approx_space are the bodies of MOISE_352_OPEN_STATEMENT and      *)
(* MOISE_APPROX_STATEMENT for one space.                                    *)
(* ========================================================================= *)

needs "src/pc_moi_glue.ml";;
needs "src/pc_moi_tridef.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_352_space = new_definition
 `moi_352_space (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    !(h:A->real^3) (e:A->real).
        hausdorff_space top /\ second_countable top /\
        pl_manifold_atlas top atlas /\ embedding_map (top,euclidean) h /\
        continuous_map (top,euclideanreal) e /\
        (!x. x IN topspace top ==> &0 < e x)
        ==> ?f. embedding_map (top,euclidean) f /\ pl_in_charts atlas f /\
                !x. x IN topspace top ==> dist(f x,h x) < e x`;;

let moi_approx_space = new_definition
 `moi_approx_space (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    !(h:A->real^3) (e:A->real).
        hausdorff_space top /\ second_countable top /\
        pl_manifold_atlas top atlas /\
        embedding_map (top,euclidean) h /\ open (IMAGE h (topspace top)) /\
        continuous_map (top,euclideanreal) e /\
        (!x. x IN topspace top ==> &0 < e x)
        ==> ?f. embedding_map (top,euclidean) f /\
                IMAGE f (topspace top) = IMAGE h (topspace top) /\
                pl_in_charts atlas f /\
                !x. x IN topspace top ==> dist(f x,h x) < e x`;;

let MOI_GLUE2_352_OPEN_EQ = prove
 (`!u:A->bool. MOISE_352_OPEN_STATEMENT u <=>
               !top atlas. moi_352_space (top:A topology) atlas`,
  REWRITE_TAC[MOISE_352_OPEN_STATEMENT; moi_352_space]);;

let MOI_GLUE2_APPROX_EQ = prove
 (`!u:A->bool. MOISE_APPROX_STATEMENT u <=>
               !top atlas. moi_approx_space (top:A topology) atlas`,
  REWRITE_TAC[MOISE_APPROX_STATEMENT; moi_approx_space]);;

let MOI_GLUE2_IMAGE_EQUALITY_SPACE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
     moi_352_space top atlas ==> moi_approx_space top atlas`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_352_space; moi_approx_space] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^3`; `e:A->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (h:A->real^3) (topspace top)` MOI_GLUE_DD_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real^3->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `continuous_map (top,euclidean) (h:A->real^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `embedding_map (top,euclidean) (h:A->real^3)`) THEN
    REWRITE_TAC[embedding_map] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,euclideanreal) (dd:real^3->real)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(dd:real^3->real) = drop o (lift o dd)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `euclidean:(real^1)topology` THEN
    REWRITE_TAC[CONTINUOUS_MAP_DROP] THEN
    MP_TAC(ISPECL [`lift o (dd:real^3->real)`; `(:real^3)`]
                  CONTINUOUS_MAP_EUCLIDEAN) THEN
    REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^3` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN
    ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`h:A->real^3`; `\x:A. min (e x) ((dd:real^3->real) (h x) / &5)`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
      SUBGOAL_THEN `(\x:A. (dd:real^3->real) (h x)) = dd o h` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^3)topology` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_MIN] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < d ==> &0 < d / &5`) THEN
      ASM_MESON_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:A->real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> dist((f:A->real^3) x,h x) < e x /\
              dist(f x,h x) < (dd:real^3->real)(h x) / &5`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LT_MIN] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_GLUE_IMAGE_EQ_CORE THEN
  EXISTS_TAC `dd:real^3->real` THEN ASM_SIMP_TAC[]);;

let MOI_GLUE2_TRANSFER_SPACE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c:(real^N->bool)->bool) (t:real^N->A).
     MOISE_352_COMPLEX_STATEMENT (:N) /\ combinatorial_manifold 3 c /\
     homeomorphic_map (subtopology euclidean (UNIONS c),top) t /\
     (!U phi. (U,phi) IN atlas
              ==> ?g. pl_map_on {x | x IN UNIONS c /\ t x IN U} g /\
                      !x. x IN UNIONS c /\ t x IN U ==> g x = phi(t x))
     ==> moi_352_space top atlas`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOISE_352_COMPLEX_STATEMENT; moi_352_space] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^3`; `e:A->real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS] o
    check (fun th -> free_in `t:real^N->A` (concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map")) THEN
  DISCH_THEN(X_CHOOSE_TAC `s:A->real^N`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> free_in `s:A->real^N` (concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_maps")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                              INTER_UNIV]) THEN
  SUBGOAL_THEN `!z:A. z IN topspace top ==> (s:A->real^N) z IN UNIONS c`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `s:A->real^N` (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN UNIONS c ==> (t:real^N->A) x IN topspace top`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `t:real^N->A` (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,euclidean) (h:A->real^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `embedding_map (top,euclidean) (h:A->real^3)`) THEN
    REWRITE_TAC[embedding_map] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:A. x IN topspace top /\ y IN topspace top /\ (h:A->real^3) x = h y ==> x = y`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `embedding_map (top,euclidean) (h:A->real^3)`) THEN
    REWRITE_TAC[embedding_map; homeomorphic_map] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `(h:A->real^3) o (t:real^N->A)`;
    `(e:A->real) o (t:real^N->A)`] o
   check (fun th -> is_forall (concl th) &&
                    can (find_term (fun tm -> try fst(dest_const tm) = "combinatorial_manifold"
                                              with _ -> false)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_GLUE_CONTINUOUS_MAP_LIFT THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(g:real^N->real^3) o (s:A->real^N)` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real^N->real^3) o (s:A->real^N)`]
                  MOI_GLUE_ATLAS_INJECTIVE_EMBEDDING) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (UNIONS c:real^N->bool)` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
      ASM_MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
      ASM_MESON_TAC[]];
    REWRITE_TAC[pl_in_charts] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC MOI_GLUE_TRANSFER_CHART THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `c:(real^N->bool)->bool`; `t:real^N->A`] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(t:real^N->A) ((s:A->real^N) x) = x /\ s x IN UNIONS c`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* The gluing step with the approximation hypothesis for the one overlap    *)
(* space only (pc_moi_glue MOI_GLUE_STEP assumes it for all spaces).        *)

let MOI_GLUE2_STEP_SPACE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) w u (h:A->real^3).
        moi_approx_space (subtopology top (w INTER u))
          {(U INTER (w INTER u),phi) | U,phi | (U,phi) IN atlas} /\
        hausdorff_space top /\
        open_in top w /\ open_in top u /\
        pl_manifold_atlas (subtopology top w) atlas /\
        homeomorphic_map (subtopology top u,euclidean) h
        ==> ?atlas':((A->bool)#(A->real^3))->bool.
              pl_manifold_atlas (subtopology top (w UNION u)) atlas'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "approx") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `hinv:real^3->A` o GEN_REWRITE_RULE I
    [HOMEOMORPHIC_MAP_MAPS] o check (fun th -> is_comb (concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map")) THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `u:A->bool`; `h:A->real^3`;
                 `hinv:real^3->A`] MOI_GLUE_CHART_OVERLAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `topspace (subtopology top (w INTER u)) = w INTER u:A->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_manifold_atlas (subtopology (top:A topology) (w INTER u))
      {(U INTER (w INTER u),phi) | U,phi |
       (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (w:A->bool)`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `w INTER u:A->bool`]
                  MOI_GLUE_PL_ATLAS_RESTRICT) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `w INTER w INTER u:A->bool = w INTER u` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (h:A->real^3) (w INTER u)` MOI_GLUE_DD_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real^3->real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "approx" (MP_TAC o SPECL
   [`h:A->real^3`; `\x:A. (dd:real^3->real) (h x) / &2`] o
   GEN_REWRITE_RULE I [moi_approx_space]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
      MP_TAC(ISPECL [`subtopology top (w INTER u):A topology`;
                     `subtopology euclidean (IMAGE (h:A->real^3) (w INTER u))`;
                     `h:A->real^3`] MOI_GLUE_HOMEOMORPHIC_SECOND_COUNTABLE) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SECOND_COUNTABLE_SUBTOPOLOGY THEN
      REWRITE_TAC[MOI_GLUE_SECOND_COUNTABLE_EUCLIDEAN];
      ASM_REWRITE_TAC[embedding_map];
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
      SUBGOAL_THEN `(\x:A. (dd:real^3->real) (h x)) = dd o h` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_SIMP_TAC[MOI_GLUE_LIPSCHITZ_CONTINUOUS_MAP] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP o
        check (fun th -> is_comb (concl th) &&
          fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map")) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < d ==> &0 < d / &2`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(h:A->real^3) x` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?finv. homeomorphic_maps (subtopology top (w INTER u),
                              subtopology euclidean (IMAGE (h:A->real^3) (w INTER u)))
                             ((f:A->real^3),finv)`
  (X_CHOOSE_TAC `finv:real^3->A`) THENL
   [REWRITE_TAC[GSYM HOMEOMORPHIC_MAP_MAPS] THEN
    UNDISCH_TAC `embedding_map (subtopology top (w INTER u),euclidean) (f:A->real^3)` THEN
    ASM_REWRITE_TAC[embedding_map];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:A. x IN w INTER u ==> (finv:real^3->A) (f x) = x) /\
    continuous_map (subtopology top (w INTER u),euclidean) (f:A->real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `homeomorphic_maps (subtopology top (w INTER u),
                         subtopology euclidean (IMAGE (h:A->real^3) (w INTER u)))
                        ((f:A->real^3),(finv:real^3->A))` THEN
    ASM_REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:A->real^3) (w INTER u)`;
                 `(f:A->real^3) o (hinv:real^3->A)`; `dd:real^3->real`]
                MOI_GLUE_GLUED_HOMEOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology top (w INTER u:A->bool)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IMAGE_o];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_THM] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(finv:real^3->A) (f(x:A)) = x /\ finv (f y) = y`
      (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G':real^3->real^3`) THEN
  EXISTS_TAC `((u:A->bool),
               (\y:real^3. if y IN IMAGE (h:A->real^3) (w INTER u)
                           then ((f:A->real^3) o (hinv:real^3->A)) y else y) o h)
              INSERT (atlas:((A->bool)#(A->real^3))->bool)` THEN
  MATCH_MP_TAC MOI_GLUE_STEP_ATLAS THEN
  MAP_EVERY EXISTS_TAC [`hinv:real^3->A`; `f:A->real^3`; `finv:real^3->A`;
                        `G':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:A->real^3) x IN IMAGE h (w INTER u)` (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `hinv:real^3->A`)) (concl th) &&
    is_forall (concl th) &&
    can (find_term (fun t -> t = `w INTER u:A->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* The four PL leaves of the chain, as statement constants.  Their bodies   *)
(* are the statements of PL_TRIANGULATION_COMPACT_NBHD and                  *)
(* PL_TRIANGULATION_COMPACT_EXISTS (pc_moi_ptri),                           *)
(* LF_TRIANGULATION_OPEN_SUBSET (Moise 8.2; pc_moi_cone with pc_moi_lfopen) *)
(* and PL_TRIANGULATION_COMBINATORIAL (pc_moi_comb).                        *)

let MOI_LEAF_TRI_NBHD = new_definition
 `MOI_LEAF_TRI_NBHD (u:A->bool) (v:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) k.
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ compact_in top k /\
     7 <= dimindex(:N)
     ==> ?(c:(real^N->bool)->bool) t s.
           FINITE c /\ pl_triangulation top atlas c t s /\
           compact_in top s /\ k SUBSET top interior_of s`;;

let MOI_LEAF_TRI_EXISTS = new_definition
 `MOI_LEAF_TRI_EXISTS (u:A->bool) (v:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
     hausdorff_space top /\ compact_space top /\ pl_manifold_atlas top atlas /\
     7 <= dimindex(:N)
     ==> ?(c:(real^N->bool)->bool) t.
           FINITE c /\ pl_triangulation top atlas c t (topspace top)`;;

let MOI_LEAF_LF_OPEN = new_definition
 `MOI_LEAF_LF_OPEN (v:N->bool) <=>
    !(c:(real^N->bool)->bool) u.
     simplicial_complex c /\ open_in (subtopology euclidean (UNIONS c)) u
     ==> ?d. lf_simplicial_complex d /\ UNIONS d = u /\
             (!s. s IN d ==> ?t. t IN c /\ s SUBSET t)`;;

let MOI_LEAF_COMBINATORIAL = new_definition
 `MOI_LEAF_COMBINATORIAL (u:A->bool) (v:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
     (c:(real^N->bool)->bool) t s.
     3 <= dimindex(:N) /\ pl_manifold_atlas top atlas /\ open_in top s /\
     pl_triangulation top atlas c t s
     ==> combinatorial_manifold 3 c`;;

(* Restricting a restricted atlas.                                          *)

let MOI_GLUE2_RESTRICT_RESTRICT = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) w s.
     s SUBSET w
     ==> {(V INTER s,psi) | V,psi |
          (V,psi) IN {(U INTER w,phi) | U,phi | (U,phi) IN atlas}} =
         {(U INTER s,phi) | U,phi | (U,phi) IN atlas}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`X:A->bool`; `chi:A->real^N`] THEN
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
      (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))) THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`U INTER w:A->bool`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]]]);;

(* A chart condition restricts to an open part of a subcomplex.             *)

let MOI_GLUE2_CHART_RESTRICT = prove
 (`!(c:(real^N->bool)->bool) d (t:real^N->A) U U' (phi:A->real^3) g.
     lf_simplicial_complex d /\ UNIONS d SUBSET UNIONS c /\ U' SUBSET U /\
     pl_map_on {x | x IN UNIONS c /\ t x IN U} g /\
     (!x. x IN UNIONS c /\ t x IN U ==> g x = phi (t x)) /\
     open_in (subtopology euclidean (UNIONS d)) {x | x IN UNIONS d /\ t x IN U'}
     ==> ?g'. pl_map_on {x | x IN UNIONS d /\ t x IN U'} g' /\
              !x. x IN UNIONS d /\ t x IN U' ==> g' x = phi (t x)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `g:real^N->real^3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x | x IN UNIONS c /\ (t:real^N->A) x IN U}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;
(* Preimages of chart domains under a triangulation map are open.           *)

let MOI_GLUE2_OPEN_PREIMAGE = prove
 (`!(top:A topology) (D:real^N->bool) (t:real^N->A) O w U.
     continuous_map (subtopology euclidean D,subtopology top O) t /\
     O SUBSET w /\ open_in (subtopology top w) U
     ==> open_in (subtopology euclidean D) {x | x IN D /\ t x IN U}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_SUBTOPOLOGY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `G:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:real^N->A`; `subtopology euclidean (D:real^N->bool)`;
                 `subtopology top (O:A->bool)`; `O INTER G:A->bool`]
                OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN D` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:real^N->A) x IN O` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;
(* One gluing step on a compact part: k is kept inside the new PL domain    *)
(* w' UNION u.  w' is the interior of a triangulated compact neighbourhood  *)
(* S of k (leaf TRI_NBHD); the approximation is applied on w' INTER u only, *)
(* triangulated by Moise 8.2 (leaf LF_OPEN) and combinatorial (leaf         *)
(* COMBINATORIAL).                                                           *)

let MOI_GLUE2_STEP_COMPACT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) w u (h:A->real^3) k.
     7 <= dimindex(:N) /\ MOISE_352_COMPLEX_STATEMENT (:N) /\
     MOI_LEAF_TRI_NBHD (:A) (:N) /\ MOI_LEAF_LF_OPEN (:N) /\
     MOI_LEAF_COMBINATORIAL (:A) (:N) /\
     hausdorff_space top /\ open_in top w /\ open_in top u /\
     pl_manifold_atlas (subtopology top w) atlas /\
     homeomorphic_map (subtopology top u,euclidean) h /\
     compact_in top k /\ k SUBSET w
     ==> ?w' (atlas':((A->bool)#(A->real^3))->bool). open_in top w' /\ k SUBSET w' /\ w' SUBSET w /\
                     pl_manifold_atlas (subtopology top (w' UNION u)) atlas'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_LEAF_TRI_NBHD; MOI_LEAF_LF_OPEN; MOI_LEAF_COMBINATORIAL] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`subtopology top (w:A->bool)`;
     `atlas:((A->bool)#(A->real^3))->bool`; `k:A->bool`] o
   check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "interior_of" with _ -> false))
         (concl th))) THEN
  ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` (X_CHOOSE_THEN `t:real^N->A`
    (X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `w' = subtopology top (w:A->bool) interior_of S` THEN
  SUBGOAL_THEN `open_in top (w':A->bool) /\ w' SUBSET S /\ w' SUBSET w`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `w:A->bool` THEN
      ASM_REWRITE_TAC[OPEN_IN_INTERIOR_OF];
      REWRITE_TAC[INTERIOR_OF_SUBSET];
      MP_TAC(ISPECL [`subtopology top (w:A->bool)`; `S:A->bool`]
        INTERIOR_OF_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top ((w':A->bool) INTER u)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_triangulation] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "pl_triangulation"
                     with _ -> false)) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `subtopology (subtopology top w) (S:A->bool) = subtopology top S`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = {x:real^N | x IN UNIONS c /\ (t:real^N->A) x IN w' INTER u}` THEN
  SUBGOAL_THEN `(w':A->bool) INTER u SUBSET topspace top INTER S` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `(w':A->bool) INTER u`] OPEN_IN_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (UNIONS c),subtopology top S)
                               (t:real^N->A) /\
                IMAGE t (UNIONS c) = topspace top INTER S`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map" &&
                           free_in `t:real^N->A` (concl th) with _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map" &&
                           free_in `t:real^N->A` (concl th) with _ -> false)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (P:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_GLUE2_OPEN_PREIMAGE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S:A->bool`; `S:A->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    SUBGOAL_THEN `(w':A->bool) INTER u = S INTER (w' INTER u)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "lf_simplicial_complex" with _ -> false))
          (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "combinatorial_manifold" with _ -> false))
          (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS d SUBSET UNIONS (c:(real^N->bool)->bool) /\
                UNIONS d = {x:real^N | x IN UNIONS c /\ (t:real^N->A) x IN w' INTER u}`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphic_map (subtopology euclidean (UNIONS d),
                      subtopology top ((w':A->bool) INTER u)) (t:real^N->A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`;
                   `subtopology top (S:A->bool)`; `t:real^N->A`;
                   `UNIONS d:real^N->bool`; `(w':A->bool) INTER u`]
                  HOMEOMORPHIC_MAP_SUBTOPOLOGIES) THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                    TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `UNIONS c INTER UNIONS d:real^N->bool = UNIONS d /\
                  S INTER (w':A->bool) INTER u = w' INTER u`
    (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ASSUME `IMAGE (t:real^N->A) (UNIONS c) = topspace top INTER S`) THEN
    MP_TAC(ASSUME `(w':A->bool) INTER u SUBSET topspace top INTER S`) THEN
    MP_TAC(ASSUME `UNIONS d = {x:real^N | x IN UNIONS c /\ (t:real^N->A) x IN w' INTER u}`) THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      UNDISCH_TAC `(w':A->bool) INTER u SUBSET topspace top INTER S` THEN
      UNDISCH_TAC `(t:real^N->A) x IN w' INTER u` THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:A) IN IMAGE (t:real^N->A) (UNIONS c)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(y:A) = t (x:real^N)` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (UNIONS d),
                    subtopology top ((w':A->bool) INTER u)) (t:real^N->A)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `UNIONS (d:(real^N->bool)->bool) = P`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs(concl th) = `UNIONS (d:(real^N->bool)->bool)`)) THEN
  SUBGOAL_THEN `open_in (subtopology top (w:A->bool)) (w' INTER u)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(w':A->bool) INTER u = w INTER (w' INTER u)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U (phi:A->real^3). (U,phi) IN atlas ==> open_in (subtopology top (w:A->bool)) U`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_manifold_atlas (subtopology top (w:A->bool)) (atlas:((A->bool)#(A->real^3))->bool)` THEN
    REWRITE_TAC[pl_manifold_atlas] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U U' (phi:A->real^3).
      (U,phi) IN atlas /\ U' SUBSET U /\ open_in (subtopology top (w:A->bool)) U'
      ==> ?g. pl_map_on {x | x IN UNIONS d /\ (t:real^N->A) x IN U'} g /\
              !x. x IN UNIONS d /\ t x IN U' ==> g x = phi (t x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "pl_map_on" with _ -> false))
            (concl th) &&
        can (find_term (fun t -> t = `UNIONS (c:(real^N->bool)->bool)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:real^N->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_GLUE2_CHART_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `U:A->bool`; `g0:real^N->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_GLUE2_OPEN_PREIMAGE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(w':A->bool) INTER u`; `w:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 3 (d:(real^N->bool)->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "combinatorial_manifold" with _ -> false))
          (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (w:A->bool)`;
                          `atlas:((A->bool)#(A->real^3))->bool`;
                          `t:real^N->A`; `(w':A->bool) INTER u`] THEN
    ASM_REWRITE_TAC[pl_triangulation; SUBTOPOLOGY_SUBTOPOLOGY] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `7 <= dimindex(:N)` THEN ARITH_TAC;
      SUBGOAL_THEN `w INTER (w':A->bool) INTER u = w' INTER u` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `U':A->bool`)) (concl th))) THEN
      EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with _ -> false)) (concl th) &&
        can (find_term (fun t -> t = `atlas:((A->bool)#(A->real^3))->bool`)) (concl th) &&
        not (can (find_term (fun t -> t = `U':A->bool`)) (concl th)))) THEN
      EXISTS_TAC `phi:A->real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_approx_space (subtopology top ((w':A->bool) INTER u))
      {(U INTER (w' INTER u),phi) | U,phi |
       (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_GLUE2_IMAGE_EQUALITY_SPACE THEN
    MP_TAC(ISPECL [`subtopology top ((w':A->bool) INTER u)`;
                   `{(U INTER (w' INTER u),phi) | U,phi |
                     (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool)}`;
                   `d:(real^N->bool)->bool`; `t:real^N->A`]
                  MOI_GLUE2_TRANSFER_SPACE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^3`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `U':A->bool`)) (concl th))) THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with _ -> false)) (concl th) &&
        can (find_term (fun t -> t = `atlas:((A->bool)#(A->real^3))->bool`)) (concl th) &&
        not (can (find_term (fun t -> t = `U':A->bool`)) (concl th)))) THEN
      EXISTS_TAC `phi:A->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w':A->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `{(U INTER w',phi) | U,phi |
                   (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool)}`;
                 `w':A->bool`; `u:A->bool`; `h:A->real^3`] MOI_GLUE2_STEP_SPACE) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `w':A->bool`;
                   `(w':A->bool) INTER u`] MOI_GLUE2_RESTRICT_RESTRICT) THEN
    REWRITE_TAC[INTER_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`subtopology top (w:A->bool)`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `w':A->bool`]
                  MOI_GLUE_PL_ATLAS_RESTRICT) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `w INTER (w':A->bool) = w'` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `(w':A->bool) = w INTER w'` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[]]);;

(* Finitely many charts with compact shrinkings: induction on the charts.   *)

let MOI_GLUE2_FINITE_CHARTS = prove
 (`!(top:A topology) (charts:((A->bool)#(A->real^3)#(A->bool))->bool).
     7 <= dimindex(:N) /\ MOISE_352_COMPLEX_STATEMENT (:N) /\
     MOI_LEAF_TRI_NBHD (:A) (:N) /\ MOI_LEAF_LF_OPEN (:N) /\
     MOI_LEAF_COMBINATORIAL (:A) (:N) /\
     hausdorff_space top /\ FINITE charts /\
     (!u h k. (u,h,k) IN charts
              ==> open_in top u /\ homeomorphic_map (subtopology top u,euclidean) h /\
                  compact_in top k /\ k SUBSET u)
     ==> ?w (atlas:((A->bool)#(A->real^3))->bool).
           open_in top w /\ UNIONS (IMAGE (SND o SND) charts) SUBSET w /\
           pl_manifold_atlas (subtopology top w) atlas`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; EMPTY_SUBSET] THEN
    MAP_EVERY EXISTS_TAC [`{}:A->bool`; `{}:((A->bool)#(A->real^3))->bool`] THEN
    REWRITE_TAC[OPEN_IN_EMPTY; pl_manifold_atlas; NOT_IN_EMPTY;
                TOPSPACE_SUBTOPOLOGY; INTER_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `h:A->real^3`; `k:A->bool`;
                       `s:((A->bool)#(A->real^3)#(A->bool))->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` (X_CHOOSE_THEN
    `atlas:((A->bool)#(A->real^3))->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open_in top (u:A->bool) /\
                homeomorphic_map (subtopology top u,euclidean) (h:A->real^3) /\
                compact_in top (k:A->bool) /\ k SUBSET u`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `w:A->bool`; `u:A->bool`; `h:A->real^3`;
                 `UNIONS (IMAGE (SND o SND) (s:((A->bool)#(A->real^3)#(A->bool))->bool))`]
                MOI_GLUE2_STEP_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; o_THM] THEN
    ASM_MESON_TAC[IN_INSERT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A->bool` (X_CHOOSE_THEN
    `atlas':((A->bool)#(A->real^3))->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(w':A->bool) UNION u`;
                        `atlas':((A->bool)#(A->real^3))->bool`] THEN
  ASM_SIMP_TAC[OPEN_IN_UNION] THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT; o_THM] THEN ASM SET_TAC[]);;
(* Chart gluing on a compact topological 3-manifold (MOISE_PL_ATLAS) from  *)
(* the leaves: charts onto R^3 with the compact shrinkings HH x^-1 of unit *)
(* closed balls, a finite subcover of the open shrinkings, and induction.   *)

let MOI_GLUE2_CHART_FACTS = prove
 (`!(top:A topology) U (h:A->real^3) x.
     open_in top U /\ x IN U /\ homeomorphic_map (subtopology top U,euclidean) h
     ==> open_in top {y | y IN U /\ h y IN ball(h x,&1)} /\
         x IN {y | y IN U /\ h y IN ball(h x,&1)} /\
         {y | y IN U /\ h y IN ball(h x,&1)} SUBSET
         {y | y IN U /\ h y IN cball(h x,&1)} /\
         compact_in top {y | y IN U /\ h y IN cball(h x,&1)} /\
         {y | y IN U /\ h y IN cball(h x,&1)} SUBSET U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:real^3->A` o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> is_comb (concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_maps")) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; IN_UNIV; IN_INTER] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->real^3`; `subtopology top (U:A->bool)`;
                   `euclidean:(real^3)topology`; `ball((h:A->real^3) x,&1)`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL; TOPSPACE_SUBTOPOLOGY] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; REAL_LT_01];
    MP_TAC(ISPECL [`(h:A->real^3) x`; `&1`] BALL_SUBSET_CBALL) THEN SET_TAC[];
    SUBGOAL_THEN `{y | y IN U /\ (h:A->real^3) y IN cball(h x,&1)} =
                  IMAGE (g:real^3->A) (cball(h x,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:A` THEN
      EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC `(h:A->real^3) y` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SUBSET];
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
          check (fun th -> free_in `g:real^3->A` (concl th) &&
            fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN] THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `compact_in (subtopology top (U:A->bool)) (IMAGE (g:real^3->A) (cball((h:A->real^3) x,&1)))`
    MP_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
      SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]];
    SET_TAC[]]);;
let MOI_GLUE2_CHART_GLUING = prove
 (`!u:A->bool.
     7 <= dimindex(:N) /\ MOISE_352_COMPLEX_STATEMENT (:N) /\
     MOI_LEAF_TRI_NBHD (:A) (:N) /\ MOI_LEAF_LF_OPEN (:N) /\
     MOI_LEAF_COMBINATORIAL (:A) (:N)
     ==> MOISE_PL_ATLAS_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOISE_PL_ATLAS_STATEMENT] THEN
  X_GEN_TAC `top:A topology` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?(UU:A->A->bool) (HH:A->A->real^3).
      !x. x IN topspace top
          ==> open_in top (UU x) /\ x IN UU x /\
              homeomorphic_map (subtopology top (UU x),euclidean) (HH x)`
  (X_CHOOSE_THEN `UU:A->A->bool` (X_CHOOSE_THEN `HH:A->A->real^3`
    (LABEL_TAC "ch"))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    UNDISCH_TAC `locally_euclidean_space (:3) (top:A topology)` THEN
    REWRITE_TAC[locally_euclidean_space] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `subtopology top (U:A->bool) homeomorphic_space (euclidean:(real^3)topology)` THEN
    REWRITE_TAC[homeomorphic_space] THEN MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> open_in top {y | y IN UU x /\ (HH:A->A->real^3) x y IN ball(HH x x,&1)} /\
              x IN {y | y IN UU x /\ HH x y IN ball(HH x x,&1)} /\
              {y | y IN UU x /\ HH x y IN ball(HH x x,&1)} SUBSET
              {y | y IN UU x /\ HH x y IN cball(HH x x,&1)} /\
              compact_in top {y | y IN UU x /\ HH x y IN cball(HH x x,&1)} /\
              {y | y IN UU x /\ HH x y IN cball(HH x x,&1)} SUBSET UU x`
  (LABEL_TAC "facts") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_GLUE2_CHART_FACTS THEN
    USE_THEN "ch" (MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_SPACE] o
    check (fun th -> concl th = `compact_space (top:A topology)`)) THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\x:A. {y | y IN UU x /\ (HH:A->A->real^3) x y IN ball(HH x x,&1)})
          (topspace top)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [USE_THEN "facts" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "facts" (MP_TAC o C MP (ASSUME `(x:A) IN topspace top`) o SPEC `x:A`) THEN
      DISCH_THEN(ACCEPT_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1);
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "facts" (MP_TAC o C MP (ASSUME `(x:A) IN topspace top`) o SPEC `x:A`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\x:A. {y | y IN UU x /\ (HH:A->A->real^3) x y IN ball(HH x x,&1)}`;
    `topspace top:A->bool`; `V:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`top:A topology`;
    `IMAGE (\x:A. (UU:A->A->bool) x,(HH:A->A->real^3) x,
                  {y | y IN UU x /\ HH x y IN cball(HH x x,&1)}) fs`]
   MOI_GLUE2_FINITE_CHARTS) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `h:A->real^3`; `k:A->bool`] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ch" (MP_TAC o C MP (ASSUME `(x:A) IN topspace top`) o SPEC `x:A`) THEN
    USE_THEN "facts" (MP_TAC o C MP (ASSUME `(x:A) IN topspace top`) o SPEC `x:A`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` (X_CHOOSE_THEN
    `atlas:((A->bool)#(A->real^3))->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
  SUBGOAL_THEN `w = topspace (top:A topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC
     `UNIONS (IMAGE (SND o SND)
        (IMAGE (\x:A. (UU:A->A->bool) x,(HH:A->A->real^3) x,
                      {y | y IN UU x /\ HH x y IN cball(HH x x,&1)}) fs))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN UNIONS V` MP_TAC THENL
     [UNDISCH_TAC `UNIONS V = topspace (top:A topology)` THEN
      UNDISCH_TAC `(y:A) IN topspace top` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; o_THM; SND] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "facts" (MP_TAC o C MP (ASSUME `(x:A) IN topspace top`) o SPEC `x:A`) THEN
    UNDISCH_TAC `(y:A) IN {y | y IN UU x /\ (HH:A->A->real^3) x y IN ball(HH x x,&1)}` THEN
    SET_TAC[];
    UNDISCH_TAC `pl_manifold_atlas (subtopology top (w:A->bool))
                   (atlas:((A->bool)#(A->real^3))->bool)` THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]]);;

(* The compact triangulation statement (the statement constant               *)
(* PL_TRIANGULATION_STATEMENT) from the leaves TRI_EXISTS and COMBINATORIAL. *)

let MOI_GLUE2_PL_TRIANGULATION = prove
 (`!(u:A->bool) (v:N->bool).
     MOI_LEAF_TRI_EXISTS (:A) (:N) /\ MOI_LEAF_COMBINATORIAL (:A) (:N)
     ==> PL_TRIANGULATION_STATEMENT u v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_LEAF_TRI_EXISTS; MOI_LEAF_COMBINATORIAL; PL_TRIANGULATION_STATEMENT] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "compact_space" with _ -> false))
          (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` (X_CHOOSE_THEN `t:real^N->A`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t:real^N->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `t:real^N->A`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    UNDISCH_TAC `7 <= dimindex(:N)` THEN ARITH_TAC;
    UNDISCH_TAC `pl_triangulation (top:A topology)
                   (atlas:((A->bool)#(A->real^3))->bool)
                   (c:(real^N->bool)->bool) (t:real^N->A) (topspace top)` THEN
    SIMP_TAC[pl_triangulation; SUBTOPOLOGY_TOPSPACE]]);;

(* The main theorem of the smoothing half (MOISE_SMOOTHING_STATEMENT) from   *)
(* the two cores and the leaves.                                             *)

let MOI_GLUE2_DIMINDEX_7 = prove
 (`7 <= dimindex(:7)`,
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`; LE_REFL]);;

let MOI_MOISE_SMOOTHING_FROM_LEAVES = prove
 (`!u:A->bool.
     MOISE_352_COMPLEX_STATEMENT (:7) /\ COMBINATORIAL_SMOOTHING_STATEMENT (:7) /\
     MOI_LEAF_TRI_NBHD (:A) (:7) /\ MOI_LEAF_TRI_EXISTS (:A) (:7) /\
     MOI_LEAF_LF_OPEN (:7) /\ MOI_LEAF_COMBINATORIAL (:A) (:7)
     ==> MOISE_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `(:7)`] MOI_MOISE_SMOOTHING_FROM_PARTS) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOI_GLUE2_DIMINDEX_7] THEN CONJ_TAC THENL
   [MP_TAC(INST_TYPE [`:7`,`:N`] (ISPEC `u:A->bool` MOI_GLUE2_CHART_GLUING)) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOI_GLUE2_DIMINDEX_7];
    MATCH_MP_TAC MOI_GLUE2_PL_TRIANGULATION THEN ASM_REWRITE_TAC[]]);;

