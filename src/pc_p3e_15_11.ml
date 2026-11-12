(* ========================================================================= *)
(* Unit pc_p3e_15_11: MT Lemma 15.11 (Sec 15.4, pp. 359-364) from its        *)
(* inputs.  S1: the data at the horizon T from Thm 11.19, Lemma 11.30 and    *)
(* Thm 11.31 (with the separation clause: the central sphere of each neck    *)
(* cuts off an end of its horn, MT p. 287), the canonical neighbourhood      *)
(* assumption with r0 = rp(T) and the sphere separation of all stages; S5:   *)
(* the new slab from the maximal flow of the glued metric at T; S8: the      *)
(* extra invariant p3_extra of the extended history; the step lemma through  *)
(* P3E_SURGEVENT; the route level.                                           *)
(* ========================================================================= *)

needs "src/pc_p3e_surgevent.ml";;
needs "src/pc_rfs_limpinch.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Inputs at the horizon T (S1a).  T > 0; the canonical                      *)
(* neighbourhood assumption in the r0 = rp(T) form of MT 11.18 (rp is        *)
(* nonincreasing); sphere separation of every stage; the time-T neck of an  *)
(* evolving neck of the maximal extension; neck domains contain             *)
(* 1/2 < |y| <= 2; the restricted limit metric is pinched at T.             *)
(* ------------------------------------------------------------------------- *)

let P3E_HORIZON_POS = prove
 (`!hs:(A)rfs_history. rfs_history_ok hs ==> &0 < rfs_horizon hs`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3E_LAST_SLAB_FLOW) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o CONJUNCT1)) THEN REAL_ARITH_TAC);;

let P3E_CANON_R0 = prove
 (`!(hs:(A)rfs_history) C eps rp.
     rfs_canonical_assumption (rfs_view hs) C eps rp /\
     (!t. &0 <= t ==> &0 < rp t) /\
     (!s t. &0 <= s /\ s <= t ==> rp t <= rp s)
     ==> !t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
               inv(rp(rfs_horizon hs) pow 2) <= rfs_vscalar (rfs_view hs) t x
               ==> p3_canon_at (rfs_view hs) C eps x t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p3_canon_at] THEN
  MATCH_MP_TAC P3E_CANON_ASSUMPTION_AT THEN EXISTS_TAC `rp:real->real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[rfs_view; rfs_vtop]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(rp(rfs_horizon (hs:(A)rfs_history)) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `&0 < rp(rfs_horizon (hs:(A)rfs_history)) /\ rp(rfs_horizon hs) <= rp t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let P3E_HIST_SPHERE_SEP = prove
 (`!hs:(A)rfs_history.
     RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\ APX_SC_SPHERE_SEP_STATEMENT (:A) /\
     rfs_history_ok hs /\ rfs_components_sc (hs_top hs 0)
     ==> !k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k)`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `hs:(A)rfs_history` RFS_HISTORY_SC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[rfs_components_sc] THEN DISCH_TAC THEN
  UNDISCH_TAC `APX_SC_SPHERE_SEP_STATEMENT (:A)` THEN
  REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;

let P3E_EVNECK_AT_T = prove
 (`!(hs:(A)rfs_history) Om gl dl y len e.
     rfs_evolving_neck (p3_maxext hs Om gl) dl y (rfs_horizon hs) len e
     ==> rfs_neck (subtopology (hs_top hs (hs_count hs)) Om,
                   restrict_atlas (hs_atlas hs (hs_count hs)) Om)
                  (restrict_metric (hs_atlas hs (hs_count hs)) Om gl) dl y e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_maxext; rfs_evolving_neck] THEN SIMP_TAC[]);;

let P3E_NECKDOM_HALF_TWO = prove
 (`!dl x:real^3. &0 < dl /\ dl < &1 / &4 /\ &1 / &2 < norm x /\ norm x <= &2
                 ==> x IN rfs_neck_dom dl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
  SUBGOAL_THEN `&2 <= inv(sqrt(&2) * dl)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&2) * dl /\ sqrt(&2) * dl <= inv(&2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[P3E_SQRT2_LOG2] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (&1 / &4)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN
          SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_LSQRT THEN REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          CONV_TAC REAL_RAT_REDUCE_CONV]];
      MP_TAC(SPECL [`sqrt(&2) * dl`; `inv(&2)`] REAL_LE_INV2) THEN
      ASM_REWRITE_TAC[REAL_INV_INV]];
    ALL_TAC] THEN
  ABBREV_TAC `t = inv(sqrt(&2) * dl)` THEN
  SUBGOAL_THEN `&3 <= exp t /\ exp(--t) <= &1 / &3` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&3 <= exp t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_EXP_NEG] THEN
    MP_TAC(SPECL [`&3`; `exp t`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The restricted limit metric is pinched at T (the slab metrics are        *)
(* pinched before T).                                                        *)

let P3E_LIMIT_PINCHED_RESTRICT = prove
 (`!(hs:(A)rfs_history) Om gl q.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     open_in (hs_top hs (hs_count hs)) Om /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs)) Om
                      (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     q IN Om
     ==> rfs_pinched_at (restrict_atlas (hs_atlas hs (hs_count hs)) Om)
                        (restrict_metric (hs_atlas hs (hs_count hs)) Om gl)
                        (rfs_horizon hs) q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_LAST_SLAB_FLOW) THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                 `hs_atlas (hs:(A)rfs_history) (hs_count hs)`; `Om:A->bool`;
                 `rfs_horizon (hs:(A)rfs_history)`;
                 `hs_metric (hs:(A)rfs_history) (hs_count hs)`; `gl:A->real^3^3`; `q:A`]
                LIM_RESTRICT_CURV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[rfs_pinched_at] THEN REWRITE_TAC[GSYM rfs_pinched_at] THEN
  MATCH_MP_TAC RFS_PINCHED_AT_LIMIT THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (hs_count hs)`; `Om:A->bool`;
                        `hs_metric (hs:(A)rfs_history) (hs_count hs)`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `rfs_horizon (hs:(A)rfs_history) - hs_time hs (hs_count hs)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (hs_count hs) <= t /\ t < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P3E_LAST_SLAB_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:A) IN topspace(hs_top hs (hs_count hs))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (hs_count hs)`; `Om:A->bool`]
                  OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  SUBGOAL_THEN
   `!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
      rfs_pinched V ==>
      !t x. &0 <= t /\ x IN topspace(rfs_vtop V t)
            ==> rfs_pinched_at (rfs_vatlas V t) (rfs_vmetric V t) t x`
  (fun th -> DISCH_THEN(MP_TAC o SPECL [`t:real`; `q:A`] o MATCH_MP th)) THENL
   [REWRITE_TAC[FORALL_PAIR_THM; rfs_pinched; rfs_vtop; rfs_vatlas; rfs_vmetric];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The horn and neck data of Lemma 11.30 and Thm 11.31 in                    *)
(* abstract form (generic carrier B), p3e_horndata, give the cut data        *)
(* p3e_cutdata, the retain data p3e_hdata of pc_p3e_retain, and pairwise    *)
(* disjoint full neck images.  H j parametrizes 1/2 < |y| (the horn is the  *)
(* image of |y| >= 1); e j is the 11.31 neck in the horn of H j; R1 j the    *)
(* radius beyond which the horn lies in the end cut off by e j; nw the      *)
(* fresh cap points.                                                         *)
(* ------------------------------------------------------------------------- *)

let p3e_horndata = new_definition
 `p3e_horndata (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
               (e:num->real^3->B) (nw:num->bool->real^3->B) (Om:B->bool) (P:B->bool)
               (K:B->bool) (H:num->real^3->B) (R1:num->real) (dl:real) <=>
    hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\ compact_space topX /\
    apx_sphere_sep topX atlasX /\
    open_in topX Om /\ P SUBSET Om /\ compact_in topX K /\ FINITE J /\
    (!i b x. ~(nw i b x IN topspace topX)) /\
    (!i b x j c y. nw i b x = nw j c y ==> i = j /\ (b <=> c) /\ x = y) /\
    &0 < dl /\ dl < &1 / &4 /\
    UNIONS {U | U IN connected_components_of (subtopology topX Om) /\ ~(U INTER P = {})} =
    K UNION UNIONS {p3_horn_set (H j) | j IN J} /\
    (!j. j IN J
         ==> mfd_param (subtopology topX Om) (restrict_atlas atlasX Om)
                       {y:real^3 | &1 / &2 < norm y} (H j) /\
             DISJOINT (p3_horn_set (H j)) P /\
             mfd_param (subtopology topX Om) (restrict_atlas atlasX Om) (rfs_neck_dom dl)
                       (e j) /\
             IMAGE (e j) (rfs_neck_dom dl) SUBSET p3_horn_set (H j) /\
             (!z. R1 j <= norm z
                  ==> H j z IN p3_horn_end (subtopology topX Om) (H j) (e j)) /\
             connected_component_of
               (subtopology topX (Om DIFF IMAGE (e j) (sphere(vec 0,&1))))
               (e j (&2 % basis 1)) SUBSET
             IMAGE (H j) {z:real^3 | &1 < norm z}) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (p3_horn_set (H i)) (p3_horn_set (H j)))`;;

let P3E_NECKDOM_ANNULUS = prove
 (`!dl. &0 < dl /\ dl < &1 / &4
        ==> annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl /\
            {y:real^3 | &1 / &2 < norm y /\ norm y <= &2} SUBSET rfs_neck_dom dl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_NECKDOM_HALF_TWO THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3E_HORN_FACTS = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl j.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl /\ j IN J
     ==> mfd_param topX atlasX (rfs_neck_dom dl) (e j) /\
         IMAGE (e j) (rfs_neck_dom dl) SUBSET Om /\
         mfd_param topX atlasX {y:real^3 | &1 / &2 < norm y} (H j) /\
         IMAGE (H j) {y:real^3 | &1 / &2 < norm y} SUBSET Om /\
         p3_horn_set (H j) SUBSET Om /\
         IMAGE (e j) (rfs_neck_dom dl) SUBSET p3_horn_set (H j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3e_horndata] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn_end")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `Om:B->bool`;
                 `rfs_neck_dom dl:real^3->bool`; `(e:num->real^3->B) j`]
                APX_PARAM_FROM_RESTRICT) THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `Om:B->bool`;
                 `{y:real^3 | &1 / &2 < norm y}`; `(H:num->real^3->B) j`]
                APX_PARAM_FROM_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE ((H:num->real^3->B) j) {y:real^3 | &1 / &2 < norm y}` THEN
  ASM_REWRITE_TAC[p3_horn_set] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let P3E_HORN_NECKS_DISJ = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl i j.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl /\ i IN J /\ j IN J /\ ~(i = j)
     ==> DISJOINT (IMAGE (e i) (rfs_neck_dom dl)) (IMAGE (e j) (rfs_neck_dom dl))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_HORN_FACTS) THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `i:num`]
               P3E_HORN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (p3_horn_set ((H:num->real^3->B) i)) (p3_horn_set (H j))` MP_TAC THENL
   [UNDISCH_TAC `p3e_horndata (topX:B topology) atlasX J e nw Om P K H R1 dl` THEN
    REWRITE_TAC[p3e_horndata] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let P3E_HORN_CUTDATA = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl
     ==> p3e_cutdata topX atlasX J e nw`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3e_horndata]) THEN
  REWRITE_TAC[p3e_cutdata] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `dl:real` P3E_NECKDOM_ANNULUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[mfd_neck_chart] THEN
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom dl:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                  `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                  `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `i:num`]
                 P3E_HORN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `i:num`; `j:num`]
               P3E_HORN_NECKS_DISJ) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `!(f:real^3->B) g s t. s SUBSET t ==> DISJOINT (IMAGE f t) (IMAGE g t)
                         ==> DISJOINT (IMAGE f s) (IMAGE g s)`) THEN
  ASM_REWRITE_TAC[]);;

let P3E_SHELL_COMPACT = prove
 (`!R. compact {z:real^3 | &1 <= norm z /\ norm z <= R}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{z:real^3 | &1 <= norm z /\ norm z <= R} = cball(vec 0,R) DIFF ball(vec 0,&1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]]);;

let P3E_HORN_HDATA = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl
     ==> p3e_hdata topX atlasX J e nw Om P K H R1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN ASSUME_TAC(MATCH_MP P3E_HORN_CUTDATA th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[p3e_horndata] th)) THEN
  MP_TAC(SPEC `dl:real` P3E_NECKDOM_ANNULUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3e_hdata] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM p3_horn_set] THEN ASM_REWRITE_TAC[];
    ALL_TAC;
    REWRITE_TAC[GSYM p3_horn_set] THEN FIRST_ASSUM ACCEPT_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn_end")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `j:num`]
               P3E_HORN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM p3_horn_set] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* compact pieces *)
    GEN_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                          `{y:real^3 | &1 / &2 < norm y}`] THEN
    ASM_REWRITE_TAC[P3E_SHELL_COMPACT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    (* the neck piece lies in the horn *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((e:num->real^3->B) j) (rfs_neck_dom dl)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    (* continuity *)
    MP_TAC(MATCH_MP MFD_PARAM_MAPS (ASSUME
      `mfd_param (topX:B topology) atlasX (rfs_neck_dom dl) ((e:num->real^3->B) j)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `rfs_neck_dom dl:real^3->bool` THEN ASM_REWRITE_TAC[];
    (* injectivity *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                         `rfs_neck_dom dl:real^3->bool`; `(e:num->real^3->B) j`]
                        MFD_PARAM_INJ) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `{y:real^3 | &1 / &2 < norm y /\ norm y <= &2} SUBSET rfs_neck_dom dl`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    (* the far end *)
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn_end")) (concl th))) THEN
    ASM_REWRITE_TAC[p3_horn_end; SUBTOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `p3_horn_set ((H:num->real^3->B) j) SUBSET Om` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The two halves of a surgery neck (generic carrier B).  Neck               *)
(* points off the central sphere avoid all cut spheres; the minus half       *)
(* e i (|y| < 1) lies in the retained part Y, the plus half e i (|y| > 1)    *)
(* misses Y (it lies in the component of Om DIFF S at e i (4/3 basis 1),     *)
(* which misses P and every minus point).                                    *)
(* ------------------------------------------------------------------------- *)

let P3E_NECK_SHELLS = prove
 (`!dl. &0 < dl /\ dl < &1 / &4
        ==> connected {y:real^3 | y IN rfs_neck_dom dl /\ norm y < &1} /\
            connected {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y} /\
            (&3 / &4 % basis 1:real^3) IN {y:real^3 | y IN rfs_neck_dom dl /\ norm y < &1} /\
            (&4 / &3 % basis 1:real^3) IN {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&3 / &4 % basis 1:real^3) IN rfs_neck_dom dl /\
                (&4 / &3 % basis 1:real^3) IN rfs_neck_dom dl`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P3E_NECKDOM_HALF_TWO THEN
    ASM_REWRITE_TAC[P3E_NORM_BASIS1_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a = inv(sqrt(&2) * dl)` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3E_SQRT2_LOG2];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--a) < &1 /\ &1 < exp a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EXP_LT_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; P3E_NORM_BASIS1_MUL] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{y:real^3 | (exp(--a) < norm y /\ norm y < exp a) /\ norm y < &1} =
    {y | exp(--a) < norm(y - vec 0) /\ norm(y - vec 0) < &1} /\
    {y:real^3 | (exp(--a) < norm y /\ norm y < exp a) /\ &1 < norm y} =
    {y | &1 < norm(y - vec 0) /\ norm(y - vec 0) < exp a}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; VECTOR_SUB_RZERO] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `exp(--a)`; `&1`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `exp a`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_NECK_PIECE_CONN = prove
 (`!(topX:B topology) atlasX dl (e:real^3->B) s.
     mfd_param topX atlasX (rfs_neck_dom dl) e /\ connected s /\ s SUBSET rfs_neck_dom dl
     ==> connected_in topX (IMAGE e s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclidean (rfs_neck_dom dl:real^3->bool)` THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN MESON_TAC[];
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN]]);;

let P3E_NECK_POINT_OFF = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl i x.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl /\ i IN J /\
     x IN rfs_neck_dom dl /\ ~(norm x = &1)
     ==> e i x IN Om /\ ~(e i x IN mfd_cut_spheres J e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `i:num`]
               P3E_HORN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3e_horndata]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_cut_spheres; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `t:B->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) MP_TAC) THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_NECKDOM_SPHERE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `k:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom dl:real^3->bool`; `(e:num->real^3->B) i`; `x:real^3`;
                   `w:real^3`] MFD_PARAM_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                  `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                  `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `i:num`;
                  `k:num`] P3E_HORN_NECKS_DISJ) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->B) i x`) THEN ASM_MESON_TAC[]]);;

let P3E_NECK_HALVES = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl i.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl /\ i IN J
     ==> connected_in topX (IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ norm y < &1}) /\
         connected_in topX (IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y}) /\
         IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ norm y < &1} SUBSET
         Om DIFF mfd_cut_spheres J e /\
         IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y} SUBSET
         Om DIFF mfd_cut_spheres J e /\
         e i (&3 / &4 % basis 1) IN
         IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ norm y < &1} /\
         e i (&4 / &3 % basis 1) IN
         IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `i:num`]
               P3E_HORN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < dl /\ dl < &1 / &4` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3e_horndata]; ALL_TAC] THEN
  MP_TAC(SPEC `dl:real` P3E_NECK_SHELLS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3E_NECK_PIECE_CONN THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `dl:real`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC P3E_NECK_PIECE_CONN THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `dl:real`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC P3E_NECK_POINT_OFF THEN
    MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                          `nw:num->bool->real^3->B`; `P:B->bool`; `K:B->bool`;
                          `H:num->real^3->B`; `R1:num->real`; `dl:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC P3E_NECK_POINT_OFF THEN
    MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                          `nw:num->bool->real^3->B`; `P:B->bool`; `K:B->bool`;
                          `H:num->real^3->B`; `R1:num->real`; `dl:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P3E_MINUS_HALF_Y = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl i.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl /\ i IN J
     ==> IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ norm y < &1} SUBSET
         p3e_ysp topX J e nw (p3e_rdisc topX J e nw Om P)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_ysp] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                `K:B->bool`; `H:num->real^3->B`; `R1:num->real`] P3E_RETAIN) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P3E_HORN_HDATA THEN EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL P3E_NECK_HALVES) THEN ASM_SIMP_TAC[]);;

let P3E_PLUS_HALF_OFF_Y = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl i.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl /\ i IN J
     ==> DISJOINT (IMAGE (e i) {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y})
                  (p3e_ysp topX J e nw (p3e_rdisc topX J e nw Om P))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_NECK_HALVES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3e_hdata (topX:B topology) atlasX J e nw Om P K H R1` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_HORN_HDATA THEN EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3E_RETAIN) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3E_RETAIN_HYPS) THEN REWRITE_TAC[p3e_rhyp] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `&4 / &3 % basis 1:real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE ((e:num->real^3->B) i) {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y} SUBSET
    connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e))
                           (e i (&4 / &3 % basis 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((e:num->real^3->B) i (&4 / &3 % basis 1) IN p3e_wret topX J e Om P)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_P3E_WRET; DE_MORGAN_THM] THEN REPEAT DISJ2_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM DISJOINT] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3E_WRET_COMPONENT_DISJ) THEN
  REWRITE_TAC[p3e_ysp] THEN
  SUBGOAL_THEN `Om SUBSET topspace (topX:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(topspace (p3e_ctop topX J e nw) DIFF p3e_rdisc topX J e nw Om P) INTER
               topspace topX = p3e_wret (topX:B topology) J e Om P` THEN
  UNDISCH_TAC `IMAGE ((e:num->real^3->B) i) {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y}
               SUBSET Om DIFF mfd_cut_spheres J e` THEN
  UNDISCH_TAC
   `IMAGE ((e:num->real^3->B) i) {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y} SUBSET
    connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e))
                           (e i (&4 / &3 % basis 1))` THEN
  UNDISCH_TAC `Om SUBSET topspace (topX:B topology)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The surgery metric data p3e_smdata from the horn data and                 *)
(* the limit metric facts (generic carrier B); S5, the new slab: the maximal *)
(* flow from the glued metric gT at T, cut at T' <= Tb, equal to gT at T,   *)
(* pinched on [T,T') by MT Thm 4.32.                                         *)
(* ------------------------------------------------------------------------- *)

let P3E_SMDATA_FROM = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl gl g0 A0 d0 h0 md h ts yc.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl /\
     (!c. c IN atlasX
          ==> metric_field (IMAGE (SND c) (FST c INTER Om)) (metric_local atlasX c gl)) /\
     riemannian_metric (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl) /\
     (!q. q IN Om
          ==> rfs_pinched_at (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl) ts q) /\
     p3_std_initial g0 A0 /\ p3e_t132 g0 A0 d0 h0 md /\
     dl <= d0 /\ &0 < h /\ h <= h0 /\ &0 <= ts /\
     (!i. i IN J
          ==> rfs_neck (subtopology topX Om,restrict_atlas atlasX Om)
                       (restrict_metric atlasX Om gl) dl (yc i) (e i) /\
              mfd_scalar (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl) (yc i) =
              inv(h pow 2))
     ==> p3e_smdata topX atlasX J e nw (p3e_rdisc topX J e nw Om P) Om gl g0 A0 d0 h0 md
                    dl h ts yc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3e_hdata (topX:B topology) atlasX J e nw Om P K H R1` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_HORN_HDATA THEN EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_RETAIN) THEN
  SUBGOAL_THEN `p3e_cutdata (topX:B topology) atlasX J e nw` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_HORN_CUTDATA THEN
    MAP_EVERY EXISTS_TAC [`Om:B->bool`; `P:B->bool`; `K:B->bool`; `H:num->real^3->B`;
                          `R1:num->real`; `dl:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (topX:B topology) Om /\ &0 < dl` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p3e_horndata]; ALL_TAC] THEN
  REWRITE_TAC[p3e_smdata] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p3e_ysp] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC P3E_MINUS_HALF_Y THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                          `H:num->real^3->B`; `R1:num->real`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                  `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `P:B->bool`;
                  `K:B->bool`; `H:num->real^3->B`; `R1:num->real`; `dl:real`; `i:num`;
                  `j:num`] P3E_HORN_NECKS_DISJ) THEN
    ASM_REWRITE_TAC[]]);;

let P3E_NEW_SLAB = prove
 (`!(topY:B topology) atlasY gT T0 Tb.
     PDE_MAXIMAL_FLOW_STATEMENT (:B) (:3) /\ P2_THM_4_32_STATEMENT (:B) /\
     hausdorff_space topY /\ smooth_manifold_atlas topY atlasY /\ compact_space topY /\
     riemannian_metric atlasY gT /\ &0 <= T0 /\ T0 < Tb /\
     (!p. p IN topspace topY ==> rfs_pinched_at atlasY gT T0 p)
     ==> ?G' T'. T0 < T' /\ T' <= Tb /\ G' T0 = gT /\
                 ricci_flow_from (topY,atlasY) T0 T' G' /\
                 (!t p. T0 <= t /\ t < T' /\ p IN topspace topY
                        ==> rfs_pinched_at atlasY (G' t) t p)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "p432") STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[PDE_MAXIMAL_FLOW_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                             `gT:B->real^3^3`; `T0:real`]) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "alt"))) THEN
  SUBGOAL_THEN
   `?T'. T0 < T' /\ T' <= Tb /\
        ricci_flow_from (topY:B topology,atlasY) T0 T' (g:real->B->real^3^3)`
  MP_TAC THENL
   [REMOVE_THEN "alt" (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [EXISTS_TAC `Tb:real` THEN ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min Tb b` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`T0:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `ricci_flow_from (topY:B topology,atlasY) T0 T'
      (\t. if t = T0 then gT else (g:real->B->real^3^3) t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `g:real->B->real^3^3` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\t. if t = T0 then gT else (g:real->B->real^3^3) t`; `T':real`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "p432" (MP_TAC o SPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
     `T0:real`; `T':real`; `\t. if t = T0 then gT else (g:real->B->real^3^3) t`] o
     REWRITE_RULE[P2_THM_4_32_STATEMENT]) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* S8, the extra invariant p3_extra dl of the extended history               *)
(* (carrier A + num#num#real^3).  The fresh cap points of event n+1 are      *)
(* INR(SUC n, 2i+1 or 2i, y) (p3e_fresh n); the points of the new stage are  *)
(* old points or such cores; with the plus halves of the new surgery necks   *)
(* discarded and pairwise disjoint, p3_extra passes to the extension.        *)
(* ------------------------------------------------------------------------- *)

let p3e_fresh = new_definition
 `p3e_fresh (n:num) (i:num) (b:bool) (x:real^3) =
    (INR(SUC n,(if b then 2 * i + 1 else 2 * i),x):A+num#num#real^3)`;;

let P3E_FRESH_INJ = prove
 (`!n i b x j c y.
     (p3e_fresh n i b x:A+num#num#real^3) = p3e_fresh n j c y
     ==> i = j /\ (b <=> c) /\ x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3e_fresh; injectivity "sum"; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(if b then 2 * i + 1 else 2 * i) = (if c then 2 * j + 1 else 2 * j)` THEN
  MAP_EVERY BOOL_CASES_TAC [`b:bool`; `c:bool`] THEN REWRITE_TAC[] THENL
   [ARITH_TAC;
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
    ARITH_TAC]);;

let P3E_FRESH_NOT_OLD = prove
 (`!dl (hs:(A+num#num#real^3)rfs_history) i b x.
     p3_extra dl hs
     ==> ~(p3e_fresh (hs_count hs) i b x IN topspace(hs_top hs (hs_count hs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_extra] THEN
  DISCH_THEN(MP_TAC o SPEC `hs_count (hs:(A+num#num#real^3)rfs_history)` o CONJUNCT1) THEN
  REWRITE_TAC[LE_REFL; SUBSET; IN_UNION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[p3e_fresh] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [MESON_TAC[distinctness "sum"];
    REWRITE_TAC[injectivity "sum"; PAIR_EQ] THEN
    MESON_TAC[ARITH_RULE `~(SUC n <= n)`]]);;

let P3E_NEW_STAGE_POINTS = prove
 (`!(topX:(A+num#num#real^3) topology) atlasX J e n D.
     p3e_cutdata topX atlasX J e (p3e_fresh n) /\
     topspace topX SUBSET IMAGE INL (:A) UNION {INR(j,i,y) | j,i,y | j <= n}
     ==> p3e_ysp topX J e (p3e_fresh n) D SUBSET
         IMAGE INL (:A) UNION {INR(j,i,y) | j,i,y | j <= SUC n}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p3e_ysp] THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP P3E_CTOP_TOPSPACE) THEN
  MATCH_MP_TAC(SET_RULE `!s t d:A->bool. s SUBSET t ==> s DIFF d SUBSET t`) THEN
  REWRITE_TAC[p3e_czs; mfd_cut_cores; UNION_SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `topspace (topX:(A+num#num#real^3) topology)` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE INL (:A) UNION
                {INR(j,i,y):A+num#num#real^3 | j,i,y | j <= n}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[ARITH_RULE `j <= n ==> j <= SUC n`];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; UNION_SUBSET] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0; p3e_ccp; p3e_ccm] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p3e_fresh; IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THENL
     [MAP_EVERY EXISTS_TAC [`SUC n`; `2 * i + 1`; `x:real^3`];
      MAP_EVERY EXISTS_TAC [`SUC n`; `2 * i`; `x:real^3`]] THEN
    REWRITE_TAC[LE_REFL]]);;

let P3E_EXTRA_EVENT = prove
 (`!dl (hs:(A+num#num#real^3)rfs_history) hs'.
     p3_extra dl hs /\ rfs_extends hs hs' /\ hs_count hs' = SUC(hs_count hs) /\
     topspace(hs_top hs' (SUC(hs_count hs))) SUBSET
     IMAGE INL (:A) UNION {INR(j,i,y) | j,i,y | j <= SUC(hs_count hs)} /\
     (!i. i IN ev_index(hs_event hs' (SUC(hs_count hs)))
          ==> DISJOINT (IMAGE (ev_neck(hs_event hs' (SUC(hs_count hs))) i)
                              {y | y IN rfs_neck_dom (dl(hs_time hs' (SUC(hs_count hs)))) /\
                                   &1 < norm y})
                       (topspace(hs_top hs' (SUC(hs_count hs))))) /\
     (!i j. i IN ev_index(hs_event hs' (SUC(hs_count hs))) /\
            j IN ev_index(hs_event hs' (SUC(hs_count hs))) /\ ~(i = j)
            ==> DISJOINT (IMAGE (ev_neck(hs_event hs' (SUC(hs_count hs))) i)
                                {y | y IN rfs_neck_dom (dl(hs_time hs' (SUC(hs_count hs)))) /\
                                     &1 < norm y})
                         (IMAGE (ev_neck(hs_event hs' (SUC(hs_count hs))) j)
                                {y | y IN rfs_neck_dom (dl(hs_time hs' (SUC(hs_count hs)))) /\
                                     &1 < norm y}))
     ==> p3_extra dl hs'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "X") (CONJUNCTS_THEN2 (LABEL_TAC "ext")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "F") (CONJUNCTS_THEN2
      (LABEL_TAC "P1") (LABEL_TAC "P2")))))) THEN
  REMOVE_THEN "X" (MP_TAC o REWRITE_RULE[p3_extra]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "XF") (LABEL_TAC "XP")) THEN
  REMOVE_THEN "ext" (MP_TAC o REWRITE_RULE[rfs_extends]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "same") (LABEL_TAC "evs")))) THEN
  REWRITE_TAC[p3_extra] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THENL
   [ASM_CASES_TAC `k = SUC(hs_count (hs:(A+num#num#real^3)rfs_history))` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "F" ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k <= hs_count (hs:(A+num#num#real^3)rfs_history)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "same" (fun th -> MP_TAC(MP (SPEC `k:num` th)
      (ASSUME `k <= hs_count (hs:(A+num#num#real^3)rfs_history)`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "XF" (fun th -> MP_TAC(MP (SPEC `k:num` th)
      (ASSUME `k <= hs_count (hs:(A+num#num#real^3)rfs_history)`))) THEN
    REWRITE_TAC[];
    ASM_CASES_TAC `k = SUC(hs_count (hs:(A+num#num#real^3)rfs_history))` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL
       [USE_THEN "P1" ACCEPT_TAC; USE_THEN "P2" ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `k <= hs_count (hs:(A+num#num#real^3)rfs_history)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "same" (fun th -> MP_TAC(MP (SPEC `k:num` th)
      (ASSUME `k <= hs_count (hs:(A+num#num#real^3)rfs_history)`))) THEN
    STRIP_TAC THEN
    USE_THEN "evs" (fun th -> MP_TAC(MP (SPEC `k:num` th)
      (CONJ (ASSUME `1 <= k`) (ASSUME `k <= hs_count (hs:(A+num#num#real^3)rfs_history)`)))) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "XP" (fun th -> MP_TAC(MP (SPEC `k:num` th)
      (CONJ (ASSUME `1 <= k`) (ASSUME `k <= hs_count (hs:(A+num#num#real^3)rfs_history)`)))) THEN
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The step of MT Lemma 15.11 (carrier A + num#num#real^3).                  *)
(* From the surgery data at the horizon T (horn and neck data with the fresh *)
(* cores p3e_fresh n, the limit metric gl on Om, the y-necks, the uniform    *)
(* time t1 for compact sets off Omega_rho) to the extended history with      *)
(* p3_struct and p3_extra, through P3E_SURGMETRIC, P3E_NEW_SLAB and          *)
(* P3E_SURGEVENT.                                                            *)
(* ------------------------------------------------------------------------- *)

let P3E_WRET_COMPLEMENT = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 dl.
     p3e_horndata topX atlasX J e nw Om P K H R1 dl
     ==> compact_in topX (topspace topX DIFF p3e_wret topX J e Om P) /\
         DISJOINT (topspace topX DIFF p3e_wret topX J e Om P) P`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN ASSUME_TAC(MATCH_MP P3E_HORN_CUTDATA th) THEN
                       ASSUME_TAC(MATCH_MP P3E_HORN_HDATA th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[p3e_horndata] th)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
    MATCH_MP_TAC P3E_WRET_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `nw:num->bool->real^3->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_RETAIN o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3e_hdata")) (concl th))) THEN
  SUBGOAL_THEN `Om SUBSET topspace (topX:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `P SUBSET topspace (p3e_ctop topX J e nw) DIFF
               p3e_rdisc topX J e nw Om (P:B->bool)` THEN
  UNDISCH_TAC `(topspace (p3e_ctop topX J e nw) DIFF p3e_rdisc topX J e nw Om P) INTER
               topspace topX = p3e_wret (topX:B topology) J e Om P` THEN
  UNDISCH_TAC `(P:B->bool) SUBSET Om` THEN UNDISCH_TAC `Om SUBSET topspace (topX:B topology)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN SET_TAC[]);;

let P3E_STEP_SMDATA = prove
 (`!C eps hf md g0 A0 d0 h0 rp dl (hs:(A+num#num#real^3)rfs_history) Om gl J e K H R1 yv.
     p3_std_initial g0 A0 /\ p3e_t132 g0 A0 d0 h0 md /\
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
     dl(rfs_horizon hs) <= d0 /\
     &0 < p3_hscale hf rp dl (rfs_horizon hs) /\ p3_hscale hf rp dl (rfs_horizon hs) <= h0 /\
     p3e_horndata (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) J e
                  (p3e_fresh (hs_count hs)) Om
                  (p3_omega_rho (hs_atlas hs (hs_count hs)) Om gl
                                (dl(rfs_horizon hs) * rp(rfs_horizon hs)))
                  K H R1 (dl(rfs_horizon hs)) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs)) Om
                      (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     (!i. i IN J
          ==> yv i IN Om /\
              rfs_evolving_neck (p3_maxext hs Om gl) (dl(rfs_horizon hs)) (yv i)
                                (rfs_horizon hs) (&2) (e i) /\
              mfd_scalar (hs_atlas hs (hs_count hs)) gl (yv i) =
              inv(p3_hscale hf rp dl (rfs_horizon hs) pow 2))
     ==> p3e_smdata (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) J e
                    (p3e_fresh (hs_count hs))
                    (p3e_rdisc (hs_top hs (hs_count hs)) J e (p3e_fresh (hs_count hs)) Om
                       (p3_omega_rho (hs_atlas hs (hs_count hs)) Om gl
                                     (dl(rfs_horizon hs) * rp(rfs_horizon hs))))
                    Om gl g0 A0 d0 h0 md (dl(rfs_horizon hs))
                    (p3_hscale hf rp dl (rfs_horizon hs)) (rfs_horizon hs) yv`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A+num#num#real^3)rfs_history) /\ rfs_pinched (rfs_view hs)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A+num#num#real^3)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_LAST_SLAB_FLOW) THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_horndata (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs))
                   (hs_atlas hs (hs_count hs)) J e (p3e_fresh (hs_count hs)) Om
                   (p3_omega_rho (hs_atlas hs (hs_count hs)) Om gl
                                 (dl(rfs_horizon hs) * rp(rfs_horizon hs)))
                   K H R1 (dl(rfs_horizon hs))` THEN
    REWRITE_TAC[p3e_horndata] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P3E_SMDATA_FROM THEN
  MAP_EVERY EXISTS_TAC [`K:(A+num#num#real^3)->bool`; `H:num->real^3->(A+num#num#real^3)`;
                        `R1:num->real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `rfs_limit_metric (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs),
                                   hs_atlas hs (hs_count hs)) Om
                                  (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl` THEN
    REWRITE_TAC[rfs_limit_metric] THEN SIMP_TAC[];
    MATCH_MP_TAC LIM_RESTRICT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`;
                          `rfs_horizon (hs:(A+num#num#real^3)rfs_history)`;
                          `hs_metric (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `q:A+num#num#real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3E_LIMIT_PINCHED_RESTRICT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P3E_HORIZON_POS THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_EVNECK_AT_T THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`;
                     `hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`;
                     `Om:(A+num#num#real^3)->bool`;
                     `rfs_horizon (hs:(A+num#num#real^3)rfs_history)`;
                     `hs_metric (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`;
                     `gl:(A+num#num#real^3)->real^3^3`; `(yv:num->(A+num#num#real^3)) i`]
                    LIM_RESTRICT_CURV) THEN
      ASM_SIMP_TAC[]]]);;

let P3E_STEP_EXTRA = prove
 (`!dl (hs:(A+num#num#real^3)rfs_history) hs' J e Om P K H R1 topY.
     p3_extra dl hs /\
     p3e_horndata (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) J e
                  (p3e_fresh (hs_count hs)) Om P K H R1 (dl(rfs_horizon hs)) /\
     rfs_extends hs hs' /\ hs_count hs' = SUC(hs_count hs) /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\
     hs_top hs' (SUC(hs_count hs)) = topY /\
     topspace topY =
     p3e_ysp (hs_top hs (hs_count hs)) J e (p3e_fresh (hs_count hs))
             (p3e_rdisc (hs_top hs (hs_count hs)) J e (p3e_fresh (hs_count hs)) Om P) /\
     ev_index(hs_event hs' (SUC(hs_count hs))) = J /\
     ev_neck(hs_event hs' (SUC(hs_count hs))) = e
     ==> p3_extra dl hs'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P3E_EXTRA_EVENT THEN EXISTS_TAC `hs:(A+num#num#real^3)rfs_history` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3E_NEW_STAGE_POINTS THEN
    EXISTS_TAC `hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3E_HORN_CUTDATA THEN
      MAP_EVERY EXISTS_TAC [`Om:(A+num#num#real^3)->bool`; `P:(A+num#num#real^3)->bool`;
                            `K:(A+num#num#real^3)->bool`; `H:num->real^3->(A+num#num#real^3)`;
                            `R1:num->real`;
                            `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`] THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `p3_extra dl (hs:(A+num#num#real^3)rfs_history)` THEN
      REWRITE_TAC[p3_extra] THEN
      DISCH_THEN(MP_TAC o SPEC `hs_count (hs:(A+num#num#real^3)rfs_history)` o CONJUNCT1) THEN
      REWRITE_TAC[LE_REFL]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3E_PLUS_HALF_OFF_Y THEN
    MAP_EVERY EXISTS_TAC [`hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`;
                          `K:(A+num#num#real^3)->bool`; `H:num->real^3->(A+num#num#real^3)`;
                          `R1:num->real`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`;
                  `hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`; `J:num->bool`;
                  `e:num->real^3->(A+num#num#real^3)`;
                  `p3e_fresh (hs_count (hs:(A+num#num#real^3)rfs_history))
                     :num->bool->real^3->(A+num#num#real^3)`;
                  `Om:(A+num#num#real^3)->bool`; `P:(A+num#num#real^3)->bool`;
                  `K:(A+num#num#real^3)->bool`; `H:num->real^3->(A+num#num#real^3)`;
                  `R1:num->real`; `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`;
                  `i:num`; `j:num`] P3E_HORN_NECKS_DISJ) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:real^3->A+num#num#real^3) g s t. s SUBSET t ==> DISJOINT (IMAGE f t) (IMAGE g t)
                                         ==> DISJOINT (IMAGE f s) (IMAGE g s)`) THEN
    SET_TAC[]]);;

let P3E_STEP_CORE = prove
 (`!C eps hf md g0 A0 d0 h0 rp dl (hs:(A+num#num#real^3)rfs_history) Tb Om gl J e K H R1 yv.
     PDE_MAXIMAL_FLOW_STATEMENT (:A+num#num#real^3) (:3) /\
     P2_THM_4_32_STATEMENT (:A+num#num#real^3) /\
     RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     p3_std_initial g0 A0 /\ p3e_t132 g0 A0 d0 h0 md /\
     p3_extra dl hs /\ p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
     rfs_slab_maximal hs (hs_count hs) /\ rfs_horizon hs < Tb /\
     dl(rfs_horizon hs) <= d0 /\
     &0 < p3_hscale hf rp dl (rfs_horizon hs) /\ p3_hscale hf rp dl (rfs_horizon hs) <= h0 /\
     p3e_horndata (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) J e
                  (p3e_fresh (hs_count hs)) Om
                  (p3_omega_rho (hs_atlas hs (hs_count hs)) Om gl
                                (dl(rfs_horizon hs) * rp(rfs_horizon hs)))
                  K H R1 (dl(rfs_horizon hs)) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs)) Om
                      (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     (!i. i IN J
          ==> yv i IN Om /\
              rfs_evolving_neck (p3_maxext hs Om gl) (dl(rfs_horizon hs)) (yv i)
                                (rfs_horizon hs) (&2) (e i) /\
              mfd_scalar (hs_atlas hs (hs_count hs)) gl (yv i) =
              inv(p3_hscale hf rp dl (rfs_horizon hs) pow 2)) /\
     (!Kd. compact_in (hs_top hs (hs_count hs)) Kd /\
           DISJOINT Kd (p3_omega_rho (hs_atlas hs (hs_count hs)) Om gl
                                     (dl(rfs_horizon hs) * rp(rfs_horizon hs)))
           ==> ?t1. hs_time hs (hs_count hs) <= t1 /\ t1 < rfs_horizon hs /\
                    !t x. t1 < t /\ t < rfs_horizon hs /\ x IN Kd
                          ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x t U)
     ==> ?hs'. rfs_extends hs hs' /\ hs_count hs' = SUC(hs_count hs) /\
               hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\
               rfs_horizon hs < rfs_horizon hs' /\ rfs_horizon hs' <= Tb /\
               p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs' /\ p3_extra dl hs'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rfs_horizon (hs:(A+num#num#real^3)rfs_history)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P3E_HORIZON_POS THEN
    UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A+num#num#real^3)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* S4: the surgery metric on the retained part Y *)
  MP_TAC(SPEC_ALL P3E_STEP_SMDATA) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P3E_SURGMETRIC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tY")
      (X_CHOOSE_THEN `gT:(A+num#num#real^3)->real^3^3` STRIP_ASSUME_TAC))))) THEN
  (* S5: the new slab *)
  MP_TAC(ISPECL [`p3e_ytop (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e
      (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) (p3e_rdisc
      (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) Om
      (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl
      (dl(rfs_horizon hs) * rp(rfs_horizon hs))))`; `p3e_yatlas (hs_top
      (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) (hs_atlas
      (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) (p3e_rdisc
      (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) Om
      (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl
      (dl(rfs_horizon hs) * rp(rfs_horizon hs))))`; `gT:(A+num#num#real^3)->real^3^3`;
                 `rfs_horizon (hs:(A+num#num#real^3)rfs_history)`; `Tb:real`] P3E_NEW_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G':real->(A+num#num#real^3)->real^3^3`
    (X_CHOOSE_THEN `T':real` STRIP_ASSUME_TAC)) THEN
  (* S9: the uniform time t1 off the retained old points *)
  MP_TAC(ISPECL [`hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`; `hs_atlas
      (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`; `J:num->bool`;
      `e:num->real^3->(A+num#num#real^3)`; `(p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))`;
                 `Om:(A+num#num#real^3)->bool`; `p3_omega_rho (hs_atlas
                    (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl (dl(rfs_horizon hs)
                    * rp(rfs_horizon hs))`; `K:(A+num#num#real^3)->bool`;
                 `H:num->real^3->(A+num#num#real^3)`; `R1:num->real`;
                 `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`]
                P3E_WRET_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `topspace (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count
      hs)) DIFF p3e_wret (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e Om
      (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl
      (dl(rfs_horizon hs) * rp(rfs_horizon hs)))` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_canonical"))
          (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* S6, S7: the extended history and its structural invariant *)
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A+num#num#real^3)rfs_history`; `hs_top (hs:(A+num#num#real^3)rfs_history)
                    (hs_count hs)`; `hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count
                    hs)`; `J:num->bool`;
                 `e:num->real^3->(A+num#num#real^3)`; `(p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))`;
                    `Om:(A+num#num#real^3)->bool`;
                 `p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om
                    gl (dl(rfs_horizon hs) * rp(rfs_horizon hs))`;
                    `gl:(A+num#num#real^3)->real^3^3`; `p3e_rdisc (hs_top
                    (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))
                    Om (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count
                    hs)) Om gl (dl(rfs_horizon hs) * rp(rfs_horizon hs)))`; `p3e_ytop (hs_top
                    (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))
                    (p3e_rdisc (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e
                    (p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))
                    Om (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count
                    hs)) Om gl (dl(rfs_horizon hs) * rp(rfs_horizon hs))))`; `p3e_yatlas
                    (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) (hs_atlas
                    (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))
                    (p3e_rdisc (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e
                    (p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))
                    Om (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count
                    hs)) Om gl (dl(rfs_horizon hs) * rp(rfs_horizon hs))))`;
                 `G':real->(A+num#num#real^3)->real^3^3`; `T':real`] P3E_SURGEVENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3E_RETAIN_HYPS THEN
      MAP_EVERY EXISTS_TAC [`K:(A+num#num#real^3)->bool`; `H:num->real^3->(A+num#num#real^3)`;
                            `R1:num->real`] THEN
      MATCH_MP_TAC P3E_HORN_HDATA THEN
      EXISTS_TAC `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[p3_omega_rho; IN_ELIM_THM] THEN MESON_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      EXISTS_TAC `(yv:num->(A+num#num#real^3)) i` THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "rfs_same_metric_on")) (concl th))) THEN
      USE_THEN "tY" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `p3e_hevent hs (p3e_ytop (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs))
      J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) (p3e_rdisc
      (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) Om
      (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl
      (dl(rfs_horizon hs) * rp(rfs_horizon hs))))) (p3e_yatlas (hs_top
      (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) (hs_atlas
      (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) (p3e_rdisc
      (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) Om
      (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl
      (dl(rfs_horizon hs) * rp(rfs_horizon hs))))) G' T' (p3e_newev (hs_top
      (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) (hs_atlas
      (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) (p3e_rdisc
      (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
      (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3)) Om
      (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Om gl
      (dl(rfs_horizon hs) * rp(rfs_horizon hs)))))` THEN
  ASM_REWRITE_TAC[] THEN
  (* S8: the extra invariant *)
  MATCH_MP_TAC P3E_STEP_EXTRA THEN
  MAP_EVERY EXISTS_TAC [`hs:(A+num#num#real^3)rfs_history`; `J:num->bool`;
                        `e:num->real^3->(A+num#num#real^3)`; `Om:(A+num#num#real^3)->bool`;
                        `p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count
                    hs)) Om gl (dl(rfs_horizon hs) * rp(rfs_horizon hs))`;
                    `K:(A+num#num#real^3)->bool`;
                        `H:num->real^3->(A+num#num#real^3)`; `R1:num->real`; `p3e_ytop (hs_top
                    (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e (p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))
                    (p3e_rdisc (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) J e
                    (p3e_fresh (hs_count
                    (hs:(A+num#num#real^3)rfs_history)):num->bool->real^3->(A+num#num#real^3))
                    Om (p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count
                    hs)) Om gl (dl(rfs_horizon hs) * rp(rfs_horizon hs))))`] THEN
  ASM_REWRITE_TAC[P3E_NEWEV_FIELDS] THEN USE_THEN "tY" ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The route level.  MT Lemma 15.11 from its route inputs                    *)
(* (P3_LEMMA_15_11_ROUTE_STATEMENT, with the statements                      *)
(* P2_THM_11_31_STATEMENT and P3_LEMMA_15_11_STATEMENT).                     *)
(* ------------------------------------------------------------------------- *)


(* The constants at T: dl(T) small, rho = dl(T) rp(T) < rp(T), 2 rp(T)^-2   *)
(* <= rho^-2, and the surgery scale h(T) in (0, h0] (using rp(T) <= eps).   *)

let P3E_RT_CONSTS = prove
 (`!C hf d0 h0 eps dlT rpT.
     &1 < C /\ p3_hfun C hf /\ &0 < d0 /\ &0 < h0 /\ &0 < eps /\ eps <= &1 /\
     &0 < dlT /\ dlT <= min d0 (min h0 (&1 / &8)) /\ &0 < rpT /\ rpT <= eps
     ==> dlT < &1 / &4 /\ dlT < &1 /\ dlT <= d0 /\
         &0 < dlT * rpT /\ dlT * rpT < rpT /\
         &2 * inv(rpT pow 2) <= inv((dlT * rpT) pow 2) /\
         &0 < hf (dlT * rpT) dlT /\ hf (dlT * rpT) dlT <= h0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `dlT <= d0 /\ dlT <= h0 /\ dlT <= &1 / &8` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dlT <= min d0 (min h0 (&1 / &8))` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dlT * rpT` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `dlT * rpT <= &1` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`dlT * rpT`; `dlT:real`]
    (REWRITE_RULE[p3_hfun] (ASSUME `p3_hfun C hf`))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&2 <= inv(dlT pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(&2))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &8) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_MUL; REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dlT * rpT) * dlT` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let P3E_MAXEXT_AT_T = prove
 (`!(hs:(A)rfs_history) Om gl.
     rfs_vtop (p3_maxext hs Om gl) (rfs_horizon hs) =
     subtopology (hs_top hs (hs_count hs)) Om /\
     rfs_vatlas (p3_maxext hs Om gl) (rfs_horizon hs) =
     restrict_atlas (hs_atlas hs (hs_count hs)) Om /\
     rfs_vmetric (p3_maxext hs Om gl) (rfs_horizon hs) =
     restrict_metric (hs_atlas hs (hs_count hs)) Om gl`,
  REWRITE_TAC[p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* S1b at the history level: the 11.30 horns and the 11.31 necks (one per   *)
(* horn, Skolemized) give the abstract horn data with the fresh cores.      *)

let P3E_RT_HORNDATA = prove
 (`!(hs:(A+num#num#real^3)rfs_history) eps gl dl dl0 P J H K yv ee RR1.
     p3_extra dl hs /\ rfs_history_ok hs /\
     apx_sphere_sep (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
     open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\ P SUBSET p3_omega hs /\
     &0 < dl0 /\ dl0 < &1 / &4 /\
     FINITE J /\ compact_in (hs_top hs (hs_count hs)) K /\
     UNIONS {U | U IN connected_components_of
                        (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\
                 ~(U INTER P = {})} =
     K UNION UNIONS {p3_horn_set (H j) | j IN J} /\
     (!j. j IN J
          ==> p3_horn (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (&2 * eps) (H j) /\
              DISJOINT (p3_horn_set (H j)) P) /\
     (!i j. i IN J /\ j IN J /\ ~(i = j)
            ==> DISJOINT (p3_horn_set (H i)) (p3_horn_set (H j))) /\
     (!j. j IN J
          ==> rfs_evolving_neck (p3_maxext hs (p3_omega hs) gl) dl0 (yv j) (rfs_horizon hs)
                                (&2) (ee j) /\
              IMAGE (ee j) (rfs_neck_dom dl0) SUBSET p3_horn_set (H j) /\
              (!z. RR1 j <= norm z
                   ==> H j z IN p3_horn_end (subtopology (hs_top hs (hs_count hs))
                                                         (p3_omega hs)) (H j) (ee j)) /\
              connected_component_of
                (subtopology (hs_top hs (hs_count hs))
                             (p3_omega hs DIFF IMAGE (ee j) (sphere(vec 0,&1))))
                (ee j (&2 % basis 1)) SUBSET IMAGE (H j) {z:real^3 | &1 < norm z})
     ==> p3e_horndata (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) J ee
                      (p3e_fresh (hs_count hs)) (p3_omega hs) P K H RR1 dl0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3e_horndata] THEN
  ASM_REWRITE_TAC[P3E_FRESH_INJ] THEN
  SUBGOAL_THEN
   `hausdorff_space (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) /\
    smooth_manifold_atlas (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
    compact_space (hs_top hs (hs_count hs))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P3E_LAST_SLAB_FLOW) THEN SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P3E_FRESH_NOT_OLD THEN
    EXISTS_TAC `dl:real->real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn_end")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[p3_horn] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn")) (concl th))) THEN
    REWRITE_TAC[P3E_MAXEXT_AT_T];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP P3E_EVNECK_AT_T o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck"))
          (concl th))) THEN
    SIMP_TAC[rfs_neck];
    ASM_MESON_TAC[]]);;

(* MT Lemma 15.11 from its inputs, the hypotheses of the route statement.   *)

let P3E_LEMMA_15_11_PRE = prove
 (`!u:A->bool.
     P3_THM_13_2_STATEMENT /\
     PDE_MAXIMAL_FLOW_STATEMENT (:A+num#num#real^3) (:3) /\
     P2_THM_4_32_STATEMENT (:A+num#num#real^3) /\
     P2_THM_11_19_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_11_30_STATEMENT (:A+num#num#real^3) /\
     P2_THM_11_31_STATEMENT (:A+num#num#real^3) /\ P2_LEMMA_12_3_STATEMENT /\
     RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     APX_SC_SPHERE_SEP_STATEMENT (:A+num#num#real^3)
     ==> P3_LEMMA_15_11_STATEMENT u`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t132") (CONJUNCTS_THEN2 (LABEL_TAC "maxf")
    (CONJUNCTS_THEN2 (LABEL_TAC "p432") (CONJUNCTS_THEN2 (LABEL_TAC "t1119")
    (CONJUNCTS_THEN2 (LABEL_TAC "l1130") (CONJUNCTS_THEN2 (LABEL_TAC "t1131")
    (CONJUNCTS_THEN2 (LABEL_TAC "l123") (CONJUNCTS_THEN2 (LABEL_TAC "ccsc")
      (LABEL_TAC "scsep"))))))))) THEN
  REWRITE_TAC[P3_LEMMA_15_11_STATEMENT] THEN
  (* the standard initial metric and the constants of Thm 13.2 *)
  REMOVE_THEN "l123" (X_CHOOSE_THEN `g0:real^3->real^3^3` (X_CHOOSE_THEN `A0:real`
    (X_CHOOSE_THEN `Kv:real` (X_CHOOSE_THEN `Dv:real` STRIP_ASSUME_TAC))) o
    REWRITE_RULE[P2_LEMMA_12_3_STATEMENT]) THEN
  USE_THEN "t132" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`] o MATCH_MP P3E_T132) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `h0:real` (X_CHOOSE_THEN `md:real->real`
    (fun th -> LABEL_TAC "t132i" th THEN STRIP_ASSUME_TAC(REWRITE_RULE[p3e_t132] th))))) THEN
  (* the thresholds of 11.19, 11.30, 11.31 and of the disappearing region *)
  REMOVE_THEN "t1119" (X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `e19:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T19")))) o
    REWRITE_RULE[P2_THM_11_19_STATEMENT]) THEN
  REMOVE_THEN "l1130" (X_CHOOSE_THEN `e30:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L30")) o
    REWRITE_RULE[P2_LEMMA_11_30_STATEMENT]) THEN
  REMOVE_THEN "t1131" (X_CHOOSE_THEN `e31:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T31")) o
    REWRITE_RULE[P2_THM_11_31_STATEMENT]) THEN
  X_CHOOSE_THEN `e9:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DIS"))
    (INST_TYPE [`:A+num#num#real^3`,`:A`] P3E_DISAPPEAR_OMEGA) THEN
  MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `md:real->real`;
    `min (&1) (min e19 (min e30 (min e31 e9)))`; `min d0 (min h0 (&1 / &8))`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC(DEPTH_CONV REAL_RAT_LT_CONV) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`] THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  REMOVE_THEN "T31" (MP_TAC o SPECL [`C:real`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hf:real->real->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T31h"))) THEN
  EXISTS_TAC `hf:real->real->real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`rp:real->real`; `dl:real->real`; `kp:real->real`;
                       `hs:(A+num#num#real^3)rfs_history`; `Tb:real`] THEN
  STRIP_TAC THEN
  (* the history at its horizon T *)
  STRIP_ASSUME_TAC(REWRITE_RULE[p3_struct]
    (ASSUME `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A+num#num#real^3)rfs_history)`)) THEN
  SUBGOAL_THEN `&0 < rfs_horizon (hs:(A+num#num#real^3)rfs_history)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_HORIZON_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rp(rfs_horizon (hs:(A+num#num#real^3)rfs_history)) /\
                &0 < dl(rfs_horizon hs) /\ dl(rfs_horizon hs) <= d0 /\
                dl(rfs_horizon hs) <= h0 /\ dl(rfs_horizon hs) <= &1 / &8 /\
                rp(rfs_horizon hs) <= eps`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `hf:real->real->real`; `d0:real`; `h0:real`; `eps:real`;
                `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`;
                `rp(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`] P3E_RT_CONSTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_MIN]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A+num#num#real^3)rfs_history`; `C:real`; `eps:real`; `rp:real->real`]
                P3E_CANON_R0) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "can")] THEN
  MP_TAC(ISPEC `hs:(A+num#num#real^3)rfs_history` P3E_HIST_SPHERE_SEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "sep")] THEN
  (* Thm 11.19: Omega open, the limit metric *)
  REMOVE_THEN "T19" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A+num#num#real^3)rfs_history`;
     `rp(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `gl:(A+num#num#real^3)->real^3^3`) (K ALL_TAC))) THEN
  (* Lemma 11.30 at rho = dl(T) rp(T): the horns *)
  REMOVE_THEN "L30" (MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A+num#num#real^3)rfs_history`;
     `rp(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`; `gl:(A+num#num#real^3)->real^3^3`;
     `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)) * rp(rfs_horizon hs)`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num->bool` (X_CHOOSE_THEN `H:num->real^3->(A+num#num#real^3)`
    (X_CHOOSE_THEN `K:(A+num#num#real^3)->bool` STRIP_ASSUME_TAC))) THEN
  (* Thm 11.31 in each horn (with the separation clause), Skolemized *)
  REMOVE_THEN "T31h" (MP_TAC o SPECL [`hs:(A+num#num#real^3)rfs_history`;
     `rp(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`; `gl:(A+num#num#real^3)->real^3^3`;
     `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`]) THEN
  DISCH_THEN(fun th ->
    let yc = rand(rand(concl(SPEC `(H:num->real^3->(A+num#num#real^3)) j` th))) in
    SUBGOAL_THEN (mk_forall(`j:num`, mk_imp(`(j:num) IN J`, yc))) MP_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `(H:num->real^3->(A+num#num#real^3)) j` th) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)) * rp(rfs_horizon hs) /
                    (&2 * C) = (dl(rfs_horizon hs) * rp(rfs_horizon hs)) / (&2 * C)`
      SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ASM_REWRITE_TAC[]];
      ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `yv:num->(A+num#num#real^3)` (X_CHOOSE_THEN
    `ee:num->real^3->(A+num#num#real^3)` (X_CHOOSE_THEN `RR1:num->real` (LABEL_TAC "Y31"))) o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  (* the abstract horn data with the fresh cores *)
  SUBGOAL_THEN
   `p3e_horndata (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs))
                 (hs_atlas hs (hs_count hs)) J ee (p3e_fresh (hs_count hs)) (p3_omega hs)
                 (p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl
                               (dl(rfs_horizon hs) * rp(rfs_horizon hs)))
                 K H RR1 (dl(rfs_horizon hs))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_RT_HORNDATA THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `gl:(A+num#num#real^3)->real^3^3`; `dl:real->real`;
                          `yv:num->(A+num#num#real^3)`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; ASM_SIMP_TAC[LE_REFL];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[p3_omega_rho; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_horn")) (concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "Y31" (MP_TAC o SPEC `j:num`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* S9: the uniform time t1 for compact sets off Omega_rho *)
  SUBGOAL_THEN
   `!Kd. compact_in (hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)) Kd /\
         DISJOINT Kd (p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl
                                   (dl(rfs_horizon hs) * rp(rfs_horizon hs)))
         ==> ?t1. hs_time hs (hs_count hs) <= t1 /\ t1 < rfs_horizon hs /\
                  !t x. t1 < t /\ t < rfs_horizon hs /\ x IN Kd
                        ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x t U`
  ASSUME_TAC THENL
   [X_GEN_TAC `Kd:(A+num#num#real^3)->bool` THEN STRIP_TAC THEN
    REMOVE_THEN "DIS" (MP_TAC o SPECL [`hs:(A+num#num#real^3)rfs_history`; `C:real`;
      `eps:real`; `rp:real->real`; `gl:(A+num#num#real^3)->real^3^3`;
      `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)) * rp(rfs_horizon hs)`;
      `Kd:(A+num#num#real^3)->bool`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the step *)
  MATCH_MP_TAC P3E_STEP_CORE THEN
  MAP_EVERY EXISTS_TAC [`d0:real`; `h0:real`; `p3_omega (hs:(A+num#num#real^3)rfs_history)`;
                        `gl:(A+num#num#real^3)->real^3^3`; `J:num->bool`;
                        `ee:num->real^3->(A+num#num#real^3)`; `K:(A+num#num#real^3)->bool`;
                        `H:num->real^3->(A+num#num#real^3)`; `RR1:num->real`;
                        `yv:num->(A+num#num#real^3)`] THEN
  ASM_REWRITE_TAC[p3_hscale] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "Y31" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) IN J`))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`;
                 `hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs)`; `J:num->bool`;
                 `ee:num->real^3->(A+num#num#real^3)`;
                 `p3e_fresh (hs_count (hs:(A+num#num#real^3)rfs_history))
                    :num->bool->real^3->(A+num#num#real^3)`;
                 `p3_omega (hs:(A+num#num#real^3)rfs_history)`;
                 `p3_omega_rho (hs_atlas (hs:(A+num#num#real^3)rfs_history) (hs_count hs))
                    (p3_omega hs) gl (dl(rfs_horizon hs) * rp(rfs_horizon hs))`;
                 `K:(A+num#num#real^3)->bool`; `H:num->real^3->(A+num#num#real^3)`;
                 `RR1:num->real`; `dl(rfs_horizon (hs:(A+num#num#real^3)rfs_history)):real`;
                 `i:num`] P3E_HORN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!(x:A+num#num#real^3) s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `p3_horn_set ((H:num->real^3->(A+num#num#real^3)) i)` THEN
  ASM_REWRITE_TAC[]);;

let P3E_LEMMA_15_11_ROUTE = prove
 (`!u:A->bool. P3_LEMMA_15_11_ROUTE_STATEMENT u`,
  REWRITE_TAC[P3_LEMMA_15_11_ROUTE_STATEMENT] THEN MATCH_ACCEPT_TAC P3E_LEMMA_15_11_PRE);;

