(* ========================================================================= *)
(* Unit pc_p2b_cone: the first unit of the no-bad-tube half of MT Thm 10.2   *)
(* (Secs 10.4-10.6).  Neck geometry near the end E of a bad tube: the two    *)
(* sides of a separating neck sphere, the distance gain across a neck        *)
(* (Claim A), a Cauchy chain of necks running into E, the distance to the    *)
(* end dE, the almost-affine behaviour of dE along necks, the level-set      *)
(* lemma (LS) and the lower half of MT Claim 10.31.  The neck facts used are *)
(* APX_NECK_DIST, APX_NECK_OVERLAP, APX_NECK_SCALAR_COMPARE and              *)
(* APX_LEVEL_SPHERE_SEP.  The general lemmas (bad-tube data, the two sides   *)
(* of a neck sphere, Claim A) are in the shared unit pc_p2b_conelib.         *)
(* ========================================================================= *)

needs "src/pc_p2b_conestmts.ml";;
needs "src/pc_p2b_conelib.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_cmp_ltpg.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_grg_distcont.ml";;
needs "src/pc_mfd_restrict.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The neck scale constants.  p2bk_good_eps u eps collects the quantitative  *)
(* neck facts used below: eps <= 1/100 (so APX_NECK_EXIT and                 *)
(* APX_NECK_DIST_UPPER have factors close to 1), the scalar curvature on an  *)
(* eps-neck lies in [R(x)/2, 3R(x)/2] (APX_NECK_CURV and                     *)
(* APX_NECK_SCALAR_COMPARE), and overlapping eps-necks have scales within a  *)
(* factor 2 (APX_NECK_OVERLAP).  All small eps are good.                     *)
(* ========================================================================= *)

let p2bk_good_eps = new_definition
 `p2bk_good_eps (u:B->bool) (eps:real) <=>
    &0 < eps /\ eps <= &1 / &100 /\
    (!top atlas (g:B->real^3^3) x e y.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps
        ==> mfd_scalar atlas g x / &2 <= mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= &3 / &2 * mfd_scalar atlas g x) /\
    (!top atlas (g:B->real^3^3) x e x' e' p.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        rfs_neck (top,atlas) g eps x' e' /\
        p IN IMAGE e (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps)
        ==> mfd_scalar atlas g x' <= &2 * mfd_scalar atlas g x)`;;

let P2BK_GOOD_EPS = prove
 (`?eps1. &0 < eps1 /\ !eps. &0 < eps /\ eps <= eps1 ==> p2bk_good_eps (u:B->bool) eps`,
  MP_TAC(ISPEC `u:B->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `ea:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  MP_TAC(ISPEC `u:B->bool` APX_NECK_OVERLAP) THEN REWRITE_TAC[APX_NECK_OVERLAP_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `eb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ovl"))) THEN
  EXISTS_TAC `min (min ea eb) (&1 / &100)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN REWRITE_TAC[p2bk_good_eps] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                         `g:B->real^3^3`; `x:B`; `e:real^3->B`; `y:real^3`] THEN
    STRIP_TAC THEN MATCH_MP_TAC APX_NECK_SCALAR_COMPARE THEN
    EXISTS_TAC `top:B topology` THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "curv" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                       `g:B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`;
                                       `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                         `g:B->real^3^3`; `x:B`; `e:real^3->B`; `x':B`; `e':real^3->B`;
                         `p:B`] THEN
    STRIP_TAC THEN
    REMOVE_THEN "ovl" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                      `g:B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`;
                                      `x':B`; `e':real^3->B`; `p:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `abs(a - &1) <= &1 / &2 ==> a <= &3 / &2`;
                 REAL_LE_LDIV_EQ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `abs(a - &1) <= &1 / &2 ==> a <= &3 / &2`)) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Separating necks of the tube and their two sides.  A p2bk_sepneck is a    *)
(* neck whose central sphere separates the inner end of the tube (H w, |w|   *)
(* near 1) from the outer end (|w| near 2).  p2bk_out and p2bk_in are the    *)
(* two sides of its central sphere, defined through the ends, so they do not *)
(* depend on the separation radii.                                           *)
(* ========================================================================= *)

let p2bk_sepneck = new_definition
 `p2bk_sepneck (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
               (H:real^3->B) (eps:real) (x:B) (e:real^3->B) <=>
    rfs_neck (top,atlas) g eps x e /\
    ?r2 r3. &1 < r2 /\ r2 < r3 /\ r3 < &2 /\
            !w1 w2. &1 < norm w1 /\ norm w1 < r2 /\ r3 < norm w2 /\ norm w2 < &2
                    ==> apx_separates top (IMAGE e (sphere(vec 0,&1))) (H w1) (H w2)`;;

let p2bk_out = new_definition
 `p2bk_out (top:B topology) (H:real^3->B) (e:real^3->B) (p:B) <=>
    ?r. r < &2 /\
        !w. r < norm w /\ norm w < &2
            ==> connected_component_of
                  (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p (H w)`;;

let p2bk_in = new_definition
 `p2bk_in (top:B topology) (H:real^3->B) (e:real^3->B) (p:B) <=>
    ?r. &1 < r /\
        !w. &1 < norm w /\ norm w < r
            ==> connected_component_of
                  (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p (H w)`;;

(* The ends of the tube are connected (images of annuli). *)

let P2BK_TUBE_END_CONNECTED = prove
 (`!top atlas (H:real^3->B) a b.
     mfd_param top atlas (annulus (&1) (&2)) H /\ &1 <= a /\ b <= &2
     ==> connected_in top (IMAGE H (annulus a b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `annulus (&1) (&2):real^3->bool`] THEN
  ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3; annulus; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* For a separating neck, the side of a point off the sphere is that of     *)
(* the outer or the inner end, the outer and inner points are separated, the *)
(* two halves of the neck lie on different sides, and the ends lie on their  *)
(* own sides.                                                                *)

let P2BK_SEPNECK_SIDES = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e
     ==> (!p. p IN topspace top DIFF IMAGE e (sphere(vec 0,&1))
              ==> p2bk_out top H e p \/ p2bk_in top H e p) /\
         (!p q. p2bk_in top H e p /\ p2bk_out top H e q
                ==> ~(connected_component_of
                        (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p q)) /\
         (!p q. p2bk_out top H e p /\ p2bk_out top H e q
                ==> connected_component_of
                      (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p q) /\
         (!p q. p2bk_in top H e p /\ p2bk_in top H e q
                ==> connected_component_of
                      (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p q) /\
         (?r. r < &2 /\ !w. r < norm w /\ norm w < &2 ==> p2bk_out top H e (H w)) /\
         (?r. &1 < r /\ !w. &1 < norm w /\ norm w < r ==> p2bk_in top H e (H w)) /\
         ((!y. y IN annulus (exp(--inv eps / sqrt(&2))) (&1) ==> p2bk_in top H e (e y)) /\
          (!y. y IN annulus (&1) (exp(inv eps / sqrt(&2))) ==> p2bk_out top H e (e y)) \/
          (!y. y IN annulus (&1) (exp(inv eps / sqrt(&2))) ==> p2bk_in top H e (e y)) /\
          (!y. y IN annulus (exp(--inv eps / sqrt(&2))) (&1) ==> p2bk_out top H e (e y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2bk_sepneck]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `S = IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `X = subtopology top (topspace top DIFF (S:B->bool))` THEN
  ABBREV_TAC `w1:real^3 = ((&1 + r2) / &2) % basis 1` THEN
  ABBREV_TAC `w2:real^3 = ((r3 + &2) / &2) % basis 1` THEN
  SUBGOAL_THEN `norm(w1:real^3) = (&1 + r2) / &2 /\ norm(w2:real^3) = (r3 + &2) / &2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w1"; "w2"] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_separates top S ((H:real^3->B) w1) (H w2)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `(H:real^3->B) w1`; `(H:real^3->B) w2`]
    P2BK_NECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  (* the outer end: points H w with r3 < |w| < 2 are connected to H w2 off S *)
  SUBGOAL_THEN `!w. r3 < norm w /\ norm w < &2
                    ==> connected_component_of (X:B topology) ((H:real^3->B) w) (H w2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN EXPAND_TAC "X" THEN
    REWRITE_TAC[connected_component_of] THEN
    EXISTS_TAC `IMAGE (H:real^3->B) (annulus r3 (&2))` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BK_TUBE_END_CONNECTED THEN
      EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM; IN_DIFF] THEN
      X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `apx_separates top S ((H:real^3->B) w1) (H v)` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[apx_separates; IN_DIFF] THEN SIMP_TAC[]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^3` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w2:real^3` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. &1 < norm w /\ norm w < r2
                    ==> connected_component_of (X:B topology) ((H:real^3->B) w) (H w1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN EXPAND_TAC "X" THEN
    REWRITE_TAC[connected_component_of] THEN
    EXISTS_TAC `IMAGE (H:real^3->B) (annulus (&1) r2)` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BK_TUBE_END_CONNECTED THEN
      EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM; IN_DIFF] THEN
      X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `apx_separates top S ((H:real^3->B) v) (H w2)` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[apx_separates; IN_DIFF] THEN SIMP_TAC[]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^3` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w1:real^3` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* out and in through the base points *)
  SUBGOAL_THEN `!p:B. p2bk_out top H e p <=> connected_component_of (X:B topology) p (H w2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:B` THEN REWRITE_TAC[p2bk_out] THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `w:real^3 = ((max r r3 + &2) / &2) % basis 1` THEN
      SUBGOAL_THEN `norm(w:real^3) = (max r r3 + &2) / &2` ASSUME_TAC THENL
       [EXPAND_TAC "w" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN EXISTS_TAC `(H:real^3->B) w` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `r3:real`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN EXISTS_TAC `r3:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN EXISTS_TAC `(H:real^3->B) w2` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONNECTED_COMPONENT_OF_SYM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `r3:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:B. p2bk_in top H e p <=> connected_component_of (X:B topology) p (H w1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:B` THEN REWRITE_TAC[p2bk_in] THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `w:real^3 = ((&1 + min r r2) / &2) % basis 1` THEN
      SUBGOAL_THEN `norm(w:real^3) = (&1 + min r r2) / &2` ASSUME_TAC THENL
       [EXPAND_TAC "w" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN EXISTS_TAC `(H:real^3->B) w` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `r2:real`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN EXISTS_TAC `r2:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN EXISTS_TAC `(H:real^3->B) w1` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONNECTED_COMPONENT_OF_SYM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `r2:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `apx_separates top S ((H:real^3->B) w1) (H w2)` THEN
  REWRITE_TAC[apx_separates] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DISJ_SYM] THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`p:B`; `q:B`] THEN STRIP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~connected_component_of (X:B topology) ((H:real^3->B) w1) (H w2)` THEN
    REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS; CONNECTED_COMPONENT_OF_SYM];
    ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS; CONNECTED_COMPONENT_OF_SYM];
    ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS; CONNECTED_COMPONENT_OF_SYM];
    EXISTS_TAC `r3:real` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `r2:real` THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REWRITE_TAC[IN] THEN
    MESON_TAC[CONNECTED_COMPONENT_OF_SYM]]);;


(* ========================================================================= *)
(* Nested sides.  If the central sphere S' of a second separating neck       *)
(* misses S and meets the outer side of the first, then S' lies on that      *)
(* outer side, the inner side of e and S lie on the inner side of e', and    *)
(* the outer side of e' lies in the outer side of e.                         *)
(* ========================================================================= *)

let P2BK_SIDE_COMPONENT = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e p q.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\
     connected_component_of
       (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p q
     ==> (p2bk_out top H e p <=> p2bk_out top H e q) /\
         (p2bk_in top H e p <=> p2bk_in top H e q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bk_out; p2bk_in] THEN
  CONJ_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS; CONNECTED_COMPONENT_OF_SYM]);;

let P2BK_SIDE_CONNECTED = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e C.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\
     connected_in top C /\ DISJOINT C (IMAGE e (sphere(vec 0,&1)))
     ==> (!p q. p IN C /\ q IN C /\ p2bk_out top H e p ==> p2bk_out top H e q) /\
         (!p q. p IN C /\ q IN C /\ p2bk_in top H e p ==> p2bk_in top H e q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!p q. p IN C /\ q IN C
          ==> connected_component_of
                (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))))
                p (q:B)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[connected_component_of] THEN
    EXISTS_TAC `C:B->bool` THEN ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE) THEN
    UNDISCH_TAC `DISJOINT (C:B->bool) (IMAGE (e:real^3->B) (sphere(vec 0,&1)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`; `p:B`; `q:B`]
    P2BK_SIDE_COMPONENT) THEN
  ASM_SIMP_TAC[]);;

let P2BK_NOT_IN_AND_OUT = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e p.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e
     ==> ~(p2bk_in top H e p /\ p2bk_out top H e p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`p:B`; `p:B`] o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
  UNDISCH_TAC `p2bk_in top (H:real^3->B) e (p:B)` THEN REWRITE_TAC[p2bk_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `((&1 + r) / &2) % basis 1:real^3`) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MESON_TAC[CONNECTED_COMPONENT_IN_TOPSPACE]);;

let P2BK_NEST_SPHERE_AUX = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e x' e' C.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\ p2bk_sepneck (top,atlas) g H eps x' e' /\
     DISJOINT (IMAGE e' (sphere(vec 0,&1))) (IMAGE e (sphere(vec 0,&1))) /\
     (!p. p IN IMAGE e' (sphere(vec 0,&1)) ==> p2bk_out top H e p) /\
     (!p. p2bk_in top H e p ==> p2bk_in top H e' p) /\
     C SUBSET rfs_neck_dom eps /\ connected C /\
     (!y:real^3. y IN C /\ ~(norm y = &1) ==> p2bk_in top H e (e y)) /\
     (?y. y IN C /\ ~(norm y = &1)) /\ sphere(vec 0,&1) SUBSET C
     ==> !p. p IN IMAGE e (sphere(vec 0,&1)) ==> p2bk_in top H e' p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (l,t) -> LABEL_TAC l t)
    (zip ["haus"; "conn"; "parH"; "imH"; "sn"; "sn'"; "disj"; "outS'"; "inin";
          "Csub"; "Cconn"; "Cin"; "Cex"; "Csph"] (CONJUNCTS th))) THEN
  REMOVE_THEN "Cex" (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->B)` ASSUME_TAC THENL
   [USE_THEN "sn" (MP_TAC o GEN_REWRITE_RULE I [p2bk_sepneck]) THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:B. q IN IMAGE (e':real^3->B) (sphere(vec 0,&1))
                      ==> ~(p2bk_in top (H:real^3->B) (e:real^3->B) q)`
    (LABEL_TAC "notin") THENL
   [X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2bk_out top (H:real^3->B) (e:real^3->B) q` ASSUME_TAC THENL
     [USE_THEN "outS'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`;
                   `q:B`] P2BK_NOT_IN_AND_OUT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (e:real^3->B) C) (IMAGE (e':real^3->B) (sphere(vec 0,&1)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT (s:B->bool) t <=> !q. q IN s ==> ~(q IN t)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y1:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(y1:real^3) = &1` THENL
     [USE_THEN "disj" (MP_TAC o REWRITE_RULE
        [SET_RULE `DISJOINT (s:B->bool) t <=> !q. q IN t ==> ~(q IN s)`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_SPHERE_0];
      DISCH_TAC THEN
      USE_THEN "notin" (fun th -> MP_TAC(MATCH_MP th (ASSUME
        `(e:real^3->B) y1 IN IMAGE (e':real^3->B) (sphere(vec 0,&1))`))) THEN
      REWRITE_TAC[] THEN USE_THEN "Cin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x':B`; `e':real^3->B`;
                 `IMAGE (e:real^3->B) C`] P2BK_SIDE_CONNECTED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `(e:real^3->B) y0`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "Csph" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "inin" MATCH_MP_TAC THEN USE_THEN "Cin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BK_NEST_SPHERE = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e x' e'.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\ p2bk_sepneck (top,atlas) g H eps x' e' /\
     DISJOINT (IMAGE e' (sphere(vec 0,&1))) (IMAGE e (sphere(vec 0,&1))) /\
     (!p. p IN IMAGE e' (sphere(vec 0,&1)) ==> p2bk_out top H e p) /\
     (!p. p2bk_in top H e p ==> p2bk_in top H e' p)
     ==> !p. p IN IMAGE e (sphere(vec 0,&1)) ==> p2bk_in top H e' p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_sepneck] o
    check (fun th -> can (find_term ((=) `e:real^3->B`)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) = "p2bk_sepneck"
                      with Failure _ -> false))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o
    check (fun th -> can (find_term ((=) `e:real^3->B`)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck"
                      with Failure _ -> false))) THEN
  ABBREV_TAC `a = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `b = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < a /\ a < &1 /\ &1 < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    SUBGOAL_THEN `&0 < inv eps / sqrt(&2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_OF_NUM_LT;
                                                 ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
    MESON_TAC[REAL_EXP_LT_1; REAL_EXP_0; REAL_EXP_MONO_LT; REAL_ARITH
      `&0 < x ==> --x < &0`];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus a b` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "halves") THEN
  REMOVE_THEN "halves" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2BK_NEST_SPHERE_AUX THEN
  MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
                        `x:B`; `x':B`] THENL
   [EXISTS_TAC `{y:real^3 | a < norm y /\ norm y <= &1}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`vec 0:real^3`; `a:real`; `&1`]
        (CONJUNCT1(CONJUNCT2 CONNECTED_ANNULUS))) THEN
      REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `((a + &1) / &2) % basis 1:real^3` THEN
      SIMP_TAC[IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `{y:real^3 | &1 <= norm y /\ norm y < b}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `b:real`]
        (CONJUNCT1(CONJUNCT2(CONJUNCT2 CONNECTED_ANNULUS)))) THEN
      REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `((b + &1) / &2) % basis 1:real^3` THEN
      SIMP_TAC[IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC]]);;

let P2BK_NEST_OUT1 = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e x' e'.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\ p2bk_sepneck (top,atlas) g H eps x' e' /\
     DISJOINT (IMAGE e' (sphere(vec 0,&1))) (IMAGE e (sphere(vec 0,&1))) /\
     p2bk_out top H e x'
     ==> !p. p IN IMAGE e' (sphere(vec 0,&1)) ==> p2bk_out top H e p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e':real^3->B) /\ &0 < eps /\
                (x':B) IN IMAGE e' (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (x':B) e'`) THEN
    REWRITE_TAC[p2bk_sepneck; rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`;
                 `IMAGE (e':real^3->B) (sphere(vec 0,&1))`] P2BK_SIDE_CONNECTED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_SIMP_TAC[APX_UNIT_SPHERE_NECK_DOM; CONNECTED_SPHERE; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> X_GEN_TAC `p:B` THEN DISCH_TAC THEN MATCH_MP_TAC th THEN
                       EXISTS_TAC `x':B` THEN ASM_REWRITE_TAC[]));;

let P2BK_NEST_IN = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e x' e'.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\ p2bk_sepneck (top,atlas) g H eps x' e' /\
     (!p. p IN IMAGE e' (sphere(vec 0,&1)) ==> p2bk_out top H e p)
     ==> !p. p2bk_in top H e p ==> p2bk_in top H e' p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:B` THEN DISCH_THEN(LABEL_TAC "inp") THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x':B`; `e':real^3->B`;
                 `connected_component_of
                    (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))))
                    (p:B)`] P2BK_SIDE_CONNECTED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1)))`;
                     `p:B`] CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
      REWRITE_TAC[SET_RULE `DISJOINT (s:B->bool) t <=> !q. q IN t ==> ~(q IN s)`] THEN
      X_GEN_TAC `q:B` THEN DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [IN] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`; `p:B`; `q:B`]
        P2BK_SIDE_COMPONENT) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`; `q:B`]
        P2BK_NOT_IN_AND_OUT) THEN
      SUBGOAL_THEN `p2bk_out top (H:real^3->B) (e:real^3->B) q` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "sc" o CONJUNCT2) THEN
  USE_THEN "inp" (MP_TAC o GEN_REWRITE_RULE I [p2bk_in]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x':B`; `e':real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `w:real^3 = ((&1 + min r r') / &2) % basis 1` THEN
  SUBGOAL_THEN `&1 < norm(w:real^3) /\ norm w < r /\ norm w < r'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component_of
      (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))))
      (p:B) ((H:real^3->B) w)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "sc" MATCH_MP_TAC THEN EXISTS_TAC `(H:real^3->B) w` THEN
  REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN EXISTS_TAC `(H:real^3->B) w` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONNECTED_COMPONENT_OF_SYM] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r':real`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let P2BK_NEST_OUT2 = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e x' e'.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\ p2bk_sepneck (top,atlas) g H eps x' e' /\
     (!p. p2bk_in top H e p ==> p2bk_in top H e' p) /\
     (!p. p IN IMAGE e (sphere(vec 0,&1)) ==> p2bk_in top H e' p)
     ==> !p. p2bk_out top H e' p ==> p2bk_out top H e p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (l,t) -> LABEL_TAC l t)
    (zip ["haus"; "conn"; "parH"; "imH"; "sn"; "sn'"; "inin"; "Sin"] (CONJUNCTS th))) THEN
  X_GEN_TAC `p:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(p2bk_in top (H:real^3->B) (e':real^3->B) (p:B))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `H:real^3->B`; `eps:real`; `x':B`; `e':real^3->B`;
                   `p:B`] P2BK_NOT_IN_AND_OUT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bk_out top (H:real^3->B) e' (p:B)` THEN REWRITE_TAC[p2bk_out] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `((max r (&1) + &2) / &2) % basis 1:real^3`) THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_EQUIV; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `p2bk_in top (H:real^3->B) (e':real^3->B) (p:B)` MP_TAC THENL
     [USE_THEN "Sin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `p2bk_in top (H:real^3->B) (e:real^3->B) (p:B)` THENL
   [SUBGOAL_THEN `p2bk_in top (H:real^3->B) (e':real^3->B) (p:B)` MP_TAC THENL
     [USE_THEN "inin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `p:B` o CONJUNCT1) THEN ASM_REWRITE_TAC[IN_DIFF]);;

let P2BK_NEST = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e x' e'.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\ p2bk_sepneck (top,atlas) g H eps x' e' /\
     DISJOINT (IMAGE e' (sphere(vec 0,&1))) (IMAGE e (sphere(vec 0,&1))) /\
     p2bk_out top H e x'
     ==> (!p. p IN IMAGE e' (sphere(vec 0,&1)) ==> p2bk_out top H e p) /\
         (!p. p2bk_in top H e p ==> p2bk_in top H e' p) /\
         (!p. p IN IMAGE e (sphere(vec 0,&1)) ==> p2bk_in top H e' p) /\
         (!p. p2bk_out top H e' p ==> p2bk_out top H e p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p:B. p IN IMAGE (e':real^3->B) (sphere(vec 0,&1)) ==> p2bk_out top H e p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_NEST_OUT1 THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
                          `x:B`; `x':B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:B. p2bk_in top H (e:real^3->B) p ==> p2bk_in top H (e':real^3->B) p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_NEST_IN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
                          `x:B`; `x':B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:B. p IN IMAGE (e:real^3->B) (sphere(vec 0,&1)) ==> p2bk_in top H e' p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_NEST_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
                          `x:B`; `x':B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BK_NEST_OUT2 THEN
  MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
                        `x:B`; `x':B`] THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The tube predicate and the next neck.  p2bk_tube collects what the end    *)
(* analysis uses from a bad tube (at neck scale 2 eps, with good constants). *)
(* From a separating neck centred at x one finds a point z just outside the  *)
(* neck on its outer side: the outer side is connected, meets the neck in    *)
(* its outer half and contains points of huge scalar curvature, so it meets  *)
(* the frontier of the neck; d(x,z) <= 2 h / eps'.                           *)
(* ========================================================================= *)

let p2bk_tube = new_definition
 `p2bk_tube (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
            (H:real^3->B) (eps:real) <=>
    hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ mfd_param top atlas (annulus (&1) (&2)) H /\
    IMAGE H (annulus (&1) (&2)) = topspace top /\
    p2bk_good_eps (UNIV:B->bool) eps /\
    (?D. !x y. x IN topspace top /\ y IN topspace top
               ==> mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y <= D) /\
    (!B0. ?r. r < &2 /\
              !y. r < norm y /\ norm y < &2 ==> B0 <= mfd_scalar atlas g (H y)) /\
    (?B0. !y. y IN annulus (&1) (&3 / &2) ==> mfd_scalar atlas g (H y) <= B0) /\
    (?r1. &1 < r1 /\ r1 < &2 /\
          !y. r1 < norm y /\ norm y < &2 ==> ?e. p2bk_sepneck (top,atlas) g H eps (H y) e)`;;

let P2BK_TUBE_OF_BAD = prove
 (`!eps top atlas (g:B->real^3^3) V H.
     p2b_bad_tube eps (top,atlas) g V H /\ p2bk_good_eps (UNIV:B->bool) (&2 * eps)
     ==> p2bk_tube (top,atlas) g H (&2 * eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                     (real->B->real^3^3)`; `H:real^3->B`] P2BK_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bk_tube] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `p2b_bad_tube eps (top,atlas) (g:B->real^3^3) V H` THEN
    REWRITE_TAC[p2b_bad_tube] THEN MESON_TAC[];
    EXISTS_TAC `r1:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real^3->B` THEN ASM_REWRITE_TAC[p2bk_sepneck] THEN
    MAP_EVERY EXISTS_TAC [`r2:real`; `r3:real`] THEN ASM_REWRITE_TAC[]]);;

(* Scalar curvature is bounded on each inner part, the image under H of    *)
(* the points w with 1 < |w| <= r, for r < 2.                              *)

let P2BK_INNER_R_BOUND = prove
 (`!top atlas (g:B->real^3^3) H eps r.
     p2bk_tube (top,atlas) g H eps /\ r < &2
     ==> ?B. &0 < B /\
             !w. &1 < norm w /\ norm w <= r ==> mfd_scalar atlas g (H w) <= B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_tube] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?B1. !w. &3 / &2 <= norm w /\ norm w <= max r (&3 / &2)
                         ==> mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w) <= B1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact {w:real^3 | &3 / &2 <= norm w /\ norm w <= max r (&3 / &2)}`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `{w:real^3 | &3 / &2 <= norm w /\ norm w <= max r (&3 / &2)} =
                    cball(vec 0,max r (&3 / &2)) DIFF ball(vec 0,&3 / &2)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `{w:real^3 | &3 / &2 <= norm w /\ norm w <= max r (&3 / &2)} SUBSET
                  annulus (&1) (&2)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`]
      MFD_SCALAR_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `annulus (&1) (&2):real^3->bool`; `H:real^3->B`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `compact_in euclideanreal
                    (IMAGE (mfd_scalar atlas (g:B->real^3^3) o (H:real^3->B))
                           {w:real^3 | &3 / &2 <= norm w /\ norm w <= max r (&3 / &2)})`
    MP_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (annulus (&1) (&2):real^3->bool)` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN EXISTS_TAC `B1:real` THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `max (&1) (max B0 B1)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `norm(w:real^3) < &3 / &2` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `annulus (&1) (&3 / &2):real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `B1:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* Points of an eps-neck lie within 2 h / eps of its centre. *)

let P2BK_NECK_RADIUS = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e y.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100 /\
     y IN rfs_neck_dom eps
     ==> mfd_joinable (top,atlas) x (e y) /\
         mfd_dist (top,atlas) g x (e y) <=
         &2 * inv(sqrt(mfd_scalar atlas g x)) * inv eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `(e:real^3->B) u0`; `e:real^3->B`; `u0:real^3`; `y:real^3`]
    APX_NECK_DIST_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((e:real^3->B) u0))) *
              (abs(apx_sval y) + sqrt(&2) * pi)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((e:real^3->B) u0)))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) <= &101 / &100 /\ sqrt(&2) * pi <= &5 /\ &100 <= inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &10 / &3` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MP_TAC PI_POS THEN REAL_ARITH_TAC;
        MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `inv(&1 / &100) <= inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h * (abs(apx_sval y) + sqrt(&2) * pi) <=
                (&101 / &100) * h * (inv eps + inv eps / &20)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(&101 / &100) * h * (inv eps + inv eps / &20) <= &2 * h * inv eps`
    MP_TAC THENL
     [SUBGOAL_THEN `(&101 / &100) * h * (inv eps + inv eps / &20) =
                    (&2121 / &2000) * (h * inv eps)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * h * inv eps = &2 * (h * inv eps)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* Distance from a fixed point is continuous; so it is bounded on the       *)
(* closure of a set by any bound on the set.                                 *)

let P2BK_DIST_SECTION_CONTINUOUS = prove
 (`!top atlas (g:B->real^3^3) (x:B).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> continuous_map (top,euclideanreal) (\p. mfd_dist (top,atlas) g x p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`]
    MFD_DIST_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\p. mfd_dist (top,atlas) (g:B->real^3^3) x p) =
                (\(a,b). mfd_dist (top,atlas) g a b) o (\p:B. (x,p))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `prod_topology (top:B topology) top` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST]);;

let P2BK_CLOSURE_DIST_LE = prove
 (`!top atlas (g:B->real^3^3) (x:B) S c z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!p. p IN S ==> mfd_dist (top,atlas) g x p <= c) /\ z IN top closure_of S
     ==> mfd_dist (top,atlas) g x z <= c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`] P2BK_DIST_SECTION_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed_in top {p:B | p IN topspace top /\
                                     (\p. mfd_dist (top,atlas) (g:B->real^3^3) x p) p IN
                                     {t:real | t <= c}}` MP_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
    ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `top closure_of (S:B->bool) SUBSET
                {p:B | p IN topspace top /\ mfd_dist (top,atlas) (g:B->real^3^3) x p <= c}`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:B` o REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* The radii of the neck domain. *)

let P2BK_NECK_AB = prove
 (`!eps. &0 < eps
         ==> &0 < exp(--inv eps / sqrt(&2)) /\ exp(--inv eps / sqrt(&2)) < &1 /\
             &1 < exp(inv eps / sqrt(&2)) /\
             rfs_neck_dom eps =
             annulus (exp(--inv eps / sqrt(&2))) (exp(inv eps / sqrt(&2)))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; REAL_EXP_POS_LT] THEN
  SUBGOAL_THEN `&0 < inv eps / sqrt(&2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
  MESON_TAC[REAL_EXP_LT_1; REAL_EXP_0; REAL_EXP_MONO_LT; REAL_ARITH `&0 < x ==> --x < &0`]);;

(* The closure of an eps-neck lies within 2 h / eps of its centre. *)

let P2BK_NECK_CLOSURE_DIST = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100
     ==> x IN topspace top /\
         !z. z IN top closure_of (IMAGE e (rfs_neck_dom eps))
             ==> mfd_dist (top,atlas) g x z <=
                 &2 * inv(sqrt(mfd_scalar atlas g x)) * inv eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->B`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:B->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `open_in top (IMAGE (e:real^3->B) (rfs_neck_dom eps))` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BK_CLOSURE_DIST_LE THEN
  EXISTS_TAC `IMAGE (e:real^3->B) (rfs_neck_dom eps)` THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `y:real^3`] P2BK_NECK_RADIUS) THEN
  ASM_SIMP_TAC[]);;

(* A point of the outer half of a separating neck. *)

let P2BK_OUT_HALF_POINT = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e
     ==> ?y. y IN rfs_neck_dom eps /\ p2bk_out top H e (e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [MP_TAC(ASSUME `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (x:B) e`) THEN
    REWRITE_TAC[p2bk_sepneck; rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o el 6 o CONJUNCTS) THEN
  MP_TAC(SPEC `eps:real` P2BK_NECK_AB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `b = exp(inv eps / sqrt(&2))` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN (MP_TAC o CONJUNCT2)) THENL
   [DISCH_TAC THEN EXISTS_TAC `((&1 + b) / &2) % basis 1:real^3` THEN CONJ_TAC THENL
     [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN EXISTS_TAC `((a + &1) / &2) % basis 1:real^3` THEN CONJ_TAC THENL
     [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC]]);;

(* A far outer point of large curvature, outside the neck. *)

let P2BK_FAR_OUT_POINT = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e.
     p2bk_tube (top,atlas) g H eps /\ p2bk_sepneck (top,atlas) g H eps x e
     ==> ?q. q IN topspace top /\ p2bk_out top H e q /\
             ~(q IN IMAGE e (rfs_neck_dom eps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_sepneck]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ro:real` STRIP_ASSUME_TAC o el 4 o CONJUNCTS) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `rb:real` STRIP_ASSUME_TAC o
    SPEC `&2 * mfd_scalar atlas (g:B->real^3^3) x` o
    check (fun th -> is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  ABBREV_TAC `wq:real^3 = ((max (max ro rb) (&1) + &2) / &2) % basis 1` THEN
  SUBGOAL_THEN `ro < norm(wq:real^3) /\ rb < norm wq /\ &1 < norm wq /\ norm wq < &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "wq" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(H:real^3->B) wq` THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (H:real^3->B) (annulus (&1) (&2)) = topspace top` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ro:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) ((e:real^3->B) y) <=
                  &3 / &2 * mfd_scalar atlas g x` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                    `g:B->real^3^3`; `x:B`; `e:real^3->B`; `y:real^3`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `rfs_neck_dom`)) (concl th) &&
                         can (find_term ((=) `&3 / &2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * mfd_scalar atlas (g:B->real^3^3) x <=
                  mfd_scalar atlas g ((H:real^3->B) wq)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rb:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas (g:B->real^3^3) x` THEN REAL_ARITH_TAC]);;

(* The component of an outer point outside the neck meets the frontier.    *)

let P2BK_OUT_FRONTIER = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e q.
     hausdorff_space top /\ connected_space top /\
     mfd_param top atlas (annulus (&1) (&2)) H /\
     IMAGE H (annulus (&1) (&2)) = topspace top /\
     p2bk_sepneck (top,atlas) g H eps x e /\
     q IN topspace top /\ p2bk_out top H e q /\ ~(q IN IMAGE e (rfs_neck_dom eps))
     ==> ?z. z IN topspace top /\ p2bk_out top H e z /\
             ~(z IN IMAGE e (rfs_neck_dom eps)) /\
             z IN top closure_of (IMAGE e (rfs_neck_dom eps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_sepneck]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->B`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:B->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sides") THEN
  SUBGOAL_THEN `~((q:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [UNDISCH_TAC `~((q:B) IN IMAGE (e:real^3->B) (rfs_neck_dom eps))` THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`;
                 `connected_component_of
                    (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))))
                    (q:B)`;
                 `IMAGE (e:real^3->B) (rfs_neck_dom eps)`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1)))`;
                     `q:B`] CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_OUT_HALF_POINT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `(e:real^3->B) y` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC I [IN] THEN USE_THEN "sides" (MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN EXISTS_TAC `q:B` THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC I [IN] THEN
        REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF] THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:B` (CONJUNCTS_THEN2 (LABEL_TAC "zc") STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "zc" (ASSUME_TAC o GEN_REWRITE_RULE I [IN]) THEN CONJ_TAC THENL
   [UNDISCH_TAC `(z:B) IN top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps)` THEN
    MP_TAC(ISPECL [`top:B topology`; `IMAGE (e:real^3->B) (rfs_neck_dom eps)`]
      CLOSURE_OF_SUBSET_TOPSPACE) THEN
    SET_TAC[];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`; `q:B`; `z:B`]
      P2BK_SIDE_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let P2BK_NEXT_POINT = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e.
     p2bk_tube (top,atlas) g H eps /\ p2bk_sepneck (top,atlas) g H eps x e
     ==> ?z. z IN topspace top /\ p2bk_out top H e z /\
             ~(z IN IMAGE e (rfs_neck_dom eps)) /\
             z IN top closure_of (IMAGE e (rfs_neck_dom eps)) /\
             mfd_dist (top,atlas) g x z <= &2 * inv(sqrt(mfd_scalar atlas g x)) * inv eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_FAR_OUT_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:B` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`; `q:B`] P2BK_OUT_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_sepneck]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`] P2BK_NECK_CLOSURE_DIST) THEN
  ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* The chain of necks.  A neck centred at a point z' of the closure of the   *)
(* neck N_z overlaps N_z, so the scales are within a factor 2; if z' lies    *)
(* outside N_z the central spheres are disjoint (the exit length h/eps beats *)
(* the sphere diameter of order h); the sides nest.  By dependent choice we  *)
(* get a chain of separating necks running outwards.                         *)
(* ========================================================================= *)

let P2BK_OVERLAP_CLOSURE = prove
 (`!top atlas (g:B->real^3^3) eps (z:B) e z' e'.
     p2bk_good_eps (UNIV:B->bool) eps /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps z e /\ rfs_neck (top,atlas) g eps z' e' /\
     z' IN top closure_of (IMAGE e (rfs_neck_dom eps))
     ==> mfd_scalar atlas g z <= &2 * mfd_scalar atlas g z' /\
         mfd_scalar atlas g z' <= &2 * mfd_scalar atlas g z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p:B. p IN IMAGE (e:real^3->B) (rfs_neck_dom eps) INTER
                     IMAGE (e':real^3->B) (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z':B) IN top closure_of (IMAGE e (rfs_neck_dom eps))` THEN
    REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (e':real^3->B) (rfs_neck_dom eps)` o CONJUNCT2) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o
      check (fun th -> can (find_term ((=) `e':real^3->B`)) (concl th))) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e':real^3->B`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(z':B) IN IMAGE (e':real^3->B) (sphere(vec 0,&1))` THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`top:B topology`; `e':real^3->B`; `e:real^3->B`; `p:B`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MAP_EVERY EXISTS_TAC [`top:B topology`; `e:real^3->B`; `e':real^3->B`; `p:B`] THEN
    ASM_REWRITE_TAC[]]);;

(* Two small arithmetic facts for the scale comparisons. *)

let P2BK_LE_MUL4 = prove
 (`!a b c d a' b' c' d'.
     &0 <= a /\ a <= a' /\ &0 <= b /\ b <= b' /\ &0 <= c /\ c <= c' /\ &0 <= d /\ d <= d'
     ==> a * b * c * d <= a' * b' * c' * d'`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let P2BK_SCALE_COMPARE = prove
 (`!R R'. &0 < R /\ &0 < R' /\ R <= &2 * R'
          ==> inv(sqrt R') <= sqrt(&2) * inv(sqrt R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SQRT_INV; GSYM SQRT_MUL] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  SUBGOAL_THEN `&2 * inv R - inv R' = (&2 * R' - R) / (R * R')` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_FIELD
      `~(R = &0) /\ ~(R' = &0) ==> &2 * inv R - inv R' = (&2 * R' - R) / (R * R')`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * R' - R) / (R * R')` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let P2BK_SPHERES_DISJOINT = prove
 (`!top atlas (g:B->real^3^3) eps (z:B) e z' e'.
     hausdorff_space top /\ riemannian_metric atlas g /\ eps <= &1 / &100 /\
     rfs_neck (top,atlas) g eps z e /\ rfs_neck (top,atlas) g eps z' e' /\
     ~(z' IN IMAGE e (rfs_neck_dom eps)) /\
     mfd_scalar atlas g z <= &2 * mfd_scalar atlas g z'
     ==> DISJOINT (IMAGE e' (sphere(vec 0,&1))) (IMAGE e (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `DISJOINT (s:B->bool) t <=> !p. p IN s ==> ~(p IN t)`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `u':real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; NOT_EXISTS_THM] THEN X_GEN_TAC `u:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o
    check (fun th -> can (find_term ((=) `e':real^3->B`)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck"
                      with Failure _ -> false))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o
    check (fun th -> can (find_term ((=) `e:real^3->B`)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck"
                      with Failure _ -> false))) THEN
  UNDISCH_TAC `(z':B) IN IMAGE (e':real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u0:real^3) IN rfs_neck_dom eps /\ (u':real^3) IN rfs_neck_dom eps /\
                (u:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  (* upper bound: e' u' and z' = e' u0 lie on the sphere of e' *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `z':B`; `e':real^3->B`; `u':real^3`; `u0:real^3`]
    APX_NECK_DIST_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
  (* lower bound: every curve from e u = e' u' to z' leaves the neck of e *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `(e':real^3->B) u'`; `z':B`;
                 `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z)) * inv eps`]
    APX_DIST_GE_CURVES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `z:B`; `e:real^3->B`; `u:real^3`; `gamma:real->B`;
                   `&0`; `&1`] APX_NECK_EXIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_ABS_0; REAL_SUB_RZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* compare the scales *)
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z')) <=
                sqrt(&2) * inv(sqrt(mfd_scalar atlas g z))` MP_TAC THENL
   [MATCH_MP_TAC P2BK_SCALE_COMPARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z)) /\
                &0 < inv(sqrt(mfd_scalar atlas g z'))` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z))` THEN
  ABBREV_TAC `h' = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z'))` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&99 / &100 <= sqrt(&1 - eps) /\ sqrt(&1 + eps) <= &2 /\
                sqrt(&2) <= &3 / &2 /\ pi <= &4 /\ &100 <= inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC PI2_BOUNDS THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `inv(&1 / &100) <= inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h' <= &3 / &2 * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&2) * h` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h' * sqrt(&2) * pi <= &2 * (&3 / &2 * h) * &3 / &2 * &4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_LE_MUL4 THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE; REAL_POS; PI_POS_LE] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&99 * h <= sqrt(&1 - eps) * h * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&99 / &100 * h * &100` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BK_NEXT_NECK = prove
 (`!top atlas (g:B->real^3^3) H eps (e0:real^3->B) (z:B) e.
     p2bk_tube (top,atlas) g H eps /\
     (!p. p2bk_out top H e0 p ==> ?e'. p2bk_sepneck (top,atlas) g H eps p e') /\
     p2bk_sepneck (top,atlas) g H eps z e /\
     (!p. p2bk_out top H e p ==> p2bk_out top H e0 p)
     ==> ?z' e'. p2bk_sepneck (top,atlas) g H eps z' e' /\
                 (!p. p2bk_out top H e' p ==> p2bk_out top H e0 p) /\
                 p2bk_out top H e z' /\ ~(z' IN IMAGE e (rfs_neck_dom eps)) /\
                 mfd_dist (top,atlas) g z z' <=
                 &2 * inv(sqrt(mfd_scalar atlas g z)) * inv eps /\
                 mfd_scalar atlas g z <= &2 * mfd_scalar atlas g z' /\
                 mfd_scalar atlas g z' <= &2 * mfd_scalar atlas g z /\
                 (!p. p2bk_in top H e p ==> p2bk_in top H e' p) /\
                 (!p. p2bk_out top H e' p ==> p2bk_out top H e p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:B`; `e:real^3->B`] P2BK_NEXT_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z':B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e':real^3->B. p2bk_sepneck (top,atlas) g H eps z' e'`
  (X_CHOOSE_TAC `e':real^3->B`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`z':B`; `e':real^3->B`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps z e /\ rfs_neck (top,atlas) g eps z' e'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2bk_sepneck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `z:B`; `e:real^3->B`; `z':B`; `e':real^3->B`]
    P2BK_OVERLAP_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (e':real^3->B) (sphere(vec 0,&1)))
                         (IMAGE (e:real^3->B) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_SPHERES_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `eps:real`; `z:B`; `z':B`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[p2bk_good_eps];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:B`; `e:real^3->B`; `z':B`; `e':real^3->B`]
    P2BK_NEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let P2BK_CHAIN = prove
 (`!top atlas (g:B->real^3^3) H eps (x0:B) e0.
     p2bk_tube (top,atlas) g H eps /\ p2bk_sepneck (top,atlas) g H eps x0 e0 /\
     (!p. p2bk_out top H e0 p ==> ?e'. p2bk_sepneck (top,atlas) g H eps p e')
     ==> ?z es. z 0 = x0 /\ es 0 = e0 /\
                (!k. p2bk_sepneck (top,atlas) g H eps (z k) (es k)) /\
                (!k p. p2bk_out top H (es k) p ==> p2bk_out top H e0 p) /\
                (!k. p2bk_out top H (es k) (z(SUC k)) /\
                     ~(z(SUC k) IN IMAGE (es k) (rfs_neck_dom eps)) /\
                     mfd_dist (top,atlas) g (z k) (z(SUC k)) <=
                     &2 * inv(sqrt(mfd_scalar atlas g (z k))) * inv eps /\
                     mfd_scalar atlas g (z k) <= &2 * mfd_scalar atlas g (z(SUC k)) /\
                     mfd_scalar atlas g (z(SUC k)) <= &2 * mfd_scalar atlas g (z k) /\
                     (!p. p2bk_in top H (es k) p ==> p2bk_in top H (es(SUC k)) p) /\
                     (!p. p2bk_out top H (es(SUC k)) p ==> p2bk_out top H (es k) p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n:num (ze:B#(real^3->B)).
       p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (FST ze) (SND ze) /\
       (!p. p2bk_out top H (SND ze) p ==> p2bk_out top H e0 p)`;
    `\n:num (ze:B#(real^3->B)) (ze':B#(real^3->B)).
       p2bk_out top H (SND ze) (FST ze') /\
       ~(FST ze' IN IMAGE (SND ze) (rfs_neck_dom eps)) /\
       mfd_dist (top,atlas) (g:B->real^3^3) (FST ze) (FST ze') <=
       &2 * inv(sqrt(mfd_scalar atlas g (FST ze))) * inv eps /\
       mfd_scalar atlas g (FST ze) <= &2 * mfd_scalar atlas g (FST ze') /\
       mfd_scalar atlas g (FST ze') <= &2 * mfd_scalar atlas g (FST ze) /\
       (!p. p2bk_in top H (SND ze) p ==> p2bk_in top H (SND ze') p) /\
       (!p. p2bk_out top H (SND ze') p ==> p2bk_out top H (SND ze) p)`;
    `(x0:B,e0:real^3->B)`] DEPENDENT_CHOICE_FIXED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:B`; `e:real^3->B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `e0:real^3->B`; `z:B`; `e:real^3->B`]
      P2BK_NEXT_NECK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z':B` (X_CHOOSE_THEN `e':real^3->B` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`z':B`; `e':real^3->B`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->B#(real^3->B)` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`\k. FST((f:num->B#(real^3->B)) k)`;
                        `\k. SND((f:num->B#(real^3->B)) k)`] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* The chain runs into the end at finite distance.  A point p0 behind the    *)
(* first neck stays behind all of them (the inner sides nest), so d(p0, z k) *)
(* gains at least h_k / (2 eps) at each step (Claim A); the tube has finite  *)
(* diameter, so the scales h_k are summable and the chain is d-Cauchy.       *)
(* ========================================================================= *)

let P2BK_CHAIN_IN = prove
 (`!(es:num->real^3->B) top H p.
     (!k p. p2bk_in top H (es k) p ==> p2bk_in top H (es(SUC k)) p) /\
     p2bk_in top H (es 0) p
     ==> !k. p2bk_in top H (es k) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[]);;

let P2BK_IN_TOPSPACE = prove
 (`!top (H:real^3->B) e p.
     p2bk_in top H e p ==> p IN topspace top DIFF IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `((&1 + r) / &2) % basis 1:real^3`) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let P2BK_OUT_TOPSPACE = prove
 (`!top (H:real^3->B) e p.
     p2bk_out top H e p ==> p IN topspace top DIFF IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_out] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `((max r (&1) + &2) / &2) % basis 1:real^3`) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let P2BK_CHAIN_GAIN1 = prove
 (`!top atlas (g:B->real^3^3) H eps (z:num->B) es p0 k.
     p2bk_tube (top,atlas) g H eps /\
     p2bk_sepneck (top,atlas) g H eps (z k) (es k) /\
     p2bk_out top H (es k) (z(SUC k)) /\
     ~(z(SUC k) IN IMAGE (es k) (rfs_neck_dom eps)) /\
     p2bk_in top H (es k) p0
     ==> mfd_dist (top,atlas) g p0 (z k) +
         inv(sqrt(mfd_scalar atlas g (z k))) * inv(&2 * eps)
         <= mfd_dist (top,atlas) g p0 (z(SUC k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps ((z:num->B) k) (es k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bk_sepneck]; ALL_TAC] THEN
  SUBGOAL_THEN `(p0:B) IN topspace top DIFF IMAGE ((es:num->real^3->B) k) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_IN_TOPSPACE THEN EXISTS_TAC `H:real^3->B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(connected_component_of
                   (subtopology top (topspace top DIFF
                      IMAGE ((es:num->real^3->B) k) (sphere(vec 0,&1))))
                   (p0:B) ((z:num->B)(SUC k)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `H:real^3->B`; `eps:real`; `(z:num->B) k`;
                   `(es:num->real^3->B) k`] P2BK_SEPNECK_SIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (p0:B) ((z:num->B)(SUC k))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`p0:B`; `(z:num->B)(SUC k)`] o
      check (fun th -> can (find_term ((=) `D:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(p0:B) IN topspace top DIFF
                      IMAGE ((es:num->real^3->B) k) (sphere(vec 0,&1))` THEN
        SIMP_TAC[IN_DIFF];
        MP_TAC(ISPECL [`top:B topology`; `H:real^3->B`; `(es:num->real^3->B) k`;
                       `(z:num->B)(SUC k)`] P2BK_OUT_TOPSPACE) THEN ASM_SIMP_TAC[IN_DIFF]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BK_CROSS_GAIN THEN EXISTS_TAC `(es:num->real^3->B) k` THEN
  ASM_REWRITE_TAC[]);;

let P2BK_CHAIN_GAIN = prove
 (`!top atlas (g:B->real^3^3) H eps (z:num->B) es p0.
     p2bk_tube (top,atlas) g H eps /\
     (!k. p2bk_sepneck (top,atlas) g H eps (z k) (es k)) /\
     (!k. p2bk_out top H (es k) (z(SUC k)) /\
          ~(z(SUC k) IN IMAGE (es k) (rfs_neck_dom eps))) /\
     (!k. p2bk_in top H (es k) p0)
     ==> !k. mfd_dist (top,atlas) g p0 (z k) +
             inv(sqrt(mfd_scalar atlas g (z k))) * inv(&2 * eps)
             <= mfd_dist (top,atlas) g p0 (z(SUC k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_CHAIN_GAIN1 THEN
  MAP_EVERY EXISTS_TAC [`H:real^3->B`; `es:num->real^3->B`] THEN ASM_REWRITE_TAC[]);;

let P2BK_CHAIN_SUM_BOUND = prove
 (`!d (h:num->real) eps D.
     &0 < eps /\ (!k. d k + h k * inv(&2 * eps) <= d(SUC k)) /\
     (!k. d k <= D) /\ &0 <= d 0
     ==> !n. sum(0..n) h <= &2 * eps * D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. d 0 + sum(0..n) h * inv(&2 * eps) <= d(SUC n)` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
     [ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `SUC n` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `h:num->real`)) (concl th))) THEN
      UNDISCH_TAC `(d:num->real) 0 + sum (0..n) h * inv (&2 * eps) <= d (SUC n)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `sum(0..n) h * inv(&2 * eps) <= D` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < e ==> &0 < &2 * e`] THEN
  REAL_ARITH_TAC);;

let P2BK_SUMMABLE_POS = prove
 (`!(h:num->real) B.
     (!k. &0 <= h k) /\ (!n. sum(0..n) h <= B)
     ==> real_summable (from 0) h /\ (h ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_summable (from 0) (h:num->real)` ASSUME_TAC THENL
   [REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC CONVERGENT_REAL_BOUNDED_MONOTONE THEN CONJ_TAC THENL
     [REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN EXISTS_TAC `abs B` THEN
      X_GEN_TAC `n:num` THEN
      SUBGOAL_THEN `&0 <= sum(0..n) (h:num->real)` MP_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
      DISJ1_TAC THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
      ASM_REWRITE_TAC[REAL_LE_ADDR]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:num->real`; `from 0`] REAL_SUMMABLE_IMP_TOZERO) THEN
  ASM_REWRITE_TAC[IN_FROM; LE_0; ETA_AX]);;

let P2BK_CHAIN_DIST_SUM = prove
 (`!top atlas (g:B->real^3^3) (z:num->B) (h:num->real) eps.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!m n. mfd_joinable (top,atlas) (z m) (z n)) /\
     (!k. mfd_dist (top,atlas) g (z k) (z(SUC k)) <= &2 * h k * inv eps)
     ==> !m d. mfd_dist (top,atlas) g (z m) (z(m + SUC d)) <=
               &2 * inv eps * sum(m..m+d) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; SUM_SING_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `(z:num->B) m`; `(z:num->B)(m + SUC d)`; `(z:num->B)(m + SUC(SUC d))`]
    MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m + SUC d`) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `m + SUC d = SUC(m + d)`] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `m <= SUC(m + d)`] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) ((z:num->B) m) (z(m + SUC d)) <=
               &2 * inv eps * sum(m..m+d) h` THEN
  REWRITE_TAC[ARITH_RULE `m + SUC d = SUC(m + d)`] THEN REAL_ARITH_TAC);;

let P2BK_CHAIN_LIMIT = prove
 (`!top atlas (g:B->real^3^3) (z:num->B) (h:num->real) eps x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < eps /\
     (!m n. mfd_joinable (top,atlas) (z m) (z n)) /\
     (!k. mfd_joinable (top,atlas) x (z k)) /\
     (!k. mfd_dist (top,atlas) g (z k) (z(SUC k)) <= &2 * h k * inv eps) /\
     real_summable (from 0) h
     ==> ?l. ((\k. mfd_dist (top,atlas) g x (z k)) ---> l) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = \k. mfd_dist (top,atlas) (g:B->real^3^3) x ((z:num->B) k)` THEN
  SUBGOAL_THEN `!k. abs(a(k + 1) - a k) <= &2 * inv eps * (h:num->real) k` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "a" THEN REWRITE_TAC[GSYM ADD1] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`; `(z:num->B) k`; `(z:num->B)(SUC k)`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`; `(z:num->B)(SUC k)`; `(z:num->B) k`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `(z:num->B) k`; `(z:num->B)(SUC k)`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `h:num->real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 0) (\k. a(k + 1) - (a:num->real) k)` MP_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\k. &2 * inv eps * (h:num->real) k` THEN
    ASM_SIMP_TAC[REAL_SUMMABLE_LMUL] THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG; SUM_DIFFS_ALT; LE_0] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN EXISTS_TAC `L + (a:num->real) 0` THEN
  UNDISCH_TAC `((\n. (a:num->real)(n + 1) - a 0) ---> L) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n - 1 + 1 = n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "a" THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The chain of necks running into the end.  A neck whose centre has scalar  *)
(* curvature above twice the bound on an inner region H(1 < |w| <= r) has    *)
(* that region on its inner side.  Starting the chain far out, every outer   *)
(* point carries a separating neck, the inner region stays inside all inner  *)
(* sides, and the scales h_k = R(z_k)^(-1/2) are summable (distance gain     *)
(* plus finite diameter).                                                    *)
(* ========================================================================= *)

let P2BK_INNER_REGION_IN = prove
 (`!top atlas (g:B->real^3^3) H eps (x:B) e r.
     p2bk_tube (top,atlas) g H eps /\ p2bk_sepneck (top,atlas) g H eps x e /\ r < &2 /\
     (!w. &1 < norm w /\ norm w <= r
          ==> &2 * mfd_scalar atlas g (H w) < mfd_scalar atlas g x)
     ==> !w. &1 < norm w /\ norm w <= r ==> p2bk_in top H e (H w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_sepneck]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  SUBGOAL_THEN `!w:real^3. &1 < norm w /\ norm w <= r
                           ==> ~((H:real^3->B) w IN IMAGE (e:real^3->B) (rfs_neck_dom eps))`
    (LABEL_TAC "missN") THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `g:B->real^3^3`; `x:B`; `e:real^3->B`; `y:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `rfs_neck_dom`)) (concl th) &&
                       can (find_term ((=) `&3 / &2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 < r` THENL
   [ALL_TAC; X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`;
                 `IMAGE (H:real^3->B) {w:real^3 | &1 < norm w /\ norm w <= r}`]
    P2BK_SIDE_CONNECTED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                            `annulus (&1) (&2):real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `r:real`]
          (CONJUNCT1(CONJUNCT2 CONNECTED_ANNULUS))) THEN
        REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REPEAT STRIP_TAC THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SET_RULE `DISJOINT (s:B->bool) t <=> !q. q IN s ==> ~(q IN t)`;
                  FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((H:real^3->B) w IN IMAGE (e:real^3->B) (rfs_neck_dom eps))` MP_TAC THENL
       [USE_THEN "missN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "inA" o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ri:real` STRIP_ASSUME_TAC o el 5 o CONJUNCTS) THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  USE_THEN "inA" MATCH_MP_TAC THEN
  EXISTS_TAC `(H:real^3->B) (((&1 + min r ri) / &2) % basis 1)` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `((&1 + min r ri) / &2) % basis 1:real^3` THEN REWRITE_TAC[] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC]);;

let P2BK_CHAIN_START = prove
 (`!top atlas (g:B->real^3^3) H eps.
     p2bk_tube (top,atlas) g H eps
     ==> ?x0 e0 r0. &1 < r0 /\ r0 < &2 /\ p2bk_sepneck (top,atlas) g H eps x0 e0 /\
                    (!w. r0 < norm w /\ norm w < &2
                         ==> ?e. p2bk_sepneck (top,atlas) g H eps (H w) e) /\
                    (!w. &1 < norm w /\ norm w <= r0 ==> p2bk_in top H e0 (H w)) /\
                    (!p. p2bk_out top H e0 p
                         ==> ?e'. p2bk_sepneck (top,atlas) g H eps p e')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `r1:real`] P2BK_INNER_R_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `BA:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `rb:real` STRIP_ASSUME_TAC o SPEC `&2 * BA + &1` o
    check (fun th -> is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  ABBREV_TAC `y0:real^3 = ((max rb r1 + &2) / &2) % basis 1` THEN
  SUBGOAL_THEN `rb < norm(y0:real^3) /\ r1 < norm y0 /\ norm y0 < &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `e0:real^3->B` o
    C MATCH_MP (CONJ (ASSUME `r1 < norm(y0:real^3)`) (ASSUME `norm(y0:real^3) < &2`)) o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "p2bk_sepneck" with Failure _ -> false))
          (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`(H:real^3->B) y0`; `e0:real^3->B`; `r1:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w:real^3. &1 < norm w /\ norm w <= r1
                           ==> p2bk_in top H (e0:real^3->B) ((H:real^3->B) w)`
    (LABEL_TAC "A") THENL
   [MATCH_MP_TAC P2BK_INNER_REGION_IN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
                          `(H:real^3->B) y0`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w) <= BA /\
                  &2 * BA + &1 <= mfd_scalar atlas g (H y0)` MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `BA:real`)) (concl th) &&
          not(can (find_term ((=) `rb:real`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `rb:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:B) IN IMAGE (H:real^3->B) (annulus (&1) (&2))` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `H:real^3->B`; `e0:real^3->B`; `p:B`]
      P2BK_OUT_TOPSPACE) THEN
    ASM_SIMP_TAC[IN_DIFF];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `norm(w:real^3) <= r1` THENL
   [SUBGOAL_THEN `p2bk_in top (H:real^3->B) (e0:real^3->B) (p:B)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> concl th = `(H:real^3->B) (w:real^3) = (p:B)`)) THEN
      USE_THEN "A" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `(H:real^3->B) y0`; `e0:real^3->B`; `p:B`]
      P2BK_NOT_IN_AND_OUT) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "p2bk_sepneck" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN MESON_TAC[]]);;

let p2bk_endchain = new_definition
 `p2bk_endchain (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
                (H:real^3->B) (eps:real) (z:num->B) (es:num->real^3->B) (r0:real) <=>
    p2bk_tube (top,atlas) g H eps /\ &1 < r0 /\ r0 < &2 /\
    (!k. z k IN topspace top) /\
    (!k. p2bk_sepneck (top,atlas) g H eps (z k) (es k)) /\
    (!w. r0 < norm w /\ norm w < &2 ==> ?e. p2bk_sepneck (top,atlas) g H eps (H w) e) /\
    (!k w. &1 < norm w /\ norm w <= r0 ==> p2bk_in top H (es k) (H w)) /\
    (!k. p2bk_out top H (es k) (z(SUC k)) /\
         ~(z(SUC k) IN IMAGE (es k) (rfs_neck_dom eps)) /\
         mfd_dist (top,atlas) g (z k) (z(SUC k)) <=
         &2 * inv(sqrt(mfd_scalar atlas g (z k))) * inv eps /\
         mfd_scalar atlas g (z k) <= &2 * mfd_scalar atlas g (z(SUC k)) /\
         mfd_scalar atlas g (z(SUC k)) <= &2 * mfd_scalar atlas g (z k) /\
         (!p. p2bk_in top H (es k) p ==> p2bk_in top H (es(SUC k)) p) /\
         (!p. p2bk_out top H (es(SUC k)) p ==> p2bk_out top H (es k) p)) /\
    real_summable (from 0) (\k. inv(sqrt(mfd_scalar atlas g (z k)))) /\
    ((\k. inv(sqrt(mfd_scalar atlas g (z k)))) ---> &0) sequentially`;;

let P2BK_END_CHAIN = prove
 (`!top atlas (g:B->real^3^3) H eps.
     p2bk_tube (top,atlas) g H eps
     ==> ?z es r0. p2bk_endchain (top,atlas) g H eps z es r0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`] P2BK_CHAIN_START) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:B` (X_CHOOSE_THEN `e0:real^3->B`
    (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x0:B`; `e0:real^3->B`] P2BK_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num->B` (X_CHOOSE_THEN `es:num->real^3->B` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[p2bk_endchain] THEN
  MAP_EVERY EXISTS_TAC [`z:num->B`; `es:num->real^3->B`; `r0:real`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  (* the centres lie in the space *)
  SUBGOAL_THEN `!k. (z:num->B) k IN topspace top` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `(z:num->B) k`; `(es:num->real^3->B) k`]
      P2BK_NECK_CLOSURE_DIST) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[p2bk_sepneck]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the inner region lies in every inner side *)
  SUBGOAL_THEN `!k w. &1 < norm w /\ norm w <= r0
                      ==> p2bk_in top (H:real^3->B) ((es:num->real^3->B) k) (H w)`
    ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`es:num->real^3->B`; `top:B topology`; `H:real^3->B`; `(H:real^3->B) w`]
      P2BK_CHAIN_IN) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the distance from a fixed inner point grows by h_k / (2 eps) per step *)
  ABBREV_TAC `p0:B = (H:real^3->B) (((&1 + r0) / &2) % basis 1)` THEN
  SUBGOAL_THEN `!k. p2bk_in top H ((es:num->real^3->B) k) (p0:B)` ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p0:B) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `H:real^3->B`; `(es:num->real^3->B) 0`; `p0:B`]
      P2BK_IN_TOPSPACE) THEN
    ASM_SIMP_TAC[IN_DIFF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `p0:B`]
    P2BK_CHAIN_GAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\k. mfd_dist (top,atlas) (g:B->real^3^3) p0 ((z:num->B) k)`;
                 `\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))`;
                 `eps:real`; `D:real`] P2BK_CHAIN_SUM_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`p0:B`; `(z:num->B) k`] o
        check (fun th -> can (find_term ((=) `D:real`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`p0:B`; `(z:num->B) 0`] o
        check (fun th -> can (find_term ((=) `D:real`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC P2BK_SUMMABLE_POS THEN EXISTS_TAC `&2 * eps * D` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[p2bk_sepneck; rfs_neck]);;

(* ========================================================================= *)
(* The distance to the end along an end chain, dE x = lim_k d(x, z_k)        *)
(* (p2bk_dend).  It exists, is 1-Lipschitz, tends to 0 along the chain, is   *)
(* at least sqrt(1 - eps) h(x) / eps at the centre of an eps-neck (every     *)
(* curve to z_k leaves the neck), is positive on the whole tube and is       *)
(* bounded below on each inner region.                                       *)
(* ========================================================================= *)

let p2bk_dend = new_definition
 `p2bk_dend (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
            (z:num->B) (x:B) =
    reallim sequentially (\k. mfd_dist (top,atlas) g x (z k))`;;

let P2BK_ENDCHAIN_BASIC = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0.
     p2bk_endchain (top,atlas) g H eps z es r0
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         riemannian_metric atlas g /\ &0 < eps /\ eps <= &1 / &100 /\
         (!k. rfs_neck (top,atlas) g eps (z k) (es k)) /\
         (!k. &0 < mfd_scalar atlas g (z k)) /\
         (!p q. p IN topspace top /\ q IN topspace top ==> mfd_joinable (top,atlas) p q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_endchain; p2bk_tube; p2bk_good_eps] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k. rfs_neck (top,atlas) (g:B->real^3^3) eps ((z:num->B) k) (es k)`
    ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      (try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) = "p2bk_sepneck"
       with Failure _ -> false))) THEN
    SIMP_TAC[p2bk_sepneck];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) &&
      (try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) = "rfs_neck"
       with Failure _ -> false))) THEN
    SIMP_TAC[rfs_neck];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:B`; `q:B`] o
      check (fun th -> can (find_term ((=) `D:real`)) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

let P2BK_DEND_TENDSTO = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ x IN topspace top
     ==> ((\k. mfd_dist (top,atlas) g x (z k)) ---> p2bk_dend (top,atlas) g z x)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `z:num->B`; `\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))`;
                 `eps:real`; `x:B`] P2BK_CHAIN_LIMIT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN REWRITE_TAC[p2bk_dend; reallim] THEN
  CONV_TAC SELECT_CONV THEN EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[]);;

let P2BK_DEND_LIPSCHITZ = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top
     ==> abs(p2bk_dend (top,atlas) g z p - p2bk_dend (top,atlas) g z q) <=
         mfd_dist (top,atlas) g p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `p:B`]
    P2BK_DEND_TENDSTO) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_TENDSTO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`;
    `\k. abs(mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B) k) -
             mfd_dist (top,atlas) g q (z k))`] REALLIM_UBOUND) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`sequentially:num net`;
                   `\k. mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B) k)`;
                   `\k. mfd_dist (top,atlas) (g:B->real^3^3) q ((z:num->B) k)`;
                   `p2bk_dend (top,atlas) (g:B->real^3^3) z p`;
                   `p2bk_dend (top,atlas) (g:B->real^3^3) z q`] REALLIM_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ABS) THEN REWRITE_TAC[];
    EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `q:B`; `(z:num->B) k`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `q:B`; `p:B`; `(z:num->B) k`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `q:B`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let P2BK_DEND_TAIL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 e.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ &0 < e
     ==> ?K. !k. K <= k ==> p2bk_dend (top,atlas) g z (z k) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  UNDISCH_TAC `real_summable (from 0)
                 (\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k))))` THEN
  REWRITE_TAC[REAL_SUMMABLE_CAUCHY; FROM_0; INTER_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `e * eps / &4`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e / &2` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`;
    `\m. mfd_dist (top,atlas) (g:B->real^3^3) ((z:num->B) k) (z m)`] REALLIM_UBOUND) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BK_DEND_TENDSTO THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `SUC k` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `z:num->B`; `\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))`;
                 `eps:real`] P2BK_CHAIN_DIST_SUM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `m - SUC k`]) THEN
  SUBGOAL_THEN `k + SUC(m - SUC k) = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `k + (m - SUC k)`] o
    check (fun th -> can (find_term ((=) `N:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S = sum(k..k + (m - SUC k))
                    (\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k))))` THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * inv eps * S` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e / &2 = &2 * inv eps * (e * eps / &4)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_FIELD
      `~(eps = &0) ==> e / &2 = &2 * inv eps * (e * eps / &4)`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]);;

let P2BK_DEND_SMALL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 s.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ &0 < s
     ==> ?x. x IN topspace top /\ p2bk_dend (top,atlas) g z x < s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `s:real`]
    P2BK_DEND_TAIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
  EXISTS_TAC `(z:num->B) K` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[p2bk_endchain]; FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* The chain leaves every neck: R(z_k) tends to infinity. *)

let P2BK_EVENTUALLY_OUTSIDE_NECK = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e (z:num->B).
     p2bk_good_eps (UNIV:B->bool) eps /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\
     ((\k. inv(sqrt(mfd_scalar atlas g (z k)))) ---> &0) sequentially
     ==> ?K. !k. K <= k ==> ~(z k IN IMAGE e (rfs_neck_dom eps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps (x:B) e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  UNDISCH_TAC `((\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))) ---> &0)
               sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2 * mfd_scalar atlas (g:B->real^3^3) x))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                `g:B->real^3^3`; `x:B`; `e:real^3->B`; `y:real^3`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `rfs_neck_dom`)) (concl th) &&
                     can (find_term ((=) `&3 / &2`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(sqrt(&2 * mfd_scalar atlas (g:B->real^3^3) x)) <=
                inv(sqrt(mfd_scalar atlas g ((e:real^3->B) y)))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `abs(inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))) <
               inv(sqrt(&2 * mfd_scalar atlas g x))` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* From a point on the inner side of all necks after k0, the distance to   *)
(* z_k grows, and dE gains h_k0 / (2 eps) over d(p, z_k0).                *)

let P2BK_DEND_GAIN_FROM = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p k0.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\
     (!k. k0 <= k ==> p2bk_in top H (es k) p)
     ==> mfd_dist (top,atlas) g p (z k0) +
         inv(sqrt(mfd_scalar atlas g (z k0))) * inv(&2 * eps)
         <= p2bk_dend (top,atlas) g z p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  SUBGOAL_THEN
   `!k. k0 <= k
        ==> mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B) k) +
            inv(sqrt(mfd_scalar atlas g (z k))) * inv(&2 * eps)
            <= mfd_dist (top,atlas) g p (z(SUC k))`
    (LABEL_TAC "gain") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_CHAIN_GAIN1 THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `es:num->real^3->B`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. SUC k0 <= n
        ==> mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B)(SUC k0)) <=
            mfd_dist (top,atlas) g p (z n)`
    (LABEL_TAC "mono") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[ARITH_RULE `~(SUC k0 <= 0)`];
      DISCH_TAC THEN ASM_CASES_TAC `SUC k0 <= n` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B) n)` THEN
        CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "gain" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a + c <= b ==> a <= b`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_INV_EQ; SQRT_POS_LE; REAL_LT_IMP_LE];
          REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `n = k0:num` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B)(SUC k0))` THEN CONJ_TAC THENL
   [USE_THEN "gain" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`;
    `\k. mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B) k)`] REALLIM_LBOUND) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BK_DEND_TENDSTO THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `SUC k0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* At the centre of an eps-neck, dE is at least the exit length. *)

let P2BK_DEND_NECK_LOWER = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x e.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ rfs_neck (top,atlas) g eps x e
     ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) * inv eps <=
         p2bk_dend (top,atlas) g z x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`] P2BK_NECK_CLOSURE_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `z:num->B`]
    P2BK_EVENTUALLY_OUTSIDE_NECK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:num` (LABEL_TAC "out")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o
    check (fun th -> concl th = `rfs_neck (top,atlas) (g:B->real^3^3) eps (x:B) e`)) THEN
  UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`;
    `\k. mfd_dist (top,atlas) (g:B->real^3^3) x ((z:num->B) k)`] REALLIM_LBOUND) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BK_DEND_TENDSTO THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `K:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((z:num->B) k IN IMAGE (e:real^3->B) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [USE_THEN "out" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC APX_DIST_GE_CURVES THEN CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `u0:real^3`; `gamma:real->B`;
                 `&0`; `&1`] APX_NECK_EXIT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_ABS_0; REAL_SUB_RZERO]);;

(* dE is positive on the tube. *)

let P2BK_DEND_POS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ x IN topspace top
     ==> &0 < p2bk_dend (top,atlas) g z x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  SUBGOAL_THEN `(x:B) IN IMAGE (H:real^3->B) (annulus (&1) (&2))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `norm(w:real^3) <= r0` THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `x:B`; `0`] P2BK_DEND_GAIN_FROM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> concl th = `(H:real^3->B) (w:real^3) = (x:B)`)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r0:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "p2bk_in" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> a + b <= c ==> &0 < c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `r0:real`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "p2bk_sepneck" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `e:real^3->B`) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps (x:B) e` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (x:B) e` THEN
    SIMP_TAC[p2bk_sepneck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps (x:B) e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `e:real^3->B`] P2BK_DEND_NECK_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= c ==> &0 < c`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]]);;

(* dE is bounded below on each inner region H(1 < |w| <= r), r < 2. *)

let P2BK_DEND_INNER_REGION = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 r.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ r < &2
     ==> ?c. &0 < c /\
             !w. &1 < norm w /\ norm w <= r ==> c <= p2bk_dend (top,atlas) g z (H w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `r:real`] P2BK_INNER_R_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `BA:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k0. &2 * BA < mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `((\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))) ---> &0)
                 sequentially` THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2 * BA))`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_TAC THEN EXISTS_TAC `N:num` THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv(sqrt(&2 * BA)) <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) N)))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `abs(inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) N)))) <
                   inv(sqrt(&2 * BA))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. &1 < norm w /\ norm w <= r
                    ==> p2bk_in top (H:real^3->B) ((es:num->real^3->B) k0) (H w)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_INNER_REGION_IN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
                          `(z:num->B) k0`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w) <= BA` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&2 * BA < mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k0)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!d w. &1 < norm w /\ norm w <= r
                      ==> p2bk_in top (H:real^3->B) ((es:num->real^3->B) (k0 + d)) (H w)`
    ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[ADD_CLAUSES];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 5 o CONJUNCTS o SPEC `k0 + d:num` o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `rfs_neck_dom`)) (concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "p2bk_out" with Failure _ -> false))
              (concl th))) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k0))) * inv(&2 * eps)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(H:real^3->B) w IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2bk_tube] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p2bk_tube"
                       with Failure _ -> false)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `(H:real^3->B) w`; `k0:num`] P2BK_DEND_GAIN_FROM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k - k0:num`; `w:real^3`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `k0:num`)) (concl th))) THEN
    SUBGOAL_THEN `k0 + (k - k0) = k:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a + b <= c ==> b <= c`) THEN
  MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Crossing a neck sphere costs at most its diameter, so for an inner point  *)
(* p of a separating neck at y, d(p,y) + dE(y) <= dE(p) + 10 h(y).  The      *)
(* level-set lemma (LS): two neck centres y, y' satisfy d(y,y') <= |dE(y) -  *)
(* dE(y')| + 10 (h(y) + h(y')), and centres at nearly the same level have    *)
(* comparable scalar curvature.                                              *)
(* ========================================================================= *)

let P2BK_SPHERE_DIAM = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e c.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100 /\
     c IN IMAGE e (sphere(vec 0,&1))
     ==> mfd_joinable (top,atlas) x c /\ mfd_joinable (top,atlas) c x /\
         mfd_dist (top,atlas) g x c <= &5 * inv(sqrt(mfd_scalar atlas g x)) /\
         mfd_dist (top,atlas) g c x <= &5 * inv(sqrt(mfd_scalar atlas g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(c:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u0:real^3) IN rfs_neck_dom eps /\ (u1:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `u0:real^3`; `u1:real^3`]
    APX_NECK_DIST_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * sqrt(&2) * pi <= &5` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * &1415 / &1000 * &315 / &100` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [SIMP_TAC[SQRT_POS_LE; REAL_POS];
        MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        REWRITE_TAC[PI_POS_LE];
        MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) x c <= &5 * inv(sqrt(mfd_scalar atlas g x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x)) * sqrt(&2) * pi` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `a * h * b * c = (a * b * c) * h:real`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM]);;

(* Crossing the central sphere: d(p,x) + d(x,q) <= d(p,q) + 10 h(x). *)

let P2BK_CROSS_UPPER = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e p q.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100 /\
     p IN topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
     ~(connected_component_of
         (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p q) /\
     mfd_joinable (top,atlas) p q
     ==> mfd_dist (top,atlas) g p x + mfd_dist (top,atlas) g x q <=
         mfd_dist (top,atlas) g p q + &10 * inv(sqrt(mfd_scalar atlas g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b <= c + d <=> a + b - d <= c:real`] THEN
  MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `gamma:real->B`; `&0`; `&1`; `IMAGE (e:real^3->B) (sphere(vec 0,&1))`]
    P2BK_CURVE_MEETS_SEP) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `(gamma:real->B) t1`] P2BK_SPHERE_DIAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `&0`; `t1:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `&0`; `t1:real`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `t1:real`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (p:B) ((gamma:real->B) t1) /\
                mfd_joinable (top,atlas) ((gamma:real->B) t1) (q:B)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->B)(&0) = p`));
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->B)(&1) = q`))] THEN
    MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `(gamma:real->B) t1`; `x:B`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `(gamma:real->B) t1`; `q:B`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The exit length from the centre of a neck. *)

let P2BK_NECK_EXIT_DIST = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e q.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100 /\
     ~(q IN IMAGE e (rfs_neck_dom eps)) /\ mfd_joinable (top,atlas) x q
     ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) * inv eps <=
         mfd_dist (top,atlas) g x q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `u0:real^3`; `gamma:real->B`;
                 `&0`; `&1`] APX_NECK_EXIT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_ABS_0; REAL_SUB_RZERO]);;

(* The chain eventually lies on the outer side of every separating neck. *)

let P2BK_ENDCHAIN_EVENTUALLY_OUT = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 (y:B) e.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p2bk_sepneck (top,atlas) g H eps y e
     ==> ?K. !k. K <= k ==> p2bk_out top H e (z k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `y:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ro:real` STRIP_ASSUME_TAC o el 4 o CONJUNCTS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `ro:real`] P2BK_INNER_R_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `BA:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `((\k. inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))) ---> &0)
               sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(sqrt(BA))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:num->B) k IN IMAGE (H:real^3->B) (annulus (&1) (&2))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `ro < norm(w:real^3)` THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `(H:real^3->B) (w:real^3) = (z:num->B) k`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ro:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "p2bk_out" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k) <= BA` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `(H:real^3->B) (w:real^3) = (z:num->B) k`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt BA) <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* For an inner point p of a separating neck at y. *)

let P2BK_DEND_CROSS_UPPER = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 (y:B) e p.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p2bk_sepneck (top,atlas) g H eps y e /\
     p2bk_in top H e p
     ==> mfd_dist (top,atlas) g p y + p2bk_dend (top,atlas) g z y <=
         p2bk_dend (top,atlas) g z p + &10 * inv(sqrt(mfd_scalar atlas g y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps (y:B) e` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (y:B) e` THEN
    SIMP_TAC[p2bk_sepneck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:B) IN topspace top /\ ~((p:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `H:real^3->B`; `e:real^3->B`; `p:B`]
      P2BK_IN_TOPSPACE) THEN ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `y:B`; `e:real^3->B`] P2BK_NECK_CLOSURE_DIST) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `e:real^3->B`] P2BK_ENDCHAIN_EVENTUALLY_OUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:num` (LABEL_TAC "out")) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `y:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sep" o el 1 o CONJUNCTS) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b <= c + d <=> a + b - d <= c:real`] THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`;
    `\k. mfd_dist (top,atlas) (g:B->real^3^3) p y + mfd_dist (top,atlas) g y ((z:num->B) k) -
         &10 * inv(sqrt(mfd_scalar atlas g y))`;
    `\k. mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B) k)`] REALLIM_LE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC P2BK_DEND_TENDSTO THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BK_DEND_TENDSTO THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `K:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `y:B`; `e:real^3->B`; `p:B`; `(z:num->B) k`] P2BK_CROSS_UPPER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[IN_DIFF] THEN USE_THEN "sep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "out" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]);;

let P2BK_EXIT_FACTOR = prove
 (`!eps h. &0 < eps /\ eps <= &1 / &100 /\ &0 <= h
           ==> &99 * h <= sqrt(&1 - eps) * h * inv eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&99 / &100 <= sqrt(&1 - eps) /\ &100 <= inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `inv(&1 / &100) <= inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&99 / &100 * h * &100` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* The level-set lemma. *)

let P2BK_LEVEL_DIST = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 (y:B) e y' e'.
     p2bk_endchain (top,atlas) g H eps z es r0 /\
     p2bk_sepneck (top,atlas) g H eps y e /\ p2bk_sepneck (top,atlas) g H eps y' e'
     ==> mfd_dist (top,atlas) g y y' <=
         abs(p2bk_dend (top,atlas) g z y - p2bk_dend (top,atlas) g z y') +
         &10 * (inv(sqrt(mfd_scalar atlas g y)) + inv(sqrt(mfd_scalar atlas g y')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps (y:B) e /\
                rfs_neck (top,atlas) g eps (y':B) e'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (y:B) e`;
      UNDISCH_TAC `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (y':B) e'`] THEN
    SIMP_TAC[p2bk_sepneck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top /\ (y':B) IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `eps:real`; `y:B`; `e:real^3->B`] P2BK_NECK_CLOSURE_DIST);
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `eps:real`; `y':B`; `e':real^3->B`] P2BK_NECK_CLOSURE_DIST)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1)) /\
                (y':B) IN IMAGE (e':real^3->B) (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps (y:B) e`;
      UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps (y':B) e'`] THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y)) /\
                &0 <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y'))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `y':B`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `DISJOINT (IMAGE (e':real^3->B) (sphere(vec 0,&1)))
                          (IMAGE (e:real^3->B) (sphere(vec 0,&1)))` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `y:B`; `e:real^3->B`; `c:B`] P2BK_SPHERE_DIAM) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `y':B`; `e':real^3->B`; `c:B`] P2BK_SPHERE_DIAM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `c:B`; `y':B`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `~((y':B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))) /\
                ~((y:B) IN IMAGE (e':real^3->B) (sphere(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (IMAGE (e':real^3->B) (sphere(vec 0,&1)))
                          (IMAGE (e:real^3->B) (sphere(vec 0,&1)))` THEN
    UNDISCH_TAC `(y:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `(y':B) IN IMAGE (e':real^3->B) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `y:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y':B` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `y:B`; `e:real^3->B`; `y':B`] P2BK_DEND_CROSS_UPPER) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `y':B`; `e':real^3->B`] P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `y':B`; `e':real^3->B`; `y:B`] P2BK_DEND_CROSS_UPPER) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `y:B`; `e:real^3->B`; `y':B`; `e':real^3->B`]
    P2BK_NEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `y':B`; `e':real^3->B`; `y:B`]
    P2BK_NOT_IN_AND_OUT) THEN
  ASM_REWRITE_TAC[]);;

(* Neck centres at nearly the same level have comparable curvature. *)

let P2BK_LEVEL_SCALE = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 (y:B) e y' e'.
     p2bk_endchain (top,atlas) g H eps z es r0 /\
     p2bk_sepneck (top,atlas) g H eps y e /\ p2bk_sepneck (top,atlas) g H eps y' e' /\
     abs(p2bk_dend (top,atlas) g z y - p2bk_dend (top,atlas) g z y') <=
     inv(sqrt(mfd_scalar atlas g y)) + inv(sqrt(mfd_scalar atlas g y'))
     ==> mfd_scalar atlas g y <= &2 * mfd_scalar atlas g y' /\
         mfd_scalar atlas g y' <= &2 * mfd_scalar atlas g y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps (y:B) e /\
                rfs_neck (top,atlas) g eps (y':B) e'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (y:B) e`;
      UNDISCH_TAC `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (y':B) e'`] THEN
    SIMP_TAC[p2bk_sepneck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top /\ (y':B) IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `eps:real`; `y:B`; `e:real^3->B`] P2BK_NECK_CLOSURE_DIST);
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `eps:real`; `y':B`; `e':real^3->B`] P2BK_NECK_CLOSURE_DIST)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN IMAGE (e:real^3->B) (rfs_neck_dom eps) /\
                (y':B) IN IMAGE (e':real^3->B) (rfs_neck_dom eps)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps (y:B) e` THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps (y':B) e'` THEN
    REWRITE_TAC[rfs_neck] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) y /\ &0 < mfd_scalar atlas g y'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `(y':B) IN IMAGE (e:real^3->B) (rfs_neck_dom eps) \/
                (y:B) IN IMAGE (e':real^3->B) (rfs_neck_dom eps)` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `y:B`; `e:real^3->B`; `y':B`; `e':real^3->B`] P2BK_LEVEL_DIST) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `y:B`; `e:real^3->B`; `y':B`] P2BK_NECK_EXIT_DIST) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `y':B`; `e':real^3->B`; `y:B`] P2BK_NECK_EXIT_DIST) THEN
    MP_TAC(ISPECL [`eps:real`; `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y))`]
      P2BK_EXIT_FACTOR) THEN
    MP_TAC(ISPECL [`eps:real`; `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y'))`]
      P2BK_EXIT_FACTOR) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `y':B`] MFD_DIST_SYM) THEN
    SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y)) /\
                  &0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y'))` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`top:B topology`; `e':real^3->B`; `e:real^3->B`; `y':B`];
    MAP_EVERY EXISTS_TAC [`top:B topology`; `e:real^3->B`; `e':real^3->B`; `y':B`];
    MAP_EVERY EXISTS_TAC [`top:B topology`; `e':real^3->B`; `e:real^3->B`; `y:B`];
    MAP_EVERY EXISTS_TAC [`top:B topology`; `e:real^3->B`; `e':real^3->B`; `y:B`]] THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* ========================================================================= *)
(* Continuity of dE, dE -> 0 at the end uniformly, and ray points: for 0 < t *)
(* < dE(x) there is y with d(x,y) = t and dE(y) = dE(x) - t (near-minimizing *)
(* curves to z_k, the intermediate value theorem and compactness of H(r <=   *)
(* |w| <= rho)).  No geodesics are needed.                                   *)
(* ========================================================================= *)

let P2BK_DIST_APPROX = prove
 (`!top atlas (g:B->real^3^3) x y h.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable (top,atlas) x y /\ &0 < h
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = x /\ gamma(&1) = y /\
                 mfd_length atlas g gamma (&0) (&1) < mfd_dist (top,atlas) g x y + h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `y:B`; `mfd_dist (top,atlas) (g:B->real^3^3) x y + h`]
    APX_DIST_GE_CURVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
    EXISTS_TAC `gamma:real->B` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let P2BK_LIPSCHITZ_CONTINUOUS = prove
 (`!top atlas (g:B->real^3^3) f.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x y. x IN topspace top /\ y IN topspace top
            ==> abs(f x - f y) <= mfd_dist (top,atlas) g x y)
     ==> continuous_map (top,euclideanreal) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; CONTINUOUS_MAP_TO_METRIC] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  EXISTS_TAC `{y:B | y IN topspace top /\
                     (\p. mfd_dist (top,atlas) (g:B->real^3^3) x p) y IN {t:real | t < r}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
    ASM_SIMP_TAC[P2BK_DIST_SECTION_CONTINUOUS; GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT];
    ASM_SIMP_TAC[IN_ELIM_THM; MFD_DIST_REFL];
    REWRITE_TAC[IN_ELIM_THM; IN_MBALL; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:B`; `y:B`]) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BK_DEND_CONTINUOUS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0.
     p2bk_endchain (top,atlas) g H eps z es r0
     ==> continuous_map (top,euclideanreal) (p2bk_dend (top,atlas) g z)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  MATCH_MP_TAC P2BK_LIPSCHITZ_CONTINUOUS THEN
  MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_DEND_LIPSCHITZ THEN
  MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2BK_DEND_UNIFORM = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 y k.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ y IN topspace top
     ==> abs(p2bk_dend (top,atlas) g z y - mfd_dist (top,atlas) g y (z k)) <=
         p2bk_dend (top,atlas) g z (z k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`;
    `\m. abs(mfd_dist (top,atlas) (g:B->real^3^3) y ((z:num->B) m) -
             mfd_dist (top,atlas) g y (z k))`;
    `\m. mfd_dist (top,atlas) (g:B->real^3^3) ((z:num->B) k) (z m)`] REALLIM_LE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `y:B`]
      P2BK_DEND_TENDSTO) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o C CONJ (ISPECL [`sequentially:num net`;
      `mfd_dist (top,atlas) (g:B->real^3^3) y ((z:num->B) k)`] REALLIM_CONST)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REALLIM_SUB) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ABS) THEN REWRITE_TAC[];
    MATCH_MP_TAC P2BK_DEND_TENDSTO THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `0` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `(z:num->B) k`; `(z:num->B) m`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `(z:num->B) m`; `(z:num->B) k`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `(z:num->B) k`; `(z:num->B) m`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* dE tends to 0 uniformly at the end. *)

let P2BK_DEND_NEAR_END = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 s.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ &0 < s
     ==> ?rho. rho < &2 /\
               !w. rho < norm w /\ norm w < &2 ==> p2bk_dend (top,atlas) g z (H w) < s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_good_eps]) THEN
  ABBREV_TAC `p0:B = (H:real^3->B) (((&1 + r0) / &2) % basis 1)` THEN
  SUBGOAL_THEN `&1 < norm(((&1 + r0) / &2) % basis 1:real^3) /\
                norm(((&1 + r0) / &2) % basis 1:real^3) <= r0` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. p2bk_in top H ((es:num->real^3->B) k) (p0:B)` ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p0:B) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `H:real^3->B`; `(es:num->real^3->B) 0`; `p0:B`]
      P2BK_IN_TOPSPACE) THEN ASM_SIMP_TAC[IN_DIFF];
    ALL_TAC] THEN
  (* a chain index N with dE(p0) - d(p0,z N) < s / 2 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `p0:B`]
    P2BK_DEND_TENDSTO) THEN
  ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `s / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(LABEL_TAC "conv") THEN
  (* the radii *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `r0:real`] P2BK_INNER_R_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `(z:num->B) N`; `(es:num->real^3->B) N`]
    P2BK_SEPNECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sides") THEN
  USE_THEN "sides" (X_CHOOSE_THEN `ro:real` STRIP_ASSUME_TAC o el 4 o CONJUNCTS) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `rb:real` STRIP_ASSUME_TAC o
    SPEC `max (&2 * B1 + &1) (max (&2 * mfd_scalar atlas (g:B->real^3^3) ((z:num->B) N))
                                  ((&20 / s) pow 2))` o
    check (fun th -> is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  EXISTS_TAC `max (max ro rb) r0` THEN CONJ_TAC THENL
   [UNDISCH_TAC `(ro:real) < &2` THEN UNDISCH_TAC `(rb:real) < &2` THEN
    UNDISCH_TAC `(r0:real) < &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * B1 + &1 <= mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w) /\
                &2 * mfd_scalar atlas g ((z:num->B) N) <= mfd_scalar atlas g (H w) /\
                (&20 / s) pow 2 <= mfd_scalar atlas g (H w)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rb:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `max (max ro rb) r0 < norm(w:real^3)` THEN
      UNDISCH_TAC `norm(w:real^3) < &2` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H:real^3->B) w IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (H:real^3->B) (annulus (&1) (&2)) = topspace top` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN UNDISCH_TAC `&1 < r0` THEN
    UNDISCH_TAC `max (max ro rb) r0 < norm(w:real^3)` THEN
    UNDISCH_TAC `norm(w:real^3) < &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* H w lies beyond the neck N *)
  SUBGOAL_THEN `~((H:real^3->B) w IN IMAGE ((es:num->real^3->B) N) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `g:B->real^3^3`; `(z:num->B) N`; `(es:num->real^3->B) N`;
                                  `v:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `rfs_neck_dom`)) (concl th) &&
                       can (find_term ((=) `&3 / &2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&2 * mfd_scalar atlas (g:B->real^3^3) ((z:num->B) N) <=
                 mfd_scalar atlas g ((H:real^3->B) w)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!k. &0 < mfd_scalar atlas (g:B->real^3^3) ((z:num->B) k)` THEN
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* distance gain across the neck N *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `(z:num->B) N`; `(es:num->real^3->B) N`; `p0:B`;
                 `(H:real^3->B) w`] P2BK_CROSS_GAIN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `H:real^3->B`; `(es:num->real^3->B) N`; `p0:B`]
      P2BK_IN_TOPSPACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sides" (MATCH_MP_TAC o el 1 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ro:real`)) (concl th))) THEN
    UNDISCH_TAC `max (max ro rb) r0 < norm(w:real^3)` THEN
    UNDISCH_TAC `norm(w:real^3) < &2` THEN REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "gainN")] THEN
  (* a separating neck at H w, with p0 on its inner side *)
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `r0:real`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "p2bk_sepneck" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `max (max ro rb) r0` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `eq:real^3->B`)] THEN
  SUBGOAL_THEN `p2bk_in top (H:real^3->B) (eq:real^3->B) (p0:B)` ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `(H:real^3->B) w`; `eq:real^3->B`; `r0:real`]
      P2BK_INNER_REGION_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w':real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w') <= B1` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&2 * B1 + &1 <= mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w)` THEN
      REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `(H:real^3->B) w`; `eq:real^3->B`; `p0:B`] P2BK_DEND_CROSS_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "upper") THEN
  SUBGOAL_THEN `&10 * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w))) <= s / &2`
  (LABEL_TAC "hw") THENL
   [SUBGOAL_THEN `&20 / s <= sqrt(mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w))`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((H:real^3->B) w))) <= inv(&20 / s)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_DIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) ((z:num->B) N))) * inv(&2 * eps)`
  (LABEL_TAC "hN") THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "conv" MP_TAC THEN REMOVE_THEN "gainN" MP_TAC THEN
  REMOVE_THEN "upper" MP_TAC THEN REMOVE_THEN "hw" MP_TAC THEN REMOVE_THEN "hN" MP_TAC THEN
  REAL_ARITH_TAC);;

(* Approximate ray points, from a near-minimizing curve to z_k. *)

let P2BK_RAY_ARITH = prove
 (`!dxy t L L1 L2 dxz dyz dEy dEx dEz delta.
     dxy = t /\ L = L1 + L2 /\ dxy <= L1 /\ dyz <= L2 /\ L < dxz + delta / &3 /\
     dxz <= dxy + dyz /\ abs(dEy - dyz) <= dEz /\ dEz < delta / &3 /\
     abs(dxz - dEx) < min (delta / &3) (dEx - t)
     ==> abs(dEy - (dEx - t)) <= delta`,
  REAL_ARITH_TAC);;

let P2BK_RAY_APPROX = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x t delta.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ x IN topspace top /\
     &0 < t /\ t < p2bk_dend (top,atlas) g z x /\ &0 < delta
     ==> ?y. y IN topspace top /\ mfd_dist (top,atlas) g x y = t /\
             abs(p2bk_dend (top,atlas) g z y - (p2bk_dend (top,atlas) g z x - t)) <= delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `x:B`]
    P2BK_DEND_TENDSTO) THEN
  ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `min (delta / &3) (p2bk_dend (top,atlas) (g:B->real^3^3) z x - t)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN
    UNDISCH_TAC `t < p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
    UNDISCH_TAC `&0 < delta` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `K1:num`)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `delta / &3`] P2BK_DEND_TAIL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < delta` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `K2:num`)] THEN
  SUBGOAL_THEN
   `abs(mfd_dist (top,atlas) (g:B->real^3^3) x ((z:num->B)(K1 + K2)) -
        p2bk_dend (top,atlas) g z x) <
    min (delta / &3) (p2bk_dend (top,atlas) g z x - t) /\
    p2bk_dend (top,atlas) g z (z(K1 + K2)) < delta / &3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `(z:num->B)(K1 + K2)`; `delta / &3`] P2BK_DIST_APPROX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN UNDISCH_TAC `&0 < delta` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->B` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `?tau. tau IN real_interval[&0,&1] /\
          mfd_dist (top,atlas) (g:B->real^3^3) x ((gamma:real->B) tau) = t`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `is_realinterval (IMAGE (\tau. mfd_dist (top,atlas) (g:B->real^3^3) x ((gamma:real->B) tau))
                             (real_interval[&0,&1]))`
    MP_TAC THENL
     [REWRITE_TAC[GSYM CONNECTED_IN_EUCLIDEANREAL] THEN
      MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
      SUBGOAL_THEN `(\tau. mfd_dist (top,atlas) (g:B->real^3^3) x ((gamma:real->B) tau)) =
                    (\p. mfd_dist (top,atlas) g x p) o gamma` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:B topology` THEN
      ASM_SIMP_TAC[P2BK_DIST_SECTION_CONTINUOUS] THEN
      UNDISCH_TAC `mfd_c1_curve (top,atlas:((B->bool)#(B->real^3))->bool) gamma (&0) (&1)` THEN
      SIMP_TAC[mfd_c1_curve];
      ALL_TAC] THEN
    REWRITE_TAC[is_realinterval; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`mfd_dist (top,atlas) (g:B->real^3^3) x ((gamma:real->B)(&0))`;
       `mfd_dist (top,atlas) (g:B->real^3^3) x ((gamma:real->B)(&1))`; `t:real`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
        EXISTS_TAC `&1` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[MFD_DIST_REFL] THEN UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `abs(mfd_dist (top,atlas) (g:B->real^3^3) x ((z:num->B)(K1 + K2)) -
                         p2bk_dend (top,atlas) g z x) <
                     min (delta / &3) (p2bk_dend (top,atlas) g z x - t)` THEN
        REAL_ARITH_TAC];
      MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `(gamma:real->B) tau` THEN
  SUBGOAL_THEN `(gamma:real->B) tau IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                         `gamma:real->B`; `&0`; `&1`; `tau:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `tau IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `&0`; `tau:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `&0`; `tau:real`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `tau:real`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `(gamma:real->B) tau`; `(z:num->B)(K1 + K2)`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `(gamma:real->B) tau`; `K1 + K2:num`] P2BK_DEND_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BK_RAY_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`mfd_dist (top,atlas) (g:B->real^3^3) x ((gamma:real->B) tau)`;
    `mfd_length atlas (g:B->real^3^3) (gamma:real->B) (&0) (&1)`;
    `mfd_length atlas (g:B->real^3^3) (gamma:real->B) (&0) tau`;
    `mfd_length atlas (g:B->real^3^3) (gamma:real->B) tau (&1)`;
    `mfd_dist (top,atlas) (g:B->real^3^3) x ((z:num->B)(K1 + K2))`;
    `mfd_dist (top,atlas) (g:B->real^3^3) ((gamma:real->B) tau) ((z:num->B)(K1 + K2))`;
    `p2bk_dend (top,atlas) (g:B->real^3^3) z ((z:num->B)(K1 + K2))`] THEN
  ASM_REWRITE_TAC[]);;

(* Exact ray points by compactness of H(r <= |w| <= rho). *)

let P2BK_DEND_RAY_POINT = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x t r.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ x IN topspace top /\
     &0 < t /\ t < p2bk_dend (top,atlas) g z x /\ &1 < r /\ r < &2 /\
     (!w. &1 < norm w /\ norm w <= r
          ==> p2bk_dend (top,atlas) g z x <= p2bk_dend (top,atlas) g z (H w))
     ==> ?y. y IN topspace top /\ mfd_dist (top,atlas) g x y = t /\
             p2bk_dend (top,atlas) g z y = p2bk_dend (top,atlas) g z x - t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  ABBREV_TAC `dx = p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `(dx - t) / &2`] P2BK_DEND_NEAR_END) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t < dx` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")))] THEN
  ABBREV_TAC `K = {w:real^3 | r <= norm w /\ norm w <= max rho r}` THEN
  SUBGOAL_THEN `compact (K:real^3->bool) /\ K SUBSET annulus (&1) (&2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{w:real^3 | r <= norm w /\ norm w <= max rho r} =
                    cball(vec 0,max rho r) DIFF ball(vec 0,r)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `annulus (&1) (&2):real^3->bool`; `H:real^3->B`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Hi:B->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `C = IMAGE (H:real^3->B) K INTER
                  {y:B | y IN topspace top /\
                         (\p. mfd_dist (top,atlas) (g:B->real^3^3) x p) y IN {t}}` THEN
  SUBGOAL_THEN `compact_in top (C:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (annulus (&1) (&2):real^3->bool)` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
      ASM_SIMP_TAC[P2BK_DIST_SECTION_CONTINUOUS; GSYM REAL_CLOSED_IN; REAL_CLOSED_SING]];
    ALL_TAC] THEN
  (* approximate ray points lie in C *)
  SUBGOAL_THEN
   `!delta. &0 < delta /\ delta < min ((dx - t) / &2) t
            ==> ?y. y IN C /\ abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t)) <= delta`
    (LABEL_TAC "approx") THENL
   [X_GEN_TAC `delta:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `x:B`; `t:real`; `delta:real`] P2BK_RAY_APPROX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_SING] THEN
    SUBGOAL_THEN `(y:B) IN IMAGE (H:real^3->B) (annulus (&1) (&2))` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r:real`)) (concl th) &&
        can (find_term ((=) `dx:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; UNDISCH_TAC `norm(w:real^3) < r` THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t)) <= delta` THEN
      UNDISCH_TAC `delta < min ((dx - t) / &2) t` THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "far" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `max rho r < norm(w:real^3)` THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t)) <= delta` THEN
      UNDISCH_TAC `delta < min ((dx - t) / &2) t` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the minimum of |dE y - (dx - t)| on C *)
  MP_TAC(ISPEC `IMAGE (\y. abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t))) C`
    REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; ETA_AX] THEN
      MATCH_MP_TAC P2BK_DEND_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      USE_THEN "approx" (MP_TAC o SPEC `min ((dx - t) / &2) t / &2`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `t < dx` THEN UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `y0:B` STRIP_ASSUME_TAC) THEN EXISTS_TAC `y0:B` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t)) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(&0 < a) ==> a = &0`) THEN
    REWRITE_TAC[REAL_ABS_POS] THEN DISCH_TAC THEN
    USE_THEN "approx" (MP_TAC o SPEC
      `min (abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t)) / &2)
           (min ((dx - t) / &2) t / &2)`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `&0 < abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t))` THEN
      UNDISCH_TAC `t < dx` THEN UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y':B`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y' - (dx - t)) <=
                 min (abs(p2bk_dend (top,atlas) g z y - (dx - t)) / &2)
                     (min ((dx - t) / &2) t / &2)` THEN
    UNDISCH_TAC `&0 < abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `y:B` THEN
  UNDISCH_TAC `(y:B) IN C` THEN EXPAND_TAC "C" THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_SING] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs(p2bk_dend (top,atlas) (g:B->real^3^3) z y - (dx - t)) = &0` THEN
  REAL_ARITH_TAC);;

