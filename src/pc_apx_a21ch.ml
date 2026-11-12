(* ========================================================================= *)
(* pc_apx_a21ch: MT Prop A.21 with the chains of the proof exposed, in the   *)
(* form of the statement P2BT_REQ_A21_CH_STATEMENT of pc_p2b_tubestmts       *)
(* (main theorem APXH_A21_CH).  The proof is that of pc_apx_a21              *)
(* (APX21_CASE_I, APX21_MAIN) with the capped-tube case returning the chain  *)
(* of APX21_GROWTH (first neck the end neck e0 of the maximal cap, oriented  *)
(* by APXH_ORIENT, compact closure of its lower half from APX21_CAP_ENDS)    *)
(* instead of the tube.                                                      *)
(* ========================================================================= *)

needs "src/pc_apx_a21.ml";;
needs "src/pc_p2b_tubestmts.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Orientation of the end neck, Case I and the assembly.                     *)
(* ------------------------------------------------------------------------- *)

(* The end neck e0 of a cap (APX21_CAP_ENDS) has its negative half next to  *)
(* the core: otherwise K = cl Y would be open (K + e0(slab(-1/eps,0)) is   *)
(* open) and closed in the connected cap U, though K and U - K = e0(dom)   *)
(* are nonempty.                                                             *)

let APXH_ORIENT = prove
 (`!top atlas (g:A->real^3^3) C eps U Y z0 (e0:real^3->A) K.
     rfs_cap (top,atlas) g C eps U Y /\ ~(Y = {}) /\ Y SUBSET K /\ K SUBSET U /\
     closed_in top K /\ rfs_neck (top,atlas) g eps z0 e0 /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\
     open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) (&0)))
     ==> ~(top closure_of (IMAGE e0 (apx_slab (--inv eps) (&0))) INTER K = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `A = IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))` THEN
  SUBGOAL_THEN `open_in top (K:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `K:A->bool = (K UNION A) INTER (topspace top DIFF top closure_of A)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `K:A->bool`] CLOSED_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `A:A->bool`] CLOSURE_OF_SUBSET_INTER) THEN
      UNDISCH_TAC `top closure_of A INTER (K:A->bool) = {}` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN
      REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_CLOSURE_OF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `K:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX21_CAP_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `C:real`; `eps:real`; `Y:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (e0:real^3->A) (rfs_neck_dom eps) = {})` MP_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `basis 1:real^3` THEN
    MP_TAC(ISPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z0 (e0:real^3->A)` THEN
      SIMP_TAC[rfs_neck];
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let APXH_CASE_I = prove
 (`!top atlas (g:A->real^3^3) C eps NK (X:A->bool) U Y x0.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx21_ext top atlas g eps /\ apx21_tubes top atlas g eps /\
     (!x1 (e2:real^3->A) U1 Y1. rfs_neck (top,atlas) g eps x1 e2 /\
                                rfs_cap (top,atlas) g C eps U1 Y1
                                ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))) /\
     &0 < C /\ compact_in top X /\ connected_in top X /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     (!x. x IN X ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y)) /\
     rfs_cap (top,atlas) g C eps U Y /\ x0 IN X /\ x0 IN Y
     ==> (?V. V IN connected_components_of top /\ compact_in top V /\ X SUBSET V) \/
         (?U Y. rfs_cap (top,atlas) g C eps U Y /\ X SUBSET U) \/
         (?U Y a b x e.
              rfs_cap (top,atlas) g C eps U Y /\ a < b /\
              apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
              IMAGE (e a) (rfs_neck_dom eps) = U DIFF top closure_of Y /\
              ~(top closure_of (IMAGE (e a) (apx_slab (--inv eps) (&0))) INTER
                top closure_of Y = {}) /\
              compact_in top (top closure_of (IMAGE (e a) (apx_slab (--inv eps) (&0)))) /\
              (!i. a < i /\ i <= b
                   ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
              X SUBSET U UNION apx_chain_union eps {i:int | a <= i /\ i <= b} e /\
              ~DISJOINT X (top closure_of Y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "nocap" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck_dom")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "cover" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck_dom"))
              (concl th)))) THEN
  SUBGOAL_THEN `hausdorff_space (top:A topology) /\
                smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                &0 < eps /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) eps` THEN SIMP_TAC[apx_ch_ctx];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps /\ &0 < sqrt(&2) /\ exp(&0 / sqrt(&2)) = &1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0]];
    ALL_TAC] THEN
  (* the maximal cap U0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `X:A->bool`; `U:A->bool`; `Y:A->bool`]
                APX21_MAXIMAL_CAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX21_CORE_IN_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(x0:A) IN X`; `(x0:A) IN Y`] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:A->bool` (X_CHOOSE_THEN `Y0:A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max"))))) THEN
  (* its end neck e0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U0:A->bool`; `Y0:A->bool`] APX21_CAP_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `z0:A` (X_CHOOSE_THEN `K0:A->bool`
      STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(LABEL_TAC "tfam" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `e0:real^3->A`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
  USE_THEN "tfam" (MP_TAC o SPEC `&0`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN STRIP_TAC THEN
  (* the longest chain *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `e0:real^3->A`; `z0:A`;
                 `K0:A->bool`; `U0:A->bool`] APX21_GROWTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `x:int->A` (X_CHOOSE_THEN `e:int->real^3->A`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k} x e`
  ASSUME_TAC THENL [ASM_MESON_TAC[apx_balanced]; ALL_TAC] THEN
  ABBREV_TAC `CU = apx_chain_union eps {i:int | &0 <= i /\ i <= &k} (e:int->real^3->A)` THEN
  SUBGOAL_THEN `~((X:A->bool) INTER (U0 UNION CU) = {})` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~DISJOINT (X:A->bool) (top closure_of Y0)`;
                           `top closure_of (Y0:A->bool) SUBSET K0`; `(K0:A->bool) SUBSET U0`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(X:A->bool) INTER top frontier_of (U0 UNION CU) = {}` THENL
   [(* stop (i): X lies in the capped chain *)
    SUBGOAL_THEN `(X:A->bool) SUBSET U0 UNION CU` ASSUME_TAC THENL
     [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `X:A->bool`; `U0 UNION CU:A->bool`]
                    CONNECTED_IN_INTER_FRONTIER_OF) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~((X:A->bool) SUBSET U0 UNION CU)`;
                             `~((X:A->bool) INTER (U0 UNION CU) = {})`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `k = 0` THENL
     [(* a single cap *)
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`U0:A->bool`; `Y0:A->bool`] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(CU:A->bool) SUBSET U0` MP_TAC THENL
       [EXPAND_TAC "CU" THEN
        REWRITE_TAC[SUBSET; APX21_IN_CHAIN_UNION; IN_ELIM_THM] THEN
        X_GEN_TAC `q:A` THEN DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `i = &0:int` SUBST_ALL_TAC THENL
         [UNDISCH_TAC `i <= &k:int` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `&0 <= i:int` THEN INT_ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `(q:A) IN IMAGE ((e:int->real^3->A)(&0)) (rfs_neck_dom eps)` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(X:A->bool) SUBSET U0 UNION CU` THEN SET_TAC[];
      ALL_TAC] THEN
    (* a capped tube *)
    DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN
     `!t. --inv eps + &11 <= t /\ t <= &0
          ==> open_in top (K0 UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) t)) /\
              top closure_of (K0 UNION IMAGE e0 (apx_slab (--inv eps) t)) SUBSET
              K0 UNION IMAGE e0 (apx_slab (--inv eps) t) UNION
              IMAGE e0 (sphere(vec 0,exp(t / sqrt(&2))))` ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "tfam" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `--inv eps + &11 <= t /\ t <= &0`))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `top closure_of (Y0:A->bool) = K0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(top closure_of (IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))) INTER K0 = {}) /\
      compact_in top (top closure_of (IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)))) /\
      &0:int < &k /\
      (!i. &0 < i /\ i <= &k
           ==> (x:int->A) i IN X /\
               ((NK:A->(real^3->A)->bool) (x i) (e i) \/ NK (x i) (apx_rev (e i))))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC APXH_ORIENT THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `C:real`; `U0:A->bool`; `Y0:A->bool`; `z0:A`] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CLOSED_COMPACT_IN THEN
        EXISTS_TAC `top closure_of (K0 UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)))` THEN
        ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[];
        REWRITE_TAC[INT_OF_NUM_LT] THEN UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
        X_GEN_TAC `i:int` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`U0:A->bool`; `Y0:A->bool`; `&0:int`; `&k:int`; `x:int->A`;
                          `e:int->real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* stop (c): a frontier point z of X in the core of a second cap *)
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `~(?ez. (NK:A->(real^3->A)->bool) z ez)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier_of")) (concl th) &&
      can (find_term (fun t -> t = `NK:A->(real^3->A)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?U' Y'. rfs_cap (top,atlas) (g:A->real^3^3) C eps U' Y' /\ (z:A) IN Y'`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cover" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:A) IN X`))) THEN
    UNDISCH_TAC `~(?ez. (NK:A->(real^3->A)->bool) z ez)` THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `X:A->bool`; `U0:A->bool`; `Y0:A->bool`; `e0:real^3->A`;
                 `K0:A->bool`; `k:num`; `x:int->A`; `e:int->real^3->A`; `U':A->bool`;
                 `Y':A->bool`; `z:A`] APX21_UNION_COMPONENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
      `apx_chain_union eps {i:int | &0 <= i /\ i <= &k} (e:int->real^3->A) = CU`])] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `k:num`; `x:int->A`; `e:int->real^3->A`] APX21_CHAIN_TUBE_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real`
      (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
        `apx_chain_union eps {i:int | &0 <= i /\ i <= &k} (e:int->real^3->A) = CU`]))))
    (K ALL_TAC))) THEN
  SUBGOAL_THEN `(X:A->bool) SUBSET (U0 UNION CU) UNION U' /\
                ~DISJOINT (X:A->bool) (top closure_of Y')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((X:A->bool) INTER (U0 UNION CU) = {})` THEN SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U':A->bool`; `Y':A->bool`]
                    APX21_CORE_IN_CLOSURE) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(z:A) IN X`; `(z:A) IN Y'`] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISJ1_TAC THEN EXISTS_TAC `(U0 UNION CU) UNION U':A->bool` THEN
  ASM_REWRITE_TAC[]);;

let APXH_MAIN = prove
 (`?eps0. &0 < eps0 /\
      !C eps top atlas g NK X.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3) /\ apx_sphere_sep top atlas /\
         compact_in top X /\ connected_in top X /\ ~(X = {}) /\
         (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
         (!x. x IN X
              ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y))
         ==> (?V. V IN connected_components_of top /\ compact_in top V /\ X SUBSET V) \/
             (?U Y. rfs_cap (top,atlas) g C eps U Y /\ X SUBSET U) \/
             (?U Y a b x e.
                  rfs_cap (top,atlas) g C eps U Y /\ a < b /\
                  apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
                  IMAGE (e a) (rfs_neck_dom eps) = U DIFF top closure_of Y /\
                  ~(top closure_of (IMAGE (e a) (apx_slab (--inv eps) (&0))) INTER
                    top closure_of Y = {}) /\
                  compact_in top (top closure_of (IMAGE (e a) (apx_slab (--inv eps) (&0)))) /\
                  (!i. a < i /\ i <= b
                       ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                  X SUBSET U UNION apx_chain_union eps {i:int | a <= i /\ i <= b} e /\
                  ~DISJOINT X (top closure_of Y)) \/
             (?a b x e.
                 a <= b /\
                 apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
                 (!i. a <= i /\ i <= b
                      ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                 X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e)`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_A19) THEN REWRITE_TAC[APX_A19_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e19:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a19"))) THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NO_CAP_IN_NECK_UNCOND) THEN
  REWRITE_TAC[APX_NO_CAP_IN_NECK_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `enc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `ectx:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] APX_CH_N4R_HOLDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `en4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] APX21_EXT_HOLDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `eext:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] APX21_TUBES_HOLDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `etub:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tub"))) THEN
  EXISTS_TAC `min e19 (min enc (min ectx (min en4 (min eext etub))))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `NK:A->(real^3->A)->bool`; `X:A->bool`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  (* the atlas is smooth: X has a point, a neck centre or in a cap core *)
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(X:A->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x0:A`) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x0:A) IN X`)) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_TAC `e:real^3->A`)
      (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC))) THENL
     [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(NK:A->(real^3->A)->bool) x0 e`)) THEN
      SIMP_TAC[rfs_neck];
      UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN SIMP_TAC[rfs_cap]];
    ALL_TAC] THEN
  (* the contexts at eps *)
  REMOVE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                     `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REMOVE_THEN "n4" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                    `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REMOVE_THEN "ext" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                     `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REMOVE_THEN "tub" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                     `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!x1 (e2:real^3->A) U1 Y1. rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e2 /\
                              rfs_cap (top,atlas) g C eps U1 Y1
                              ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x1:A`; `e2:real^3->A`; `U1:A->bool`; `Y1:A->bool`] THEN
    STRIP_TAC THEN
    REMOVE_THEN "nc" (MP_TAC o SPECL [`C:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `x1:A`;
      `e2:real^3->A`; `U1:A->bool`; `Y1:A->bool`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `!x:A. x IN X ==> ?e:real^3->A. NK x e` THENL
   [(* Case II: all points of X are NK-centres (A19) *)
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    REMOVE_THEN "a19" (MP_TAC o SPECL [`top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`;
      `NK:A->(real^3->A)->bool`; `X:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A`
      (X_CHOOSE_THEN `e:int->real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real`
        STRIP_ASSUME_TAC))))))))))) THEN
    MAP_EVERY EXISTS_TAC [`a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* Case I: a point x0 of X in a cap core *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC o
      REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    SUBGOAL_THEN `?U Y. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\ (x0:A) IN Y`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x0:A) IN X`)) THEN
      UNDISCH_TAC `~(?e:real^3->A. (NK:A->(real^3->A)->bool) x0 e)` THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `U:A->bool`;
                   `Y:A->bool`; `x0:A`] APXH_CASE_I) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> DISJ1_TAC THEN ACCEPT_TAC th)
      (DISJ_CASES_THEN2 (fun th -> DISJ2_TAC THEN DISJ1_TAC THEN ACCEPT_TAC th)
        (fun th -> DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ACCEPT_TAC th)))]);;

(* The headline: MT A.21 with the chains exposed (P2BT_REQ_A21_CH_STATEMENT). *)

let APXH_A21_CH = prove
 (`!u:A->bool. P2BT_REQ_A21_CH_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2BT_REQ_A21_CH_STATEMENT] THEN ACCEPT_TAC APXH_MAIN);;

