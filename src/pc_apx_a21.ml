(* ========================================================================= *)
(* pc_apx_a21: MT Prop A.21 in corrected form (APX_A21_STATEMENT, T6 of      *)
(* pc_apx_defs), separating case, compact connected X, class NK of necks.    *)
(* Main theorem APX_A21 |- !u. APX_A21_STATEMENT u (unconditional).  Method  *)
(* (MT pp. 508-514): Case II (all points of X are NK-neck centres) is        *)
(* APX_A19.  Case I: a maximal cap from Claim A.22 (APX_A22); attach         *)
(* X-centred NK-necks at frontier points (APX_A18) until no point of X on    *)
(* the frontier is an NK-centre (bounded length, APX_CHAIN_CARD_BOUND); then *)
(* X lies in the cap (single cap) or in the capped tube (A13 tube of the     *)
(* added necks), or a point of X on the frontier lies in the core of a       *)
(* second cap and the union is a compact component (MT Claims A.23-A.24).    *)
(* ========================================================================= *)

needs "src/pc_apx_a22.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The maximal cap (Claim A.22), the frontier of a cap                       *)
(* followed by a chain of necks, and the growth by X-centred NK-necks.       *)
(* ------------------------------------------------------------------------- *)

(* Membership in a chain union. *)

let APX21_IN_CHAIN_UNION = prove
 (`!eps Ix (e:int->real^3->A) q.
     q IN apx_chain_union eps Ix e <=> ?i. i IN Ix /\ q IN IMAGE (e i) (rfs_neck_dom eps)`,
  REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The maximal cap: a cap with closed core meeting X such that no cap       *)
(* containing it whose closed core meets X has a frontier point of it in    *)
(* its closed core (else iterate and contradict APX22_NO_CHAIN).  This is   *)
(* MT's choice of C0 in A.21 Case I, slightly stronger (any frontier point).*)

let APX21_MAXIMAL_CAP = prove
 (`!top atlas (g:A->real^3^3) C eps (X:A->bool) U Y.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\ &0 < C /\
     rfs_cap (top,atlas) g C eps U Y /\ ~DISJOINT X (top closure_of Y)
     ==> ?U0 Y0. rfs_cap (top,atlas) g C eps U0 Y0 /\ ~DISJOINT X (top closure_of Y0) /\
                 !U1 Y1. rfs_cap (top,atlas) g C eps U1 Y1 /\ U0 SUBSET U1 /\
                         ~DISJOINT X (top closure_of Y1)
                         ==> DISJOINT (top frontier_of U0) (top closure_of Y1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_THEN(LABEL_TAC "neg") THEN
  SUBGOAL_THEN
   `!U0 Y0. rfs_cap (top,atlas) (g:A->real^3^3) C eps U0 Y0 /\
            ~DISJOINT X (top closure_of Y0)
            ==> ?U1 Y1. (rfs_cap (top,atlas) g C eps U1 Y1 /\
                         ~DISJOINT X (top closure_of Y1)) /\ U0 SUBSET U1 /\
                        ~DISJOINT (top frontier_of U0) (top closure_of Y1)`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U0:A->bool`; `Y0:A->bool`] THEN STRIP_TAC THEN
    USE_THEN "neg" (MP_TAC o SPECL [`U0:A->bool`; `Y0:A->bool`] o
                    REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `fU:(A->bool)->(A->bool)->(A->bool)`
    (X_CHOOSE_THEN `fY:(A->bool)->(A->bool)->(A->bool)` (LABEL_TAC "st"))) THEN
  MP_TAC(ISPECL [`(U:A->bool,Y:A->bool)`;
                 `\(p:(A->bool)#(A->bool)) (n:num).
                    ((fU:(A->bool)->(A->bool)->(A->bool)) (FST p) (SND p),
                     (fY:(A->bool)->(A->bool)->(A->bool)) (FST p) (SND p))`]
                num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sq:num->(A->bool)#(A->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. rfs_cap (top,atlas) (g:A->real^3^3) C eps (FST(sq n)) (SND(sq n)) /\
        ~DISJOINT X (top closure_of (SND((sq:num->(A->bool)#(A->bool)) n)))`
  (LABEL_TAC "inv") THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "st" (MP_TAC o SPECL [`FST((sq:num->(A->bool)#(A->bool)) n)`;
                                   `SND((sq:num->(A->bool)#(A->bool)) n)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `\n. FST((sq:num->(A->bool)#(A->bool)) n)`;
                 `\n. SND((sq:num->(A->bool)#(A->bool)) n)`] APX22_NO_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  USE_THEN "st" (MP_TAC o SPECL [`FST((sq:num->(A->bool)#(A->bool)) n)`;
                                 `SND((sq:num->(A->bool)#(A->bool)) n)`]) THEN
  ANTS_TAC THENL [USE_THEN "inv" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[DISJOINT] THEN SIMP_TAC[]);;

(* The frontier of a cap U followed by a chain e0, ..., ek (e0 the oriented *)
(* end neck of U) lies in the closure of the top quarter of ek.            *)

let APX21_CAPPED_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) eps (e0:real^3->A) K U k x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ open_in top U /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     top frontier_of U SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps))) /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\ e(&0) = e0
     ==> top frontier_of (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)
         SUBSET top closure_of (IMAGE (e(&k)) (apx_slab (inv(&2 * eps)) (inv eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `CU = apx_chain_union eps {i:int | &0 <= i /\ i <= &k} (e:int->real^3->A)` THEN
  (* the chain union is open and contains the neck e0 *)
  SUBGOAL_THEN `open_in top (CU:A->bool) /\ IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET CU`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "CU" THEN REWRITE_TAC[apx_chain_union] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:int` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k}
                                x e` THEN
        REWRITE_TAC[apx_chain] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
          not (can (find_term (fun t -> t = `inv(&2 * eps)`)) (concl th)))) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[rfs_neck];
        REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
      EXISTS_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      EXISTS_TAC `&0:int` THEN REWRITE_TAC[INT_LE_REFL; INT_POS] THEN
      REWRITE_TAC[ASSUME `(e:int->real^3->A)(&0) = e0`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top frontier_of (CU:A->bool) SUBSET
                top closure_of (IMAGE ((e:int->real^3->A)(&0))
                                      (apx_slab (--inv eps) (--inv(&2 * eps))) UNION
                                IMAGE (e(&k)) (apx_slab (inv(&2 * eps)) (inv eps)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "CU" THEN MATCH_MP_TAC APX_FIN_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `x:int->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the closure of the low quarter of e0 lies in U *)
  SUBGOAL_THEN `top closure_of (IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps))))
                SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of (K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MONO THEN
      MATCH_MP_TAC(SET_RULE `!K A B:A->bool. A SUBSET B ==> A SUBSET K UNION B`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET
                  IMAGE e0 (rfs_neck_dom eps) /\
                  IMAGE (e0:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e0 (rfs_neck_dom eps)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THENL
       [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`top closure_of (K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1))`;
      `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET IMAGE e0 (rfs_neck_dom eps)`;
      `IMAGE (e0:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e0 (rfs_neck_dom eps)`;
      `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`; `(K:A->bool) SUBSET U`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!K U D S0 Sg cl:A->bool.
        K SUBSET U ==> D = U DIFF K ==> Sg SUBSET D ==> S0 SUBSET D ==>
        cl SUBSET K UNION S0 UNION Sg ==> cl SUBSET U`);
    ALL_TAC] THEN
  (* the top slab of e0 lies in the chain union *)
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps)) SUBSET CU`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `top frontier_of (U UNION CU:A->bool) =
                top closure_of (U UNION CU) DIFF (U UNION CU)` SUBST1_TAC THENL
   [MATCH_MP_TAC FRONTIER_OF_OPEN_IN THEN ASM_SIMP_TAC[OPEN_IN_UNION]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_OF_UNION] THEN
  SUBGOAL_THEN `top closure_of (U:A->bool) SUBSET U UNION top closure_of CU` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] FRONTIER_OF_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`;
                   `IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps))`; `CU:A->bool`]
                  CLOSURE_OF_MONO) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`top frontier_of (U:A->bool) SUBSET
       top closure_of (IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps)))`;
      `top frontier_of (U:A->bool) = top closure_of U DIFF U`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (CU:A->bool) SUBSET
                CU UNION U UNION
                top closure_of (IMAGE ((e:int->real^3->A)(&k))
                                      (apx_slab (inv(&2 * eps)) (inv eps)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `CU:A->bool`] FRONTIER_OF_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `top frontier_of (CU:A->bool) SUBSET
                 top closure_of (IMAGE ((e:int->real^3->A)(&0))
                                       (apx_slab (--inv eps) (--inv(&2 * eps))) UNION
                                 IMAGE (e(&k)) (apx_slab (inv(&2 * eps)) (inv eps)))` THEN
    ASM_REWRITE_TAC[CLOSURE_OF_UNION] THEN
    UNDISCH_TAC `top closure_of (IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps))))
                 SUBSET U` THEN
    UNDISCH_TAC `top frontier_of (CU:A->bool) = top closure_of CU DIFF CU` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`top closure_of (U:A->bool) SUBSET U UNION top closure_of CU`;
    `top closure_of (CU:A->bool) SUBSET
     CU UNION U UNION
     top closure_of (IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv(&2 * eps)) (inv eps)))`] THEN
  SET_TAC[]);;


(* The extension property of APX_A18 at a fixed scale. *)

let apx21_ext = new_definition
 `apx21_ext (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
            (eps:real) <=>
    !a b x (e:int->real^3->A) z ez.
       a <= b /\ apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
       z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps))) /\
       ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e) /\
       rfs_neck (top,atlas) g eps z ez
       ==> ?ez'. (ez' = ez \/ ez' = apx_rev ez) /\
                 apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b + &1}
                   (\i. if i = b + &1 then z else x i)
                   (\i. if i = b + &1 then ez' else e i)`;;

let APX21_EXT_HOLDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g /\
        apx_sphere_sep top atlas
        ==> apx21_ext top atlas g eps`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_A18) THEN REWRITE_TAC[APX_A18_STATEMENT; apx21_ext] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The number of indices of the chain segment 0..k. *)

let APX21_SEG_CARD = prove
 (`!k. FINITE {i:int | &0 <= i /\ i <= &k} /\ CARD {i:int | &0 <= i /\ i <= &k} = k + 1`,
  INDUCT_TAC THENL
   [SUBGOAL_THEN `{i:int | &0 <= i /\ i <= &0} = {&0}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN INT_ARITH_TAC;
      REWRITE_TAC[FINITE_SING; CARD_SING] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{i:int | &0 <= i /\ i <= &(SUC k)} = (&(SUC k)) INSERT {i | &0 <= i /\ i <= &k}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_INSERT; CARD_CLAUSES] THEN
  COND_CASES_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_ELIM_THM; GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC;
    ARITH_TAC]);;

(* A longest admissible chain from the end neck e0 of a cap: no point of     *)
(* X on the frontier of the cap with the chain is the centre of an NK-neck.  *)

let APX21_GROWTH = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) (e0:real^3->A) z0 K U.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx21_ext top atlas g eps /\ compact_in top X /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     rfs_neck (top,atlas) g eps z0 e0 /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ open_in top U /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     top frontier_of U SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps)))
     ==> ?k x e.
           apx_balanced (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\
           e(&0) = e0 /\ x(&0) = z0 /\
           (!i. &1 <= i /\ i <= &k
                ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
           (1 <= k ==> x(&1) IN top frontier_of U) /\
           (!z. z IN X /\
                z IN top frontier_of
                       (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)
                ==> ~(?ez. NK z ez))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `P = \k. ?x (e:int->real^3->A).
             apx_balanced (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k} x e /\
             e(&0) = e0 /\ x(&0) = (z0:A) /\
             (!i. &1 <= i /\ i <= &k
                  ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
             (1 <= k ==> x(&1) IN top frontier_of U)` THEN
  SUBGOAL_THEN `(P:num->bool) 0` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`\i:int. (z0:A)`; `\i:int. (e0:real^3->A)`] THEN
    REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_SINGLE_CHAIN THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  (* the length is bounded *)
  SUBGOAL_THEN `(z0:A) IN U` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z0:A) IN IMAGE (e0:real^3->A) (sphere(vec 0,&1)) /\
                  sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` MP_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
      MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_MESON_TAC[rfs_neck];
      UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `{z0:A} UNION X`] APX_CHAIN_CARD_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IN_UNION THEN
    ASM_REWRITE_TAC[COMPACT_IN_SING] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "card")) THEN
  SUBGOAL_THEN `!k. (P:num->bool) k ==> k <= N` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:int->A` (X_CHOOSE_THEN `e:int->real^3->A` STRIP_ASSUME_TAC)) THEN
    USE_THEN "card" (MP_TAC o SPECL [`{i:int | &0 <= i /\ i <= &k}`; `x:int->A`;
                                     `e:int->real^3->A`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[apx_balanced]; ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_SING] THEN X_GEN_TAC `i:int` THEN STRIP_TAC THEN
      ASM_CASES_TAC `i:int = &0` THENL
       [ASM_REWRITE_TAC[];
        DISJ2_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `X:A->bool`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_INT_ARITH_TAC; SIMP_TAC[]]];
      REWRITE_TAC[APX21_SEG_CARD] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. (P:num->bool) m /\ !k. P k ==> k <= m` MP_TAC THENL
   [REWRITE_TAC[GSYM num_MAX] THEN CONJ_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "max"))) THEN
  EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:int->A` (X_CHOOSE_THEN `e:int->real^3->A` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `x:int->A`; `e:int->real^3->A`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN DISCH_THEN(X_CHOOSE_TAC `ez:real^3->A`) THEN
  (* z lies near the top of the last neck and outside the chain union *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `e0:real^3->A`; `K:A->bool`; `U:A->bool`; `m:num`; `x:int->A`;
                 `e:int->real^3->A`] APX21_CAPPED_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_balanced]; DISCH_TAC] THEN
  SUBGOAL_THEN `~((z:A) IN apx_chain_union eps {i:int | &0 <= i /\ i <= &m} e)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN top frontier_of
                   (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &m} e)` THEN
    SUBGOAL_THEN `open_in top (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &m}
                                         (e:int->real^3->A))`
    MP_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[apx_chain_union] THEN
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:int` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `apx_balanced (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &m}
                                  x e` THEN
        REWRITE_TAC[apx_balanced; apx_chain] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
          not (can (find_term (fun t -> t = `inv(&2 * eps)`)) (concl th)))) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[rfs_neck];
        REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]];
      SIMP_TAC[FRONTIER_OF_OPEN_IN; IN_DIFF; IN_UNION; DE_MORGAN_THM]];
    ALL_TAC] THEN
  (* the extension by the NK-neck at z *)
  FIRST_ASSUM(MP_TAC o SPECL [`&0:int`; `&m:int`; `x:int->A`; `e:int->real^3->A`; `z:A`;
                              `ez:real^3->A`] o REWRITE_RULE[apx21_ext] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx21_ext")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_POS] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  USE_THEN "max" (MP_TAC o SPEC `m + 1`) THEN REWRITE_TAC[ARITH_RULE `~(m + 1 <= m)`] THEN
  EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`\i:int. if i = &m + &1 then (z:A) else x i`;
                        `\i:int. if i = &m + &1 then (ez':real^3->A) else e i`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `~(&0:int = &m + &1)`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:int` THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term (fun t -> t = `ez':real^3->A`)) (concl th))) THEN
      ASM_REWRITE_TAC[APX_REV_REV];
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `X:A->bool`)) (concl th) &&
        can (find_term (fun t -> t = `&1:int`)) (concl th))) THEN
      ASM_INT_ARITH_TAC];
    DISCH_TAC THEN ASM_CASES_TAC `m = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[INT_ADD_LID] THEN
      UNDISCH_TAC `(z:A) IN top frontier_of
                     (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &0} e)` THEN
      SUBGOAL_THEN `apx_chain_union eps {i:int | &0 <= i /\ i <= &0} (e:int->real^3->A)
                    SUBSET U` MP_TAC THENL
       [REWRITE_TAC[SUBSET; APX21_IN_CHAIN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN
        DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `i:int = &0` SUBST_ALL_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(q:A) IN IMAGE ((e:int->real^3->A) (&0)) (rfs_neck_dom eps)` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        SIMP_TAC[SET_RULE `!s t:A->bool. t SUBSET s ==> s UNION t = s`]];
      SUBGOAL_THEN `~(&1:int = &m + &1)` (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The cap ends at every level t (the core                                   *)
(* side K + e0(levels < t) is open, its closure adds only the level sphere   *)
(* t), and the necks of a chain from the end neck miss the closed core.      *)
(* ------------------------------------------------------------------------- *)

(* Images of closed shells inside the neck domain are compact. *)

let APX21_SHELL_COMPACT = prove
 (`!top atlas (e:real^3->A) eps a b.
     mfd_param top atlas (rfs_neck_dom eps) e /\
     exp(--inv eps / sqrt(&2)) < a /\ b < exp(inv eps / sqrt(&2))
     ==> compact_in top (IMAGE e {y:real^3 | a <= norm y /\ norm y <= b})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | a <= norm y /\ norm y <= b} = cball(vec 0,b) DIFF ball(vec 0,a)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
    REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Sets whose points are joinable inside them are connected (a copy of      *)
(* APX_JOINABLE_IN_CONNECTED of pc_apx_class, which is not loaded here).    *)

let APX21_JOINABLE_IN_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (U:A->bool).
     (!y1 y2. y1 IN U /\ y2 IN U ==> mfd_joinable_in (top,atlas) U y1 y2)
     ==> connected_in top U`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_IN_IMP_CONNECTED_IN THEN
  REWRITE_TAC[path_connected_in; path_connected_space] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[mfd_joinable_in] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `&0`; `&1`; `&0`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; SET_RULE `(s:A->bool) SUBSET t ==> t INTER s = s`] THEN
  MAP_EVERY X_GEN_TAC [`y1:A`; `y2:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y1:A`; `y2:A`]) THEN
  ASM_REWRITE_TAC[mfd_joinable_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[PATH_IN_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[path_in] THEN
    UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_SIMP_TAC[]]);;

(* Caps are connected. *)

let APX21_CAP_CONNECTED = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y ==> connected_in top U`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`]
                      APX21_JOINABLE_IN_CONNECTED) THEN
  MATCH_MP_TAC APX_CAP_JOINABLE THEN
  MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `Y:A->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The cap data of APX22_CAP_DATA with the closed core K = closure of the   *)
(* core Y, Y open and connected, and K DIFF Y on the central sphere of the  *)
(* boundary neck e'.                                                         *)

let APX21_CAP_DATA = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     hausdorff_space top /\ rfs_cap (top,atlas) g C eps U Y
     ==> smooth_manifold_atlas top atlas /\ open_in top U /\ ~(Y = {}) /\
         ?e z e' z' K.
           rfs_neck (top,atlas) g eps z e /\ rfs_neck (top,atlas) g eps z' e' /\
           IMAGE e (rfs_neck_dom eps) = U DIFF K /\
           compact_in top K /\ K SUBSET U /\ top closure_of Y SUBSET K /\ Y SUBSET K /\
           IMAGE e' (annulus (&1) (&2)) SUBSET U DIFF K /\
           open_in top (K UNION IMAGE e' (annulus (&1) (&3 / &2))) /\
           top closure_of (IMAGE e' (annulus (&1) (&3 / &2))) SUBSET
           K UNION IMAGE e' {y | &1 < norm y /\ norm y <= &3 / &2} /\
           K SUBSET top closure_of Y /\ open_in top Y /\ connected_in top Y /\
           K DIFF Y SUBSET IMAGE e' (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL APX_CAP_CORE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`;
                   `e'':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`] APX22_BALL_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`]
                  APX_BALL_CORE_TOP) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; STRIP_TAC] THEN
    SUBGOAL_THEN `IMAGE (b:real^3->A) (cball(vec 0,&1)) SUBSET
                  top closure_of (IMAGE b (ball(vec 0,&1))) /\
                  connected_in top (IMAGE (b:real^3->A) (ball(vec 0,&1))) /\
                  IMAGE (b:real^3->A) (cball(vec 0,&1)) DIFF IMAGE b (ball(vec 0,&1)) SUBSET
                  IMAGE b (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION; UNION_SUBSET] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
        ASM_MESON_TAC[OPEN_IN_SUBSET];
        MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
        REWRITE_TAC[CONNECTED_BALL] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[mfd_ball_chart];
          REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC];
        REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN SET_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->A`; `z:A`; `e'':real^3->A`; `z'':A`;
                          `IMAGE (b:real^3->A) (cball(vec 0,&1))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      SUBGOAL_THEN `IMAGE (b:real^3->A) (annulus (&1) (&2)) SUBSET U` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `DISJOINT (IMAGE (b:real^3->A) (annulus (&1) (&2)))
                              (IMAGE b (cball(vec 0,&1)))` THEN SET_TAC[]]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`;
                   `e'':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`]
                  APX22_TWISTED_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`]
                  APX_TWISTED_CORE_TOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `IMAGE (p:real^3->A) (sphere(vec 0,&1 / &2)) SUBSET IMAGE p (sphere(vec 0,&2))`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN EXISTS_TAC `rfs_twist y` THEN
      ASM_SIMP_TAC[APX_TWIST_SPHERE] THEN
      UNDISCH_TAC `rfs_twisted_chart top atlas (p:real^3->A)` THEN
      REWRITE_TAC[rfs_twisted_chart] THEN
      DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `rfs_twist y`] o CONJUNCT1) THEN
      ASM_SIMP_TAC[annulus; IN_ELIM_THM; APX_TWIST_SPHERE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `continuous_map (subtopology euclidean (annulus (&1 / &4) (&4)),top)
                                 (p:real^3->A)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_twisted_chart top atlas (p:real^3->A)` THEN
      REWRITE_TAC[rfs_twisted_chart] THEN DISCH_THEN(LABEL_TAC "loc" o CONJUNCT2) THEN
      MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ball(y:real^3,r)` THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_ANNULUS; OPEN_BALL; CENTRE_IN_BALL] THEN
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `ball(y:real^3,r)`; `p:real^3->A`] GRGD_PARAM_FACTS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2} SUBSET
      top closure_of (IMAGE p (annulus (&1 / &2) (&2))) /\
      connected_in top (IMAGE (p:real^3->A) (annulus (&1 / &2) (&2))) /\
      IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2} DIFF
      IMAGE p (annulus (&1 / &2) (&2)) SUBSET IMAGE p (sphere(vec 0,&2))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
        annulus (&1 / &2) (&2) UNION sphere(vec 0,&1 / &2) UNION sphere(vec 0,&2)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; annulus; IN_SPHERE_0] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[IMAGE_UNION; UNION_SUBSET] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
          ASM_MESON_TAC[SUBSET_TRANS]];
        MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
        EXISTS_TAC `subtopology euclidean (annulus (&1 / &4) (&4):real^3->bool)` THEN
        ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN;
                        APX_CONNECTED_ANNULUS3] THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[IMAGE_UNION] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->A`; `z:A`; `e'':real^3->A`; `z'':A`;
                          `IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2}`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `IMAGE (p:real^3->A) (annulus (&2) (&4)) SUBSET U` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `DISJOINT (IMAGE (p:real^3->A) (annulus (&2) (&4)))
                              (IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2})` THEN
        SET_TAC[]]]]);;

(* L1 of pc_apx_a22 at every level t in [-1/eps + 11, 0], with the core     *)
(* facts of APX21_CAP_DATA and the compactness of the closure of W_t.       *)

let APX21_CAP_ENDS = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     rfs_cap (top,atlas) g C eps U Y
     ==> open_in top U /\ ~(Y = {}) /\
         ?e0 z K.
           rfs_neck (top,atlas) g eps z e0 /\
           IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\
           compact_in top K /\ K SUBSET U /\ top closure_of Y SUBSET K /\ Y SUBSET K /\
           K SUBSET top closure_of Y /\ open_in top Y /\ connected_in top Y /\
           (?z' e'. rfs_neck (top,atlas) g eps z' e' /\
                    IMAGE e' (annulus (&1) (&2)) SUBSET U DIFF K /\
                    K DIFF Y SUBSET IMAGE e' (sphere(vec 0,&1))) /\
           top frontier_of U SUBSET
             top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps))) /\
           !t. --inv eps + &11 <= t /\ t <= &0
               ==> open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) t)) /\
                   top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) t)) SUBSET
                   K UNION IMAGE e0 (apx_slab (--inv eps) t) UNION
                   IMAGE e0 (sphere(vec 0,exp(t / sqrt(&2)))) /\
                   compact_in top
                     (top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX21_CAP_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `z':A`; `e':real^3->A`; `K:A->bool`;
                 `U:A->bool`] APX22_CAP_ENDS_RAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps z e0 /\
                IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[APX_REV_NECK; APX_REV_IMAGE_DOM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e0:real^3->A`; `z:A`; `K:A->bool`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`z':A`; `e':real^3->A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* basic facts *)
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e0:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z e0` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (K:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--inv eps / sqrt(&2)) < exp((--inv eps + d / &2) / sqrt(&2)) /\
    exp((--inv eps + d / &2) / sqrt(&2)) <= exp((--inv eps + d) / sqrt(&2)) /\
    exp(&0 / sqrt(&2)) = &1 /\ &1 < exp(inv eps / sqrt(&2)) /\
    exp((inv eps - &1) / sqrt(&2)) < exp(inv eps / sqrt(&2))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT; REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Cl = IMAGE (e':real^3->A) (annulus (&1) (&3 / &2))` THEN
  ABBREV_TAC `CS = IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2}` THEN
  SUBGOAL_THEN `(Cl:A->bool) SUBSET CS /\ (Cl:A->bool) SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Cl"; "CS"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K UNION Cl:A->bool` THEN
      REWRITE_TAC[SUBSET_UNION] THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0)) /\
                IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET U DIFF K`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &11))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> if concl th = `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`
        then REWRITE_TAC[SYM th] THEN ASSUME_TAC th else failwith "no") THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (Cl:A->bool) SUBSET K UNION IMAGE e0 (apx_slab (--inv eps) (&0))`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`top closure_of (Cl:A->bool) SUBSET K UNION CS`;
                           `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the middle shells *)
  ABBREV_TAC `Mi = {y:real^3 | exp((--inv eps + d / &2) / sqrt(&2)) <= norm y /\ norm y <= &1}` THEN
  ABBREV_TAC `Mo = {y:real^3 | exp((--inv eps + d / &2) / sqrt(&2)) <= norm y /\
                               norm y <= exp((inv eps - &1) / sqrt(&2))}` THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e0:real^3->A) Mi) /\ closed_in top (IMAGE (e0:real^3->A) Mo)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Mi"; "Mo"] THEN CONJ_TAC THEN MATCH_MP_TAC APX22_SHELL_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `apx_slab (--inv eps) (&0) SUBSET apx_slab (--inv eps) (--inv eps + d) UNION Mi /\
    Mi SUBSET apx_slab (--inv eps) (&0) UNION sphere(vec 0,&1) /\
    rfs_neck_dom eps SUBSET apx_slab (--inv eps) (--inv eps + d) UNION Mo UNION
                            apx_slab (inv eps - &1) (inv eps) /\
    Mo SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Mi"; "Mo"] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM] THEN
    REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_UNION; IN_SPHERE_0] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the frontier of U *)
      SUBGOAL_THEN `top frontier_of U = top closure_of U DIFF (U:A->bool)` SUBST1_TAC THENL
       [MATCH_MP_TAC FRONTIER_OF_OPEN_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `top closure_of (U:A->bool) SUBSET
        K UNION top closure_of Cl UNION IMAGE (e0:real^3->A) Mo UNION
        top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps)))` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
        ASM_SIMP_TAC[CLOSED_IN_UNION; CLOSED_IN_CLOSURE_OF] THEN
        MP_TAC(ISPECL [`top:A topology`; `Cl:A->bool`] CLOSURE_OF_SUBSET) THEN
        MP_TAC(ISPECL [`top:A topology`;
                       `IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps))`]
                      CLOSURE_OF_SUBSET) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
          MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
          DISCH_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET
                      IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) UNION IMAGE e0 Mo UNION
                      IMAGE e0 (apx_slab (inv eps - &1) (inv eps))` MP_TAC THENL
         [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`; `(K:A->bool) SUBSET U`;
          `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl`;
          `(Cl:A->bool) SUBSET top closure_of Cl`;
          `IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps)) SUBSET
           top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps)))`] THEN
        MATCH_ACCEPT_TAC(SET_RULE
         `!U K D A B C Cl cCl cC:A->bool.
            C SUBSET cC ==> Cl SUBSET cCl ==> A SUBSET Cl ==> K SUBSET U ==> D = U DIFF K ==>
            D SUBSET A UNION B UNION C ==> U SUBSET K UNION cCl UNION B UNION cC`);
    ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (e0:real^3->A) Mo SUBSET U` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K` THEN
          MATCH_ACCEPT_TAC(SET_RULE `!D U K:A->bool. D = U DIFF K ==> D SUBSET U`)];
    ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`top closure_of (Cl:A->bool) SUBSET K UNION IMAGE e0 (apx_slab (--inv eps) (&0))`;
        `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET U DIFF K`;
        `(K:A->bool) SUBSET U`] THEN
      MATCH_ACCEPT_TAC(SET_RULE
       `!K U S0 cCl Mo cU cT:A->bool.
          K SUBSET U ==> S0 SUBSET U DIFF K ==> cCl SUBSET K UNION S0 ==> Mo SUBSET U ==>
          cU SUBSET K UNION cCl UNION Mo UNION cT ==> cU DIFF U SUBSET cT`);
    ALL_TAC] THEN
  (* the core side W_t up to the level t *)
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `exp(t / sqrt(&2)) < exp(inv eps / sqrt(&2))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) t) /\
                IMAGE (e0:real^3->A) (apx_slab (--inv eps) t) SUBSET U DIFF K`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &11))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[SUBSET_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (Cl:A->bool) SUBSET K UNION IMAGE e0 (apx_slab (--inv eps) t)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`top closure_of (Cl:A->bool) SUBSET K UNION CS`;
                           `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) t)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Mt = {y:real^3 | exp((--inv eps + d / &2) / sqrt(&2)) <= norm y /\
                               norm y <= exp(t / sqrt(&2))}` THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e0:real^3->A) Mt)` ASSUME_TAC THENL
   [EXPAND_TAC "Mt" THEN MATCH_MP_TAC APX22_SHELL_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `apx_slab (--inv eps) t SUBSET apx_slab (--inv eps) (--inv eps + d) UNION Mt /\
    Mt SUBSET apx_slab (--inv eps) t UNION sphere(vec 0,exp(t / sqrt(&2)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Mt" THEN
    REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_UNION; IN_SPHERE_0] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) t)) SUBSET
                K UNION top closure_of (Cl:A->bool) UNION IMAGE e0 Mt` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION; CLOSED_IN_CLOSURE_OF] THEN
      MP_TAC(ISPECL [`top:A topology`; `Cl:A->bool`] CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `IMAGE (e0:real^3->A) (apx_slab (--inv eps) t) SUBSET
                    IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) UNION IMAGE e0 Mt`
      MP_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl`;
          `(Cl:A->bool) SUBSET top closure_of Cl`] THEN
        SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* W is open *)
    SUBGOAL_THEN `K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) t) =
                  (K UNION Cl) UNION IMAGE e0 (apx_slab (--inv eps) t)` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(Cl:A->bool) SUBSET CS`;
                             `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) t)`] THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[apx_slab; OPEN_ANNULUS];
        MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the closure of W *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `K UNION top closure_of (Cl:A->bool) UNION IMAGE (e0:real^3->A) Mt` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (e0:real^3->A) Mt SUBSET
                    IMAGE e0 (apx_slab (--inv eps) t) UNION IMAGE e0 (sphere(vec 0,exp(t / sqrt(&2))))`
      MP_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `top closure_of (Cl:A->bool) SUBSET
                     K UNION IMAGE e0 (apx_slab (--inv eps) t)` THEN
        SET_TAC[]];
    (* the closure of W is compact *)
    SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < &1 /\ &3 / &2 < exp(inv eps / sqrt(&2))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
        REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `inv eps / sqrt(&2)` REAL_EXP_LE_X) THEN
        SUBGOAL_THEN `&1 <= inv eps / sqrt(&2)` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
          SUBGOAL_THEN `sqrt(&2) <= &3 / &2` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `K UNION IMAGE (e':real^3->A) {y | &1 <= norm y /\ norm y <= &3 / &2} UNION
                IMAGE (e0:real^3->A) Mt` THEN
    REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX21_SHELL_COMPACT THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' e'` THEN SIMP_TAC[rfs_neck];
        EXPAND_TAC "Mt" THEN MATCH_MP_TAC APX21_SHELL_COMPACT THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(CS:A->bool) SUBSET
                    IMAGE (e':real^3->A) {y | &1 <= norm y /\ norm y <= &3 / &2}`
      MP_TAC THENL
       [EXPAND_TAC "CS" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`top closure_of (Cl:A->bool) SUBSET K UNION CS`;
        `top closure_of (K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) t)) SUBSET
         K UNION top closure_of (Cl:A->bool) UNION IMAGE e0 Mt`] THEN
      MATCH_ACCEPT_TAC(SET_RULE
       `!cW K cCl M CS E1:A->bool.
          cW SUBSET K UNION cCl UNION M ==> cCl SUBSET K UNION CS ==> CS SUBSET E1 ==>
          cW SUBSET K UNION E1 UNION M`)]]);;

(* The necks e1, ..., ek of a chain from the end neck e0 of a cap miss the  *)
(* closed core K: each misses the low quarter of e0 (chain clause), and a   *)
(* connected set meeting K and missing that quarter lies in K, while e1    *)
(* meets e0 and e(i+1) meets e(i).                                          *)

let APX21_CHAIN_OFF_CORE = prove
 (`!top atlas (g:A->real^3^3) eps (e0:real^3->A) K U k x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\
     (!t. --inv eps + &11 <= t /\ t <= &0
          ==> open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) t)) /\
              top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) t)) SUBSET
              K UNION IMAGE e0 (apx_slab (--inv eps) t) UNION
              IMAGE e0 (sphere(vec 0,exp(t / sqrt(&2))))) /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\ e(&0) = e0
     ==> !i. &1 <= i /\ i <= &k ==> DISJOINT K (IMAGE (e i) (rfs_neck_dom eps))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "fam") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))) THEN
  REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "neck") (CONJUNCTS_THEN2 (LABEL_TAC "ovl") (LABEL_TAC "dsj"))))) THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps) /\ inv(&2 * eps) + &512 <= inv eps` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t0 = --inv(&2 * eps) - &1` THEN
  SUBGOAL_THEN `--inv eps + &11 <= t0 /\ t0 <= &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "fam" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `--inv eps + &11 <= t0`) (ASSUME `t0 <= &0`)))) THEN STRIP_TAC THEN
  (* the low quarter of e0 contains the slab below t0 and the level sphere t0 *)
  SUBGOAL_THEN `apx_slab (--inv eps) t0 UNION sphere(vec 0:real^3,exp(t0 / sqrt(&2))) SUBSET
                apx_slab (--inv eps) (--inv(&2 * eps))` ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; APX_SPHERE_LEVEL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_SLAB_SUBSET THEN EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* later necks miss that quarter *)
  SUBGOAL_THEN `!i. &1 <= i /\ i <= &k
                    ==> DISJOINT (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps))
                                 (IMAGE e0 (apx_slab (--inv eps) t0) UNION
                                  IMAGE e0 (sphere(vec 0,exp(t0 / sqrt(&2)))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "dsj" (MP_TAC o SPECL [`&0:int`; `i:int`]) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a b c:A->bool. b SUBSET c ==> DISJOINT a c ==> DISJOINT a b`) THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a neck meeting K lies in K *)
  SUBGOAL_THEN `!i. &1 <= i /\ i <= &k /\
                    ~DISJOINT K (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps))
                    ==> IMAGE (e i) (rfs_neck_dom eps) SUBSET K` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)`;
                   `K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) t0)`]
                  APX22_CLOPEN_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
        REWRITE_TAC[SUBSET_REFL; rfs_neck_dom; APX_CONNECTED_ANNULUS3] THEN
        REWRITE_TAC[GSYM rfs_neck_dom] THEN
        USE_THEN "neck" (MP_TAC o SPEC `i:int`) THEN
        ANTS_TAC THENL [ASM_INT_ARITH_TAC; SIMP_TAC[rfs_neck]];
        FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `t0:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `top closure_of (K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) t0))
                     SUBSET K UNION IMAGE e0 (apx_slab (--inv eps) t0) UNION
                            IMAGE e0 (sphere(vec 0,exp(t0 / sqrt(&2))))` THEN
        SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `t0:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~DISJOINT K (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* consecutive necks meet *)
  SUBGOAL_THEN `!i. &0 <= i /\ i + &1 <= &k
                    ==> ~DISJOINT (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps))
                                  (IMAGE (e(i + &1)) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "ovl" (MP_TAC o SPEC `i:int`) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(SPECL [`inv(&2 * eps)`; `inv eps`] APX_SLAB_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; SUBSET; IN_UNION] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->A) i y`) THEN
    ANTS_TAC THENL [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                    MESON_TAC[]];
    ALL_TAC] THEN
  (* induction along the chain *)
  SUBGOAL_THEN `!n. 1 <= n /\ n <= k
                    ==> DISJOINT K (IMAGE ((e:int->real^3->A) (&n)) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `&(SUC n):int` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
      can (find_term (fun t -> t = `K:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `&n:int` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&1:int`)) (concl th) &&
      not (can (find_term (fun t -> t = `K:A->bool`)) (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_POS; INT_OF_NUM_ADD; INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[INT_OF_NUM_ADD; GSYM ADD1]) THEN
    ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_TAC `~DISJOINT (IMAGE ((e:int->real^3->A) (&n)) (rfs_neck_dom eps))
                             (IMAGE (e(&(SUC n))) (rfs_neck_dom eps))` THEN
      UNDISCH_TAC `IMAGE ((e:int->real^3->A) (&(SUC n))) (rfs_neck_dom eps) SUBSET K` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K` THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        can (find_term (fun t -> t = `n:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~DISJOINT (IMAGE ((e:int->real^3->A) (&n)) (rfs_neck_dom eps))
                             (IMAGE (e(&(SUC n))) (rfs_neck_dom eps))` THEN
      UNDISCH_TAC `IMAGE ((e:int->real^3->A) (&(SUC n))) (rfs_neck_dom eps) SUBSET K` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `i:int` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. (i:int) = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN UNDISCH_TAC `&1:int <= i` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`&1:int <= &n`; `&n:int <= &k`] THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The capped tube.  A sub-chain of a chain; the A13 tubes at a fixed scale; *)
(* the capped tube of a cap followed by a chain e0, ..., ek (k >= 1): the    *)
(* A13 tube E of e1, ..., ek meets U, leaves U at its outer end, and misses  *)
(* the closed core.                                                          *)
(* ------------------------------------------------------------------------- *)

let APX21_SUBCHAIN = prove
 (`!top atlas (g:A->real^3^3) eps Ix Jx x (e:int->real^3->A).
     apx_chain (top,atlas) g eps Ix x e /\ apx_int_interval Jx /\ ~(Jx = {}) /\
     Jx SUBSET Ix
     ==> apx_chain (top,atlas) g eps Jx x e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_chain] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* The A13 conclusion at a fixed scale. *)

let apx21_tubes = new_definition
 `apx21_tubes (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
              (eps:real) <=>
    !n x (e:int->real^3->A).
       apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e
       ==> ?E L f f'.
             &0 <= L /\ sphere_diffeo f f' /\
             mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
             (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
             (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
                  ==> E y = e (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
             IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
             apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e /\
             apx_tube (top,atlas) g eps E (exp(--inv eps / sqrt(&2)))
                      (exp((L + inv eps) / sqrt(&2)))`;;

let APX21_TUBES_HOLDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g /\
        apx_sphere_sep top atlas
        ==> apx21_tubes top atlas g eps`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_A13_UNCOND) THEN REWRITE_TAC[apx21_tubes] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:int->A` THEN ASM_REWRITE_TAC[]);;

(* Radial extensions of sphere diffeomorphisms preserve the level. *)

let APX21_SVAL_RADIAL = prove
 (`!f f' v:real^3. sphere_diffeo f f' ==> apx_sval(radial_ext f v) = apx_sval v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_diffeo] THEN STRIP_TAC THEN
  REWRITE_TAC[apx_sval] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[]);;

(* The capped tube. *)

let APX21_CAPPED_TUBE = prove
 (`!top atlas (g:A->real^3^3) eps U Y (e0:real^3->A) K k x (e:int->real^3->A) (X:A->bool).
     apx_ch_ctx top atlas g eps /\ apx21_tubes top atlas g eps /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ top closure_of Y SUBSET K /\
     (!t. --inv eps + &11 <= t /\ t <= &0
          ==> open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) t)) /\
              top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) t)) SUBSET
              K UNION IMAGE e0 (apx_slab (--inv eps) t) UNION
              IMAGE e0 (sphere(vec 0,exp(t / sqrt(&2))))) /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\ e(&0) = e0 /\ 1 <= k /\
     X SUBSET U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e
     ==> ?E r1 rho r2.
           apx_tube (top,atlas) g eps E r1 r2 /\ r1 < rho /\ rho < r2 /\
           ~(U INTER IMAGE E (annulus r1 r2) = {}) /\
           DISJOINT U (IMAGE E (annulus rho r2)) /\
           DISJOINT (top closure_of Y) (IMAGE E (annulus r1 r2)) /\
           X SUBSET U UNION IMAGE E (annulus r1 r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `e0:real^3->A`; `K:A->bool`; `U:A->bool`; `k:num`; `x:int->A`;
                 `e:int->real^3->A`] APX21_CHAIN_OFF_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps) /\ inv(&2 * eps) + &512 <= inv eps /\
                &0 < inv(&8 * eps)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &(k - 1):int = &k /\ &(k - 1) + &1:int = &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the chain clauses *)
  UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k} x e` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "neck") (CONJUNCTS_THEN2 (LABEL_TAC "ovl") (LABEL_TAC "dsj"))))) THEN
  (* the sub-chain 1..k, shifted to 0..k-1, and its A13 tube *)
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps
                  {i:int | &1 <= i /\ i <= &1 + &(k - 1)} x e` MP_TAC THENL
   [MATCH_MP_TAC APX21_SUBCHAIN THEN EXISTS_TAC `{i:int | &0 <= i /\ i <= &k}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[apx_int_interval; IN_ELIM_THM] THEN INT_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&1:int` THEN
      REWRITE_TAC[INT_LE_REFL] THEN REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP APX_CHAIN_SHIFT) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k - 1`; `\i:int. (x:int->A)(i + &1)`;
                                `\i:int. (e:int->real^3->A)(i + &1)`] o
    REWRITE_RULE[apx21_tubes] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx21_tubes")) (concl th))) THEN
  ASM_REWRITE_TAC[INT_ADD_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`E:real^3->A`; `exp(--inv eps / sqrt(&2))`; `exp((L + inv(&2 * eps)) / sqrt(&2))`;
    `exp((L + inv eps) / sqrt(&2))`] THEN
  ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN
  ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
  SUBGOAL_THEN `annulus (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2))) =
                apx_slab (--inv eps) (L + inv eps) /\
                annulus (exp((L + inv(&2 * eps)) / sqrt(&2))) (exp((L + inv eps) / sqrt(&2))) =
                apx_slab (L + inv(&2 * eps)) (L + inv eps)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[apx_slab]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* U meets the tube: e0 and e1 overlap *)
    USE_THEN "ovl" (MP_TAC o SPEC `&0:int`) THEN
    ANTS_TAC THENL [REWRITE_TAC[INT_ADD_LID; INT_POS; INT_LE_REFL; INT_OF_NUM_LE] THEN
                    ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[INT_ADD_LID] THEN
    MP_TAC(SPECL [`inv(&2 * eps)`; `inv eps`] APX_SLAB_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `(e0:real^3->A) y`) THEN
    ANTS_TAC THENL [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(e0:real^3->A) y` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(e0:real^3->A) y IN U DIFF K` THEN SET_TAC[];
      REWRITE_TAC[APX21_IN_CHAIN_UNION; IN_ELIM_THM] THEN EXISTS_TAC `&1:int` THEN
      ASM_REWRITE_TAC[INT_LE_REFL; INT_OF_NUM_LE; LE_REFL]];
    (* the outer end of the tube is off U *)
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (L - inv(&8 * eps)) (L + inv eps)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (L + inv(&2 * eps)) (L + inv eps)` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN
      apx_slab (L - inv(&8 * eps)) (L + inv eps)`) o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `radial_ext (f:real^3->real^3)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `radial_ext (f:real^3->real^3) (exp(--L / sqrt(&2)) % y) IN
                  apx_slab (inv(&2 * eps)) (inv eps)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (L + inv(&2 * eps)) (L + inv eps)` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`;
                     `exp(--L / sqrt(&2)) % y:real^3`] APX21_SVAL_RADIAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[APX_SVAL_EXP_SCALE] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[GSYM NORM_EQ_0] THEN
      UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN REWRITE_TAC[sphere_diffeo] THEN
      STRIP_TAC THEN MP_TAC(ISPECL [`f:real^3->real^3`; `exp(--L / sqrt(&2)) % y:real^3`]
                                   SMT_RADIAL_EXT_NORM) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_MUL_EQ_0; REAL_EXP_NZ];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:A) IN IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv(&2 * eps)) (inv eps))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "dsj" (MP_TAC o SPECL [`&0:int`; `&k:int`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_LE_REFL; INT_POS; INT_OF_NUM_LT] THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&k:int` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K:A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    REWRITE_TAC[INT_LE_REFL; INT_OF_NUM_LE; LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET
                  IMAGE (e(&k)) (rfs_neck_dom eps)` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(q:A) IN U`;
                           `(q:A) IN IMAGE ((e:int->real^3->A)(&k))
                                        (apx_slab (inv(&2 * eps)) (inv eps))`;
                           `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`] THEN
    ABBREV_TAC `Pk = IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv(&2 * eps)) (inv eps))` THEN
    ABBREV_TAC `Dk = IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
    ABBREV_TAC `D0 = IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    (* the closed core misses the tube *)
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `q:A` THEN
    REWRITE_TAC[APX21_IN_CHAIN_UNION; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K:A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(q:A) IN top closure_of Y`; `top closure_of (Y:A->bool) SUBSET K`;
                           `(q:A) IN IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)`] THEN
    SET_TAC[];
    (* X lies in U and the tube *)
    UNDISCH_TAC `(X:A->bool) SUBSET U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e` THEN
    REWRITE_TAC[SUBSET; IN_UNION; APX21_IN_CHAIN_UNION; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:int = &0` THENL
     [DISJ1_TAC THEN UNDISCH_TAC `(q:A) IN IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for MT Claim A.23.  The frontier of a capped chain                 *)
(* lies in the closure Ft of the thin top slab of its last neck; if a point *)
(* of Ft lies in the core of a second cap U', Ft lies in the core side of   *)
(* U' (scales compare through the boundary neck, APX22_CORE_FAR); the A13   *)
(* tube of the chain is connected and has a compact middle; a maximal cap   *)
(* cannot lie inside a cap whose core meets the frontier of the chain.      *)
(* ------------------------------------------------------------------------- *)

(* Claim A.23, step (a): the frontier of a capped chain lies in the closure  *)
(* of the thin top slab of the last neck (the shell between the quarter      *)
(* level and the top slab is a closed subset of the chain union).            *)

let APX21_CAPPED_FRONTIER_TOP = prove
 (`!top atlas (g:A->real^3^3) eps (e0:real^3->A) K U k x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ open_in top U /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     top frontier_of U SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps))) /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\ e(&0) = e0
     ==> top frontier_of (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)
         SUBSET top closure_of (IMAGE (e(&k)) (apx_slab (inv eps - &1) (inv eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `e0:real^3->A`; `K:A->bool`; `U:A->bool`; `k:num`; `x:int->A`;
                 `e:int->real^3->A`] APX21_CAPPED_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps) /\ inv(&2 * eps) + &256 <= inv eps` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `CU = apx_chain_union eps {i:int | &0 <= i /\ i <= &k} (e:int->real^3->A)` THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps (x(&k:int)) (e(&k:int))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k} x e` THEN
    REWRITE_TAC[apx_chain] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&k:int` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
      not (can (find_term (fun t -> t = `inv(&2 * eps)`)) (concl th)))) THEN
    REWRITE_TAC[IN_ELIM_THM; INT_LE_REFL; INT_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) ((e:int->real^3->A)(&k))` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  (* the neck e k lies in the chain union, which is open *)
  SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps) SUBSET CU` ASSUME_TAC THENL
   [EXPAND_TAC "CU" THEN REWRITE_TAC[apx_chain_union; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `&k:int` THEN REWRITE_TAC[INT_LE_REFL; INT_POS];
    ALL_TAC] THEN
  ABBREV_TAC `Sh = {y:real^3 | exp((inv(&2 * eps)) / sqrt(&2)) <= norm y /\
                               norm y <= exp((inv eps - &1) / sqrt(&2))}` THEN
  SUBGOAL_THEN `closed_in top (IMAGE ((e:int->real^3->A)(&k)) Sh)` ASSUME_TAC THENL
   [EXPAND_TAC "Sh" THEN MATCH_MP_TAC APX22_SHELL_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (inv(&2 * eps)) (inv eps) SUBSET Sh UNION apx_slab (inv eps - &1) (inv eps) /\
                Sh SUBSET rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Sh" THEN REWRITE_TAC[APX_SLAB_NECK_DOM] THEN
    REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_UNION] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^3` THENL
     [REAL_ARITH_TAC;
      SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < exp((inv(&2 * eps)) / sqrt(&2)) /\
                    exp((inv eps - &1) / sqrt(&2)) < exp(inv eps / sqrt(&2))` MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (U UNION CU:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "CU" THEN
    REWRITE_TAC[apx_chain_union] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k}
                              x e` THEN
      REWRITE_TAC[apx_chain] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
        not (can (find_term (fun t -> t = `inv(&2 * eps)`)) (concl th)))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[rfs_neck];
      REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv(&2 * eps)) (inv eps)))
                SUBSET IMAGE (e(&k)) Sh UNION
                       top closure_of (IMAGE (e(&k)) (apx_slab (inv eps - &1) (inv eps)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of (IMAGE ((e:int->real^3->A)(&k)) Sh UNION
                                IMAGE (e(&k)) (apx_slab (inv eps - &1) (inv eps)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MONO THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CLOSURE_OF_UNION; CLOSURE_OF_CLOSED_IN; SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&k)) Sh SUBSET CU` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `U UNION CU:A->bool`] FRONTIER_OF_OPEN_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`top frontier_of (U UNION CU:A->bool) = top closure_of (U UNION CU) DIFF (U UNION CU)`;
    `top frontier_of (U UNION CU:A->bool) SUBSET
     top closure_of (IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv(&2 * eps)) (inv eps)))`;
    `top closure_of (IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv(&2 * eps)) (inv eps)))
     SUBSET IMAGE (e(&k)) Sh UNION
            top closure_of (IMAGE (e(&k)) (apx_slab (inv eps - &1) (inv eps)))`;
    `IMAGE ((e:int->real^3->A)(&k)) Sh SUBSET CU`] THEN
  SET_TAC[]);;

(* Step (a), continued: if a point z of the core Y of a second cap lies in   *)
(* the closure Ft of the thin top slab of a neck ek, then Ft lies in the     *)
(* core side W = K + e'(levels < 0) of that cap (e' its complement neck):    *)
(* either Ft lies in Y, or Ft meets K - Y, which lies on the central sphere  *)
(* of the boundary neck e''; then the scales of ek, e'' and e' compare, Ft   *)
(* is short (APX22_TOP_CLOSURE_DIST) and points of K are far from the exit   *)
(* of W (APX22_CORE_FAR).                                                    *)

let APX21_TOP_IN_CORE_SIDE = prove
 (`!top atlas (g:A->real^3^3) eps xk (ek:real^3->A) z' (e':real^3->A) z'' (e'':real^3->A)
    K Y z.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps xk ek /\
     rfs_neck (top,atlas) g eps z' e' /\ rfs_neck (top,atlas) g eps z'' e'' /\
     DISJOINT K (IMAGE e' (rfs_neck_dom eps)) /\
     open_in top (K UNION IMAGE e' (apx_slab (--inv eps) (&0))) /\
     top closure_of (K UNION IMAGE e' (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e' (apx_slab (--inv eps) (&0)) UNION IMAGE e' (sphere(vec 0,&1)) /\
     IMAGE e'' (annulus (&1) (&2)) SUBSET IMAGE e' (rfs_neck_dom eps) /\
     open_in top Y /\ Y SUBSET K /\ top closure_of Y SUBSET K /\
     K DIFF Y SUBSET IMAGE e'' (sphere(vec 0,&1)) /\
     z IN Y /\ z IN top closure_of (IMAGE ek (apx_slab (inv eps - &1) (inv eps)))
     ==> top closure_of (IMAGE ek (apx_slab (inv eps - &1) (inv eps))) SUBSET
         K UNION IMAGE e' (apx_slab (--inv eps) (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Ft = top closure_of (IMAGE (ek:real^3->A) (apx_slab (inv eps - &1) (inv eps)))` THEN
  SUBGOAL_THEN `connected_in top (Ft:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ft" THEN MATCH_MP_TAC CONNECTED_IN_CLOSURE_OF THEN
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3] THEN REWRITE_TAC[GSYM apx_slab] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps xk ek` THEN SIMP_TAC[rfs_neck];
      MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(Ft:A->bool) SUBSET Y` THENL
   [MAP_EVERY UNDISCH_TAC [`(Ft:A->bool) SUBSET Y`; `(Y:A->bool) SUBSET K`] THEN SET_TAC[];
    ALL_TAC] THEN
  (* a point f of Ft on the boundary sphere of the core *)
  MP_TAC(ISPECL [`top:A topology`; `Ft:A->bool`; `Y:A->bool`]
                CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`~((Ft:A->bool) SUBSET Y)`; `(z:A) IN Y`; `(z:A) IN Ft`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `(f:A) IN K /\ f IN IMAGE (e'':real^3->A) (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:A) IN top frontier_of Y` THEN ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN] THEN
    MAP_EVERY UNDISCH_TAC [`top closure_of (Y:A->bool) SUBSET K`;
                           `(K:A->bool) DIFF Y SUBSET IMAGE (e'':real^3->A) (sphere(vec 0,&1))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the scales *)
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps /\
                annulus (&1) (&2) SUBSET rfs_neck_dom eps /\
                apx_slab (inv eps - &1) (inv eps) SUBSET rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[];
      MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET b ==> b SUBSET c ==> a SUBSET c`) THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. v IN rfs_neck_dom eps /\ (ek:real^3->A) v IN IMAGE e'' (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `IMAGE (e'':real^3->A) (rfs_neck_dom eps)`;
                   `IMAGE (ek:real^3->A) (apx_slab (inv eps - &1) (inv eps))`]
                  OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      REWRITE_TAC[SUBSET_REFL; rfs_neck_dom; OPEN_ANNULUS] THEN REWRITE_TAC[GSYM rfs_neck_dom] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z'' e''` THEN SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:A) IN IMAGE (e'':real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
     [UNDISCH_TAC `(f:A) IN IMAGE (e'':real^3->A) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(f:A) IN Ft` THEN
    UNDISCH_TAC `apx_slab (inv eps - &1) (inv eps) SUBSET rfs_neck_dom eps` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) xk)) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas g z''))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&3 / &2`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`e'':real^3->A`; `ek:real^3->A`; `v:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'')) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas g z'))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&3 / &2`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`e':real^3->A`; `e'':real^3->A`; `&3 / &2 % basis 1:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&3 / &2 % basis 1:real^3 IN annulus (&1) (&2)` ASSUME_TAC THENL
     [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `annulus (&1) (&2) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `&3 / &2 % basis 1:real^3 IN annulus (&1) (&2)` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (e'':real^3->A) (annulus (&1) (&2)) SUBSET IMAGE e' (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `&3 / &2 % basis 1:real^3 IN annulus (&1) (&2)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* every point of Ft lies in W *)
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `xk:A`; `ek:real^3->A`; `f:A`; `q:A`] APX22_TOP_CLOSURE_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_ch_ctx] THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`; `K:A->bool`; `f:A`; `q:A`]
                APX22_CORE_FAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_ch_ctx] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `hk = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) xk))` THEN
  ABBREV_TAC `h2 = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z''))` THEN
  ABBREV_TAC `h1 = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'))` THEN
  SUBGOAL_THEN `&0 < hk /\ &0 < h1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hk"; "h1"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC PI_POS THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hk * (&1 + sqrt(&2) * pi) <= (&9 / &4 * h1) * (&29 / &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN MP_TAC APX_SQRT2_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h1 * &1024 <= h1 * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Step (d): the A13 tube of the whole chain e0, ..., ek: its union is a    *)
(* connected eps-tube, covered by the low end slab of e0, a compact middle   *)
(* shell and the thin top slab of ek.                                        *)

let APX21_CHAIN_TUBE_COVER = prove
 (`!top atlas (g:A->real^3^3) eps k x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx21_tubes top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e
     ==> connected_in top (apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e) /\
         (?E r1 r2. apx_tube (top,atlas) g eps E r1 r2 /\
                    IMAGE E (annulus r1 r2) =
                    apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e) /\
         (?Q. compact_in top Q /\
              apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e SUBSET
              IMAGE (e(&0)) (apx_slab (--inv eps) (--inv eps + &11)) UNION Q UNION
              IMAGE (e(&k)) (apx_slab (inv eps - &1) (inv eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `apx21_tubes top atlas (g:A->real^3^3) eps` THEN REWRITE_TAC[apx21_tubes] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `x:int->A`; `e:int->real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&8 * eps) /\ --inv eps + &11 <= inv(&8 * eps) /\
                inv(&8 * eps) <= &1 / &8 * inv eps` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain_union")) (concl th)
    then SUBST1_TAC(SYM th) THEN ASSUME_TAC th else failwith "no") THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab (--inv eps) (L + inv eps)`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; apx_slab; APX_CONNECTED_ANNULUS3];
    MAP_EVERY EXISTS_TAC [`E:real^3->A`; `exp(--inv eps / sqrt(&2))`;
                          `exp((L + inv eps) / sqrt(&2))`] THEN
    ASM_REWRITE_TAC[GSYM apx_slab];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (E:real^3->A) {y | exp((--inv eps + &11) / sqrt(&2)) <= norm y /\
                                     norm y <= exp((L + inv eps - &1) / sqrt(&2))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab (--inv eps) (L + inv eps)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | exp((--inv eps + &11) / sqrt(&2)) <= norm y /\
                                norm y <= exp((L + inv eps - &1) / sqrt(&2))} =
                    cball(vec 0,exp((L + inv eps - &1) / sqrt(&2))) DIFF
                    ball(vec 0,exp((--inv eps + &11) / sqrt(&2)))` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
      SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < exp((--inv eps + &11) / sqrt(&2)) /\
                    exp((L + inv eps - &1) / sqrt(&2)) < exp((L + inv eps) / sqrt(&2))`
      MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN REAL_ARITH_TAC;
        REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNION] THEN
  ASM_CASES_TAC `norm(y:real^3) < exp((--inv eps + &11) / sqrt(&2))` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (--inv eps + &11) /\
                  y IN apx_slab (--inv eps) (inv(&8 * eps))` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
      SUBGOAL_THEN `exp((--inv eps + &11) / sqrt(&2)) <= exp(inv(&8 * eps) / sqrt(&2))`
      MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
      UNDISCH_TAC `norm(y:real^3) < exp((--inv eps + &11) / sqrt(&2))` THEN
      REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN
      apx_slab (--inv eps) (inv(&8 * eps))`) o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `inv(&8 * eps)`)) (concl th) &&
      not (can (find_term (fun t -> t = `radial_ext (f:real^3->real^3)`)) (concl th)))) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `exp((L + inv eps - &1) / sqrt(&2)) < norm(y:real^3)` THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (L + inv eps - &1) (L + inv eps) /\
                  y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
      SUBGOAL_THEN `exp((L - inv(&8 * eps)) / sqrt(&2)) <= exp((L + inv eps - &1) / sqrt(&2))`
      MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `exp((L + inv eps - &1) / sqrt(&2)) < norm(y:real^3)` THEN
      REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN
      apx_slab (L - inv(&8 * eps)) (L + inv eps)`) o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `radial_ext (f:real^3->real^3)`)) (concl th))) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (L + inv eps - &1) (L + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`;
                   `exp(--L / sqrt(&2)) % y:real^3`] APX21_SVAL_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[APX_SVAL_EXP_SCALE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM NORM_EQ_0] THEN
    UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN REWRITE_TAC[sphere_diffeo] THEN
    STRIP_TAC THEN MP_TAC(ISPECL [`f:real^3->real^3`; `exp(--L / sqrt(&2)) % y:real^3`]
                                 SMT_RADIAL_EXT_NORM) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_MUL_EQ_0; REAL_EXP_NZ];
    ALL_TAC] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* Disjoint subsets of the domain of a parametrization have disjoint images  *)
(* (a copy of APX_PARAM_IMAGE_DISJOINT of pc_apx_class, not loaded here).    *)

let APX21_PARAM_IMAGE_DISJOINT = prove
 (`!top atlas s (e:real^3->A) a b.
     mfd_param top atlas s e /\ a SUBSET s /\ b SUBSET s /\ DISJOINT a b
     ==> DISJOINT (IMAGE e a) (IMAGE e b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `q:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `u:real^3 = v` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `s:real^3->bool`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* The upper half 1 <= |y| < R of an annulus (R >= 2) is connected. *)

let APX21_UPPER_CONNECTED = prove
 (`!R. &2 <= R ==> connected {y:real^3 | &1 <= norm y /\ norm y < R}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `annulus (&1) R:real^3->bool` THEN REWRITE_TAC[APX_CONNECTED_ANNULUS3] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `closure(annulus (&1) (&2)) SUBSET closure(annulus (&1) R:real^3->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_CLOSURE THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `annulus (&1) R:real^3->bool` CLOSURE_SUBSET) THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] APX_SPHERE_CLOSURE_ANNULUS) THEN
  REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
  MESON_TAC[REAL_ARITH `&1 <= x ==> x = &1 \/ &1 < x`]);;

(* Step (c): a capped chain with a frontier point z in the core Y' of a cap *)
(* U' cannot have its cap U inside U' when U is maximal: then the closed    *)
(* core K1 of U' misses the frontier of U (maximality), hence misses U      *)
(* (K1 connected, z in K1 outside U), and the closed core of U lies in the  *)
(* complement neck of U', which no cap core does (APX_NO_CAP_IN_NECK).      *)

let APX21_NOT_INSIDE = prove
 (`!top atlas (g:A->real^3^3) C eps (X:A->bool) U Y K U' Y' K1 (e1:real^3->A) z1 z.
     (!x1 (e2:real^3->A) U1 Y1. rfs_neck (top,atlas) g eps x1 e2 /\
                                rfs_cap (top,atlas) g C eps U1 Y1
                                ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))) /\
     rfs_cap (top,atlas) g C eps U Y /\
     (!U1 Y1. rfs_cap (top,atlas) g C eps U1 Y1 /\ U SUBSET U1 /\
              ~DISJOINT X (top closure_of Y1)
              ==> DISJOINT (top frontier_of U) (top closure_of Y1)) /\
     K SUBSET U /\ top closure_of Y SUBSET K /\
     rfs_cap (top,atlas) g C eps U' Y' /\ rfs_neck (top,atlas) g eps z1 e1 /\
     IMAGE e1 (rfs_neck_dom eps) = U' DIFF K1 /\ K1 SUBSET top closure_of Y' /\
     top closure_of Y' SUBSET K1 /\ connected_in top Y' /\ Y' SUBSET topspace top /\
     U SUBSET U' /\ z IN X /\ z IN Y' /\ ~(z IN U)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN top closure_of Y'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `Y':A->bool`] CLOSURE_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:A) IN Y'` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U':A->bool`; `Y':A->bool`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier_of")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `DISJOINT (K1:A->bool) U` ASSUME_TAC THENL
   [SUBGOAL_THEN `K1 = top closure_of (Y':A->bool)` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT] THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `top closure_of (Y':A->bool)`; `U:A->bool`]
                  CONNECTED_IN_INTER_FRONTIER_OF) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CONNECTED_IN_CLOSURE_OF] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN EXISTS_TAC `z:A` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT (top frontier_of U) (top closure_of (Y':A->bool))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z1:A`; `e1:real^3->A`; `U:A->bool`; `Y:A->bool`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck_dom")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`top closure_of (Y:A->bool) SUBSET K`; `(K:A->bool) SUBSET U`;
                         `(U:A->bool) SUBSET U'`; `DISJOINT (K1:A->bool) U`] THEN
  SET_TAC[]);;

(* MT Claim A.23: a capped chain whose frontier contains a point z of X    *)
(* in the core Y' of a cap U': the union of the cap U, the chain and U' is  *)
(* a compact connected component.  The core side W1 of U' contains the      *)
(* frontier of the capped chain (APX21_TOP_IN_CORE_SIDE); the upper part T  *)
(* of the complement neck of U' (levels >= 0) is connected and misses W1,   *)
(* so it lies in the capped chain or misses it; the latter puts U inside    *)
(* U', impossible by APX21_NOT_INSIDE.  Hence the frontier of U' (in the    *)
(* closure of T) lies in the union, which is closed, and it lies in the     *)
(* compact closures of the core sides and the middle of the chain tube.     *)

let APX21_UNION_COMPONENT = prove
 (`!top atlas (g:A->real^3^3) C eps (X:A->bool) U Y (e0:real^3->A) K k x (e:int->real^3->A)
    U' Y' z.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx21_tubes top atlas g eps /\
     (!x1 (e2:real^3->A) U1 Y1. rfs_neck (top,atlas) g eps x1 e2 /\
                                rfs_cap (top,atlas) g C eps U1 Y1
                                ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))) /\
     rfs_cap (top,atlas) g C eps U Y /\
     (!U1 Y1. rfs_cap (top,atlas) g C eps U1 Y1 /\ U SUBSET U1 /\
              ~DISJOINT X (top closure_of Y1)
              ==> DISJOINT (top frontier_of U) (top closure_of Y1)) /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ top closure_of Y SUBSET K /\
     open_in top U /\
     top frontier_of U SUBSET top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps))) /\
     (!t. --inv eps + &11 <= t /\ t <= &0
          ==> open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) t)) /\
              top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) t)) SUBSET
              K UNION IMAGE e0 (apx_slab (--inv eps) t) UNION
              IMAGE e0 (sphere(vec 0,exp(t / sqrt(&2)))) /\
              compact_in top (top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) t)))) /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\ e(&0) = e0 /\
     rfs_cap (top,atlas) g C eps U' Y' /\ z IN X /\ z IN Y' /\
     z IN top frontier_of (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)
     ==> (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e) UNION U'
           IN connected_components_of top /\
         compact_in top ((U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e) UNION U')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "nocap" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck_dom")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "max" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier_of")) (concl th))) THEN
  SUBGOAL_THEN `hausdorff_space (top:A topology) /\
                smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                &0 < eps /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) eps` THEN SIMP_TAC[apx_ch_ctx];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps + &11 <= &0 /\ exp(&0 / sqrt(&2)) = &1 /\
                exp(--inv eps / sqrt(&2)) < &1 /\ &2 <= exp(inv eps / sqrt(&2)) /\
                &1 <= exp((inv eps - &1) / sqrt(&2))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN REWRITE_TAC[GSYM real_div] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `inv eps / sqrt(&2)` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&1 <= inv eps / sqrt(&2)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MP_TAC(SPEC `(inv eps - &1) / sqrt(&2)` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&0 <= (inv eps - &1) / sqrt(&2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the core side W0 of U at level 0 *)
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `e0:real^3->A`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  (* the data of U' *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U':A->bool`; `Y':A->bool`] APX21_CAP_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e1:real^3->A` (X_CHOOSE_THEN `z1:A` (X_CHOOSE_THEN `K1:A->bool`
      STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `e1:real^3->A`)) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  (* the last neck, the frontier of the capped chain, the tube of the chain *)
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps (x(&k:int)) (e(&k:int))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k} x e` THEN
    REWRITE_TAC[apx_chain] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&k:int` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
      not (can (find_term (fun t -> t = `inv(&2 * eps)`)) (concl th)))) THEN
    REWRITE_TAC[IN_ELIM_THM; INT_LE_REFL; INT_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `e0:real^3->A`; `K:A->bool`; `U:A->bool`; `k:num`; `x:int->A`;
                 `e:int->real^3->A`] APX21_CAPPED_FRONTIER_TOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `k:num`; `x:int->A`; `e:int->real^3->A`] APX21_CHAIN_TUBE_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `Q:A->bool`
      (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(e:int->real^3->A)(&0) = e0`])))) THEN
  SUBGOAL_THEN `(z:A) IN top closure_of (IMAGE ((e:int->real^3->A)(&k))
                                               (apx_slab (inv eps - &1) (inv eps)))`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(z:A) IN top frontier_of
                  (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)`;
      `top frontier_of (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e) SUBSET
       top closure_of (IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv eps - &1) (inv eps)))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* step (a): the top of the chain lies in the core side W1 of U' *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:int->A)(&k)`; `(e:int->real^3->A)(&k)`; `z1:A`;
                 `e1:real^3->A`; `z':A`; `e':real^3->A`; `K1:A->bool`; `Y':A->bool`; `z:A`]
                APX21_TOP_IN_CORE_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `top closure_of (K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))) SUBSET
    (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) UNION IMAGE e0 (sphere(vec 0,&1)) /\
    top closure_of (K1 UNION IMAGE (e1:real^3->A) (apx_slab (--inv eps) (&0))) SUBSET
    (K1 UNION IMAGE e1 (apx_slab (--inv eps) (&0))) UNION IMAGE e1 (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[UNION_ASSOC]; ALL_TAC] THEN
  ABBREV_TAC `CU = apx_chain_union eps {i:int | &0 <= i /\ i <= &k} (e:int->real^3->A)` THEN
  ABBREV_TAC `Ft = top closure_of (IMAGE ((e:int->real^3->A)(&k))
                                         (apx_slab (inv eps - &1) (inv eps)))` THEN
  ABBREV_TAC `W0 = K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))` THEN
  ABBREV_TAC `W1 = K1 UNION IMAGE (e1:real^3->A) (apx_slab (--inv eps) (&0))` THEN
  (* the capped chain C = U + CU: open, connected, z on its frontier *)
  SUBGOAL_THEN `open_in top (U UNION CU:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "CU" THEN
    REWRITE_TAC[apx_chain_union] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k}
                              x e` THEN
      REWRITE_TAC[apx_chain] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
        not (can (find_term (fun t -> t = `inv(&2 * eps)`)) (concl th)))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[rfs_neck];
      REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET CU` ASSUME_TAC THENL
   [EXPAND_TAC "CU" THEN REWRITE_TAC[APX21_IN_CHAIN_UNION; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `&0:int` THEN
    REWRITE_TAC[IN_ELIM_THM; INT_LE_REFL; INT_POS; ASSUME `(e:int->real^3->A)(&0) = e0`] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(U INTER CU:A->bool = {})` ASSUME_TAC THENL
   [MP_TAC(SPECL [`--inv eps`; `inv eps`] APX_SLAB_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM APX_SLAB_NECK_DOM]] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
    SUBGOAL_THEN `(e0:real^3->A) y IN IMAGE e0 (rfs_neck_dom eps)` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET CU`;
                           `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!D U K CU q:A. D = U DIFF K ==> D SUBSET CU ==> q IN D ==> ~(U INTER CU = {})`);
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (U UNION CU:A->bool) /\ connected_in top (U':A->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX21_CAP_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `C:real`;
                            `eps:real`; `Y:A->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC APX21_CAP_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `C:real`;
                            `eps:real`; `Y':A->bool`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN top closure_of (U UNION CU) /\ ~((z:A) IN U UNION CU)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN top frontier_of (U UNION CU)` THEN
    ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y':A->bool) SUBSET W1 /\ (W1:A->bool) SUBSET U'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "W1" THEN UNDISCH_TAC `(Y':A->bool) SUBSET K1` THEN SET_TAC[];
      EXPAND_TAC "W1" THEN REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e1:real^3->A) (rfs_neck_dom eps)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    ALL_TAC] THEN
  (* the upper part e1(Tu) of the complement neck of U' (levels >= 0) *)
  ABBREV_TAC `Tu = {y:real^3 | &1 <= norm y /\ norm y < exp(inv eps / sqrt(&2))}` THEN
  SUBGOAL_THEN `(Tu:real^3->bool) SUBSET rfs_neck_dom eps /\
                DISJOINT Tu (apx_slab (--inv eps) (&0)) /\
                apx_slab (inv eps - &1) (inv eps) SUBSET Tu /\
                sphere(vec 0,&1) SUBSET Tu /\
                rfs_neck_dom eps SUBSET apx_slab (--inv eps) (&0) UNION Tu /\
                apx_slab (--inv eps) (&0) SUBSET rfs_neck_dom eps /\
                connected Tu` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Tu" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_slab; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus;
                  IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_UNION] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC APX21_UPPER_CONNECTED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e1:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z1 e1` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (IMAGE (e1:real^3->A) Tu)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e1:real^3->A) Tu SUBSET U' DIFF K1` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e1:real^3->A) (rfs_neck_dom eps)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (e1:real^3->A) Tu) W1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e1:real^3->A`; `Tu:real^3->bool`;
                   `apx_slab (--inv eps) (&0)`] APX21_PARAM_IMAGE_DISJOINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "W1" THEN
    UNDISCH_TAC `IMAGE (e1:real^3->A) Tu SUBSET U' DIFF K1` THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!A K D S:A->bool. A SUBSET D DIFF K ==> DISJOINT A S ==> DISJOINT A (K UNION S)`);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e1:real^3->A) (apx_slab (inv eps - &1) (inv eps)) SUBSET IMAGE (e1:real^3->A) Tu /\
                IMAGE (e1:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE (e1:real^3->A) Tu`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U':A->bool) SUBSET W1 UNION IMAGE (e1:real^3->A) Tu` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (e1:real^3->A) (rfs_neck_dom eps) SUBSET
                  IMAGE e1 (apx_slab (--inv eps) (&0)) UNION IMAGE (e1:real^3->A) Tu` MP_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "W1" THEN
    MAP_EVERY UNDISCH_TAC [`IMAGE (e1:real^3->A) (rfs_neck_dom eps) = U' DIFF K1`;
                           `(K1:A->bool) SUBSET U'`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!K U D S Tt:A->bool. K SUBSET U ==> D = U DIFF K ==> D SUBSET S UNION Tt ==>
                           U SUBSET (K UNION S) UNION Tt`);
    ALL_TAC] THEN
  (* steps (b), (c): the upper part lies in the capped chain *)
  SUBGOAL_THEN `(Y':A->bool) SUBSET topspace top /\ IMAGE (e1:real^3->A) Tu INTER
                top closure_of (U UNION CU) SUBSET U UNION CU` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `U UNION CU:A->bool`] FRONTIER_OF_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`top frontier_of (U UNION CU:A->bool) = top closure_of (U UNION CU) DIFF (U UNION CU)`;
      `top frontier_of (U UNION CU:A->bool) SUBSET Ft`; `(Ft:A->bool) SUBSET W1`;
      `DISJOINT (IMAGE (e1:real^3->A) Tu) W1`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!Tt C fC cC Ft W1:A->bool. DISJOINT Tt W1 ==> Ft SUBSET W1 ==> fC SUBSET Ft ==>
                                 fC = cC DIFF C ==> Tt INTER cC SUBSET C`);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e1:real^3->A) Tu SUBSET U UNION CU` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `IMAGE (e1:real^3->A) Tu`; `U UNION CU:A->bool`]
                  APX22_CLOPEN_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~b ==> (a \/ b) ==> a`) THEN DISCH_TAC THEN
    (* then the capped chain lies in W1 *)
    SUBGOAL_THEN `(U UNION CU:A->bool) SUBSET W1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `U UNION CU:A->bool`; `W1:A->bool`]
                    APX22_CLOPEN_SPLIT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`top closure_of W1 SUBSET W1 UNION IMAGE (e1:real^3->A) (sphere(vec 0,&1))`;
          `IMAGE (e1:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE (e1:real^3->A) Tu`;
          `DISJOINT (IMAGE (e1:real^3->A) Tu) (U UNION CU)`] THEN
        MATCH_ACCEPT_TAC(SET_RULE
         `!Tt C S cW W:A->bool. DISJOINT Tt C ==> S SUBSET Tt ==> cW SUBSET W UNION S ==>
                                C INTER cW SUBSET W`);
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `~b ==> (a \/ b) ==> a`) THEN
      MP_TAC(ISPECL [`top:A topology`; `W1:A->bool`; `U UNION CU:A->bool`]
                    OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(z:A) IN top closure_of (U UNION CU)`; `(z:A) IN Y'`;
                             `(Y':A->bool) SUBSET W1`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `X:A->bool`; `U:A->bool`; `Y:A->bool`; `K:A->bool`;
                   `U':A->bool`; `Y':A->bool`; `K1:A->bool`; `e1:real^3->A`; `z1:A`; `z:A`]
                  APX21_NOT_INSIDE) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`~((z:A) IN U UNION CU)`; `(U UNION CU:A->bool) SUBSET W1`;
                           `(W1:A->bool) SUBSET U'`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the union V = C + U' is open and closed *)
  SUBGOAL_THEN `top closure_of (U UNION CU:A->bool) SUBSET (U UNION CU) UNION W1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U UNION CU:A->bool`] FRONTIER_OF_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`top frontier_of (U UNION CU:A->bool) = top closure_of (U UNION CU) DIFF (U UNION CU)`;
      `top frontier_of (U UNION CU:A->bool) SUBSET Ft`; `(Ft:A->bool) SUBSET W1`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!C fC cC Ft W:A->bool. Ft SUBSET W ==> fC SUBSET Ft ==> fC = cC DIFF C ==>
                             cC SUBSET C UNION W`);
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (U':A->bool) SUBSET (U UNION CU) UNION U'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U':A->bool`] FRONTIER_OF_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `top closure_of (IMAGE (e1:real^3->A) (apx_slab (inv eps - &1) (inv eps)))
                  SUBSET top closure_of (U UNION CU)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MONO THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (e1:real^3->A) Tu` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(W1:A->bool) SUBSET U'`;
      `top closure_of (U UNION CU:A->bool) SUBSET (U UNION CU) UNION W1`;
      `top closure_of (IMAGE (e1:real^3->A) (apx_slab (inv eps - &1) (inv eps)))
       SUBSET top closure_of (U UNION CU)`;
      `top frontier_of (U':A->bool) SUBSET
       top closure_of (IMAGE (e1:real^3->A) (apx_slab (inv eps - &1) (inv eps)))`;
      `top frontier_of (U':A->bool) = top closure_of U' DIFF U'`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!U' fU cU cE cC C W:A->bool.
        fU = cU DIFF U' ==> fU SUBSET cE ==> cE SUBSET cC ==> cC SUBSET C UNION W ==>
        W SUBSET U' ==> cU SUBSET C UNION U'`);
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top ((U UNION CU) UNION U':A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top ((U UNION CU) UNION U':A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ISPECL [`top:A topology`; `U UNION CU:A->bool`; `U':A->bool`]
                       CLOSURE_OF_UNION] THEN
    MAP_EVERY UNDISCH_TAC
     [`top closure_of (U UNION CU:A->bool) SUBSET (U UNION CU) UNION W1`;
      `top closure_of (U':A->bool) SUBSET (U UNION CU) UNION U'`;
      `(W1:A->bool) SUBSET U'`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!C U' W cC cU:A->bool. W SUBSET U' ==> cU SUBSET C UNION U' ==> cC SUBSET C UNION W ==>
                             cC UNION cU SUBSET C UNION U'`);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* a connected component *)
    MATCH_MP_TAC APX_CLOPEN_COMPONENT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `U':A->bool`; `U UNION CU:A->bool`]
                    OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(z:A) IN top closure_of (U UNION CU)`; `(z:A) IN Y'`;
                             `(Y':A->bool) SUBSET W1`; `(W1:A->bool) SUBSET U'`] THEN
      SET_TAC[];
      UNDISCH_TAC `~(U INTER CU:A->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* compactness: inside the closures of the core sides and the middle of the tube *)
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `top closure_of W0 UNION Q UNION top closure_of (W1:A->bool)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET W0 /\
                IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &11)) SUBSET W0 /\
                IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv eps - &1) (inv eps)) SUBSET Ft /\
                (W0:A->bool) SUBSET top closure_of W0 /\
                (W1:A->bool) SUBSET top closure_of W1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "W0" THEN SET_TAC[];
      EXPAND_TAC "W0" THEN MATCH_MP_TAC(SET_RULE
       `!K A B:A->bool. A SUBSET B ==> A SUBSET K UNION B`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Ft" THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps (x(&k:int)) (e(&k:int))` THEN
        SIMP_TAC[rfs_neck];
        MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(W1:A->bool) SUBSET top closure_of W1`; `(W0:A->bool) SUBSET top closure_of W0`;
    `IMAGE (e1:real^3->A) Tu SUBSET U UNION CU`; `(U':A->bool) SUBSET W1 UNION IMAGE (e1:real^3->A) Tu`;
    `(Ft:A->bool) SUBSET W1`;
    `IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv eps - &1) (inv eps)) SUBSET Ft`;
    `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &11)) SUBSET W0`;
    `CU SUBSET IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &11)) UNION Q UNION
               IMAGE ((e:int->real^3->A)(&k)) (apx_slab (inv eps - &1) (inv eps))`;
    `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET CU`;
    `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`; `(K:A->bool) SUBSET W0`] THEN
  MATCH_ACCEPT_TAC(SET_RULE
   `!U K D CU W0 L Q E Ft W1 U' Tt cW0 cW1:A->bool.
      K SUBSET W0 ==> D = U DIFF K ==> D SUBSET CU ==>
      CU SUBSET L UNION Q UNION E ==> L SUBSET W0 ==> E SUBSET Ft ==> Ft SUBSET W1 ==>
      U' SUBSET W1 UNION Tt ==> Tt SUBSET U UNION CU ==>
      W0 SUBSET cW0 ==> W1 SUBSET cW1 ==>
      (U UNION CU) UNION U' SUBSET cW0 UNION Q UNION cW1`));;

(* ------------------------------------------------------------------------- *)
(* The assembly.  Case I (APX21_CASE_I), the thresholds and                  *)
(* Case II (APX21_MAIN, the body of APX_A21_STATEMENT), and the headline.    *)
(* ------------------------------------------------------------------------- *)


(* Points of a cap core lie in its closure. *)

let APX21_CORE_IN_CLOSURE = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     hausdorff_space top /\ rfs_cap (top,atlas) g C eps U Y
     ==> Y SUBSET topspace top /\ Y SUBSET top closure_of Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX_CAP_CORE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBSET]);;

(* MT A.21 Case I.  A point x0 of X in the core of a cap: the maximal cap   *)
(* U0 (APX21_MAXIMAL_CAP), its end neck e0 (APX21_CAP_ENDS), the longest   *)
(* chain of X-centred NK-necks from e0 (APX21_GROWTH).  If X misses the     *)
(* frontier of the capped chain, X lies in U0 (k = 0: a single cap) or in   *)
(* the capped tube (k >= 1, APX21_CAPPED_TUBE); otherwise a frontier point  *)
(* of X lies in the core of a cap U' and the union is a compact component   *)
(* (APX21_UNION_COMPONENT), its chain part an eps-tube (A13).               *)

let APX21_CASE_I = prove
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
     ==> (?V U1 Y1 U2 Y2.
              V IN connected_components_of top /\ compact_in top V /\
              X SUBSET V /\
              rfs_cap (top,atlas) g C eps U1 Y1 /\ ~DISJOINT X (top closure_of Y1) /\
              rfs_cap (top,atlas) g C eps U2 Y2 /\ ~DISJOINT X (top closure_of Y2) /\
              (V = U1 UNION U2 \/
               (?E r1 r2. apx_tube (top,atlas) g eps E r1 r2 /\
                          V = U1 UNION IMAGE E (annulus r1 r2) UNION U2))) \/
         (?U Y. rfs_cap (top,atlas) g C eps U Y /\ X SUBSET U /\
                ~DISJOINT X (top closure_of Y)) \/
         (?U Y E r1 rho r2.
              rfs_cap (top,atlas) g C eps U Y /\
              apx_tube (top,atlas) g eps E r1 r2 /\ r1 < rho /\ rho < r2 /\
              ~(U INTER IMAGE E (annulus r1 r2) = {}) /\
              DISJOINT U (IMAGE E (annulus rho r2)) /\
              DISJOINT (top closure_of Y) (IMAGE E (annulus r1 r2)) /\
              X SUBSET U UNION IMAGE E (annulus r1 r2) /\
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
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `U0:A->bool`; `Y0:A->bool`; `e0:real^3->A`; `K0:A->bool`;
                   `k:num`; `x:int->A`; `e:int->real^3->A`; `X:A->bool`] APX21_CAPPED_TUBE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `r1:real`
      (X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`U0:A->bool`; `Y0:A->bool`; `E:real^3->A`; `r1:real`; `rho:real`;
                          `r2:real`] THEN
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
  DISJ1_TAC THEN
  MAP_EVERY EXISTS_TAC [`(U0 UNION CU) UNION U':A->bool`; `U0:A->bool`; `Y0:A->bool`;
                        `U':A->bool`; `Y':A->bool`] THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `r1:real`; `r2:real`] THEN
  ASM_REWRITE_TAC[UNION_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* MT Prop A.21 (the body of APX_A21_STATEMENT):                             *)
(* the thresholds of the chain context, N4 sections, A18, A13, A19 and N5;   *)
(* Case II is APX_A19, Case I is APX21_CASE_I.                               *)
(* ------------------------------------------------------------------------- *)

let APX21_MAIN = prove
 (`?eps0. &0 < eps0 /\
      !C eps top atlas g NK X.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3) /\ apx_sphere_sep top atlas /\
         compact_in top X /\ connected_in top X /\ ~(X = {}) /\
         (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
         (!x. x IN X
              ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y))
         ==> (?V U1 Y1 U2 Y2.
                  V IN connected_components_of top /\ compact_in top V /\
                  X SUBSET V /\
                  rfs_cap (top,atlas) g C eps U1 Y1 /\ ~DISJOINT X (top closure_of Y1) /\
                  rfs_cap (top,atlas) g C eps U2 Y2 /\ ~DISJOINT X (top closure_of Y2) /\
                  (V = U1 UNION U2 \/
                   (?E r1 r2. apx_tube (top,atlas) g eps E r1 r2 /\
                              V = U1 UNION IMAGE E (annulus r1 r2) UNION U2))) \/
             (?U Y. rfs_cap (top,atlas) g C eps U Y /\ X SUBSET U /\
                    ~DISJOINT X (top closure_of Y)) \/
             (?U Y E r1 rho r2.
                  rfs_cap (top,atlas) g C eps U Y /\
                  apx_tube (top,atlas) g eps E r1 r2 /\ r1 < rho /\ rho < r2 /\
                  ~(U INTER IMAGE E (annulus r1 r2) = {}) /\
                  DISJOINT U (IMAGE E (annulus rho r2)) /\
                  DISJOINT (top closure_of Y) (IMAGE E (annulus r1 r2)) /\
                  X SUBSET U UNION IMAGE E (annulus r1 r2) /\
                  ~DISJOINT X (top closure_of Y)) \/
             (?a b x e E r1 r2.
                 a <= b /\
                 apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
                 (!i. a <= i /\ i <= b
                      ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                 apx_tube (top,atlas) g eps E r1 r2 /\
                 IMAGE E (annulus r1 r2) =
                 apx_chain_union eps {i:int | a <= i /\ i <= b} e /\
                 X SUBSET IMAGE E (annulus r1 r2))`,
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
    MAP_EVERY EXISTS_TAC [`a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`;
                          `r1:real`; `r2:real`] THEN
    ASM_REWRITE_TAC[];
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
                   `Y:A->bool`; `x0:A`] APX21_CASE_I) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> DISJ1_TAC THEN ACCEPT_TAC th)
      (DISJ_CASES_THEN2 (fun th -> DISJ2_TAC THEN DISJ1_TAC THEN ACCEPT_TAC th)
        (fun th -> DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ACCEPT_TAC th)))]);;

(* The headline: MT Prop A.21, unconditional. *)

let APX_A21 = prove
 (`!u:A->bool. APX_A21_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A21_STATEMENT] THEN ACCEPT_TAC APX21_MAIN);;

