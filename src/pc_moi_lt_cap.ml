(* ========================================================================= *)
(* pc_moi_lt_cap: Moise GTM 47, p.185 Case 2, the clean cap of the separate *)
(* case of the disk swap.  Main theorem                                     *)
(*   CLEAN_CAP : |- MOI_LT3_CLEAN_CAP  (pc_moi_loop_stmt3.ml).               *)
(* Route: GP_SIMPLICIAL (lt_gpa) and iterated subdivision make f simplicial  *)
(* k -> t and injective on simplices, fine as in MOI_LCP_FINE.  N is the     *)
(* derived neighbourhood of E1 = f(D1) in t, a 3-cell with frontier sphere   *)
(* F (rnb2).  Pulled back to the source, N gives A UNION B (the derived      *)
(* neighbourhoods of D1 and of j2) and F gives the polygons j1p UNION j2m    *)
(* UNION j2p; the planar facts come from the capped source (moi_fcb_cap,     *)
(* fnd_cap), the polygon theorem of nb2f, the Jordan curve theorem and the   *)
(* Borsuk map.  On F the traces al = f(j1p), bi = f(j2m), bo = f(j2p) are    *)
(* disjoint circles; MOI_LCP_CHOOSE_CAP gives a cap d bounded by bo missing  *)
(* al and bi, or bi and bo on one side of al, which the crossing2 chart and  *)
(* Jordan-Brouwer two-sidedness (MOI_LCP_SEP3) exclude.  j := j2p.           *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt3.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_lt_cova.ml";;
needs "src/pc_moi_lt_nsys.ml";;
needs "src/pc_moi_lt_gpa.ml";;
needs "src/pc_moi_lt_cutc.ml";;
needs "src/pc_moi_lt_charts.ml";;
needs "src/pc_moi_fnd_nb2.ml";;
needs "src/pc_moi_fnd_surfb0.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_fnd_rnb2.ml";;
needs "src/pc_moi_fnd_nb2f.ml";;
needs "src/pc_moi_fnd_cap.ml";;
needs "src/pc_moi_lt_gpc.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* Simplicial maps injective on simplices commute with                       *)
(* barycentric subdivision.  An affine map injective on a simplex keeps its *)
(* vertices affinely independent and its barycentre.                         *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_AFFINE_INDEP_IMAGE = prove
 (`!(f:real^M->real^N) l y V.
     linear l /\ (!x. x IN convex hull V ==> f x = l x + y) /\
     (!x x'. x IN convex hull V /\ x' IN convex hull V /\ f x = f x' ==> x = x') /\
     ~affine_dependent V
     ==> ~affine_dependent (IMAGE f V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `convex hull V:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  DISCH_TAC THEN UNDISCH_TAC `~affine_dependent (V:real^M->bool)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!v:real^M. v IN V ==> (l':real^N->real^M) ((f:real^M->real^N) v) + y' = v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^M) IN convex hull V` ASSUME_TAC THENL
     [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `V = IMAGE (\x:real^M. y' + x) (IMAGE (l':real^N->real^M) (IMAGE (f:real^M->real^N) V))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `z:real^M` THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `(l':real^N->real^M) ((f:real^M->real^N) z)` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `(f:real^M->real^N) z` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `z:real^M` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `w:real^M` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `u:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `v:real^M` STRIP_ASSUME_TAC))))) THEN
      ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[AFFINE_DEPENDENT_TRANSLATION_EQ] THEN
  MATCH_MP_TAC AFFINE_DEPENDENT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `v1:real^M` THEN DISCH_TAC THEN X_GEN_TAC `v2:real^M` THEN DISCH_TAC THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(l':real^N->real^M) ((f:real^M->real^N) v1) + y' =
                l' (f v2) + y'` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]]);;

let MOI_LCP_BARYCENTRE_IMAGE = prove
 (`!(f:real^M->real^N) l y s.
     linear l /\ (!x. x IN s ==> f x = l x + y) /\
     (!x x'. x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
     (?n. n simplex s) /\ ~(s = {})
     ==> f (simplex_barycentre s) = simplex_barycentre (IMAGE f s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (V:real^M->bool) /\ ~(V = {})` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s = convex hull (IMAGE f V)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `V:real^M->bool`]
      MOI_REAL_AFFINE_IMAGE_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `!u. u SUBSET (s:real^M->bool)
                      ==> IMAGE (f:real^M->real^N) u = IMAGE (\x. l x + y) u`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(V:real^M->bool) SUBSET s` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent (IMAGE (f:real^M->real^N) V)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LCP_AFFINE_INDEP_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x x'. x IN V /\ x' IN V /\ (f:real^M->real^N) x = f x' ==> x = x'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (IMAGE (f:real^M->real^N) s) =
                inv (&(CARD (V:real^M->bool))) % vsum V (\v. f v)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[simplex_barycentre] THEN
    ASM_SIMP_TAC[EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `V:real^M->bool`] CARD_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `\v:real^N. v`; `V:real^M->bool`] VSUM_IMAGE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (s:real^M->bool) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) (simplex_barycentre s) = l (simplex_barycentre s) + y`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `s:real^M->bool`]
    MOI_FRN_AFFINE_BARYCENTRE) THEN
  SUBGOAL_THEN `{v | v extreme_point_of (s:real^M->bool)} = V` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[] THEN X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[HULL_INC]);;

let MOI_LCP_AFFINE_EQ_HULL = prove
 (`!(l1:real^M->real^N) y1 l2 y2 S.
     linear l1 /\ linear l2 /\ (!x. x IN S ==> l1 x + y1 = l2 x + y2)
     ==> !x. x IN convex hull S ==> l1 x + y1 = l2 x + y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull S SUBSET {x:real^M | (l1:real^M->real^N) x + y1 = l2 x + y2}`
  (fun th -> REWRITE_TAC[REWRITE_RULE[SUBSET; IN_ELIM_THM] th]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[convex; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `u:real`; `v:real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  SUBGOAL_THEN `v = &1 - u` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `u % ((l1:real^M->real^N) a + y1) + (&1 - u) % (l1 b + y1)` THEN
  CONJ_TAC THENL [VECTOR_ARITH_TAC; ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

(* A simplicial map injective on simplices stays simplicial and injective   *)
(* on simplices after barycentric subdivision of source and target.         *)

let MOI_LCP_SD_INJ = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x')
     ==> simplicial_map_on (barycentric_subdivision k) (barycentric_subdivision c) f /\
         (!s x x'. s IN barycentric_subdivision k /\ x IN s /\ x' IN s /\ f x = f x'
                   ==> x = x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
    MOI_LNS_SD_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_complex (k:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  (* on a nonempty chain hull, f agrees with h *)
  SUBGOAL_THEN
   `!q. moi_bar_chain k q /\ ~(q = {})
        ==> UNIONS q IN k /\ convex hull (IMAGE simplex_barycentre q) SUBSET UNIONS q /\
            !x. x IN convex hull (IMAGE simplex_barycentre q)
                ==> (f:real^M->real^N) x = h x`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:(real^M->bool)->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `q:(real^M->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `UNIONS q IN (k:(real^M->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `q:(real^M->bool)->bool`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `UNIONS q:real^M->bool` (REWRITE_RULE[simplicial_map_on]
      (ASSUME `simplicial_map_on k (c:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:real^M->real^N` (X_CHOOSE_THEN `y0:real^N`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre q) IN
                  barycentric_subdivision (k:(real^M->bool)->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `q:(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `convex hull (IMAGE simplex_barycentre q):real^M->bool`
      (REWRITE_RULE[simplicial_map_on]
       (ASSUME `simplicial_map_on (barycentric_subdivision k)
                  (barycentric_subdivision (c:(real^N->bool)->bool)) (h:real^M->real^N)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:real^M->real^N` (X_CHOOSE_THEN `y1:real^N`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS q` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`l0:real^M->real^N`; `y0:real^N`; `l1:real^M->real^N`; `y1:real^N`;
                   `IMAGE simplex_barycentre (q:(real^M->bool)->bool)`]
      MOI_LCP_AFFINE_EQ_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `r:real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `simplex_barycentre (r:real^M->bool) IN
                    convex hull (IMAGE simplex_barycentre q)` ASSUME_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `simplex_barycentre (r:real^M->bool) IN UNIONS q` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(r:real^M->bool) IN k /\ ~(r = {})` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^M->real^N) (simplex_barycentre r) = h (simplex_barycentre r)`
      MP_TAC THENL
       [MP_TAC(ISPECL [`f:real^M->real^N`; `l0:real^M->real^N`; `y0:real^N`;
                       `r:real^M->bool`] MOI_LCP_BARYCENTRE_IMAGE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM SET_TAC[];
            ASM_MESON_TAC[];
            ASM_MESON_TAC[simplicial_complex]];
          DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^M->real^N) (simplex_barycentre r) =
                    l0 (simplex_barycentre r) + y0 /\
                    (h:real^M->real^N) (simplex_barycentre r) =
                    l1 (simplex_barycentre r) + y1`
      (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplicial_map_on; MOI_BAR_IN_SUBDIVISION] THEN
    X_GEN_TAC `t:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)) THEN
    ASM_CASES_TAC `q:(real^M->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN CONJ_TAC THENL
       [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
        REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; moi_bar_chain; EMPTY_SUBSET;
                    FINITE_EMPTY; NOT_IN_EMPTY];
        MESON_TAC[LINEAR_ZERO]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (f:real^M->real^N) (convex hull (IMAGE simplex_barycentre q)) =
                    IMAGE h (convex hull (IMAGE simplex_barycentre q))` SUBST1_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `convex hull (IMAGE simplex_barycentre q):real^M->bool`
        (REWRITE_RULE[simplicial_map_on]
         (ASSUME `simplicial_map_on (barycentric_subdivision k)
                    (barycentric_subdivision (c:(real^N->bool)->bool)) (h:real^M->real^N)`))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `q:(real^M->bool)->bool` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN SIMP_TAC[]];
      MP_TAC(ISPEC `UNIONS q:real^M->bool` (REWRITE_RULE[simplicial_map_on]
        (ASSUME `simplicial_map_on k (c:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `l0:real^M->real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `y0:real^N` THEN ASM SET_TAC[]];
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `x:real^M`; `x':real^M`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:(real^M->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `q:(real^M->bool)->bool = {}` THENL
     [UNDISCH_TAC `(x:real^M) IN t` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `UNIONS q:real^M->bool` THEN ASM SET_TAC[]]);;

(* The image of the subdivision is the subdivision of the image complex.    *)

let MOI_LCP_CHAIN_HULL_IMAGE = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f q.
     simplicial_complex k /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
     moi_bar_chain k q /\ ~(q = {})
     ==> moi_bar_chain c (IMAGE (IMAGE f) q) /\
         IMAGE f (convex hull (IMAGE simplex_barycentre q)) =
         convex hull (IMAGE simplex_barycentre (IMAGE (IMAGE f) q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (k:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `q:(real^M->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS q IN (k:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `q:(real^M->bool)->bool`]
    MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `UNIONS q:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on k (c:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:real^M->real^N` (X_CHOOSE_THEN `y0:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MATCH_MP_TAC MOI_LNS_CHAIN_IMAGE THEN EXISTS_TAC `k:(real^M->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`l0:real^M->real^N`; `y0:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `r:real^M->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(r:real^M->bool) IN k /\ ~(r = {}) /\ r SUBSET UNIONS q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LCP_BARYCENTRE_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`l0:real^M->real^N`; `y0:real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[simplicial_complex]]);;

let MOI_LCP_SD_IMAGE = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x')
     ==> IMAGE (IMAGE f) (barycentric_subdivision k) =
         barycentric_subdivision (IMAGE (IMAGE f) k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_map_on k (IMAGE (IMAGE (f:real^M->real^N)) k) f` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_map_on k (c:(real^N->bool)->bool) (f:real^M->real^N)` THEN
    REWRITE_TAC[simplicial_map_on] THEN MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (IMAGE (IMAGE (f:real^M->real^N)) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
      MOI_LNS_IMAGE_COMPLEX) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_BAR_IN_SUBDIVISION] THEN
    X_GEN_TAC `t:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)) THEN
    ASM_CASES_TAC `q:(real^M->bool)->bool = {}` THENL
     [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; moi_bar_chain; EMPTY_SUBSET;
                      FINITE_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) q` THEN
    MATCH_MP_TAC MOI_LCP_CHAIN_HULL_IMAGE THEN EXISTS_TAC `k:(real^M->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; MOI_BAR_IN_SUBDIVISION; IN_IMAGE] THEN
  X_GEN_TAC `u:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST1_TAC)) THEN
  ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THENL
   [EXISTS_TAC `{}:real^M->bool` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN
    EXISTS_TAC `{}:(real^M->bool)->bool` THEN
    REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; moi_bar_chain; EMPTY_SUBSET;
                FINITE_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (f:real^M->real^N)) k`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^M->bool. s IN k /\ UNIONS g = IMAGE (f:real^M->real^N) s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (IMAGE (IMAGE (f:real^M->real^N)) k) g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on k (c:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `f:real^M->real^N`; `s:real^M->bool`;
                 `g:(real^N->bool)->bool`] MOI_LNS_LIFT_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain (IMAGE (IMAGE (f:real^M->real^N)) k) g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `UNIONS g:real^N->bool`)) THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) k` THEN ASM_SIMP_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre q):real^M->bool` THEN
  SUBGOAL_THEN `~(q:(real^M->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(g:(real^N->bool)->bool = {})` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `g:(real^N->bool)->bool`)) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`;
                   `q:(real^M->bool)->bool`] MOI_LCP_CHAIN_HULL_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `q:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Pulling derived neighbourhoods back along a simplicial map               *)
(* injective on simplices.  X = the image complex, L a subcomplex of X,     *)
(* K_L = the simplices of k mapping into L.  The preimage of |L| is |K_L|;  *)
(* where the points of derived_nbhd X L outside |L| have unique preimages,  *)
(* the preimage of the derived neighbourhood is derived_nbhd k K_L.         *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_SD2 = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x')
     ==> simplicial_complex (barycentric_subdivision (barycentric_subdivision k)) /\
         simplicial_map_on (barycentric_subdivision (barycentric_subdivision k))
                           (barycentric_subdivision (barycentric_subdivision c)) f /\
         (!s x x'. s IN barycentric_subdivision (barycentric_subdivision k) /\
                   x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
         IMAGE (IMAGE f) (barycentric_subdivision (barycentric_subdivision k)) =
         barycentric_subdivision (barycentric_subdivision (IMAGE (IMAGE f) k)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision k)) = UNIONS k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
    MOI_LCP_SD_INJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision (k:(real^M->bool)->bool)) /\
                lf_simplicial_complex (barycentric_subdivision (c:(real^N->bool)->bool))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (k:(real^M->bool)->bool)`;
                 `barycentric_subdivision (c:(real^N->bool)->bool)`; `f:real^M->real^N`]
    MOI_LCP_SD_INJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX];
    MP_TAC(ISPECL [`barycentric_subdivision (k:(real^M->bool)->bool)`;
                   `barycentric_subdivision (c:(real^N->bool)->bool)`; `f:real^M->real^N`]
      MOI_LCP_SD_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOI_LCP_SD_IMAGE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION; MOI_FMB_SC_LF;
                 BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX]]);;

(* The preimage of |L| is |K_L|.                                            *)

let MOI_LCP_PREIMAGE_SUBCOMPLEX = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f L.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
     simplicial_subcomplex L (IMAGE (IMAGE f) k)
     ==> {x | x IN UNIONS k /\ f x IN UNIONS L} =
         UNIONS {s | s IN k /\ IMAGE f s IN L}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (IMAGE (IMAGE (f:real^M->real^N)) k) /\
                lf_simplicial_complex (k:(real^M->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
      MOI_LNS_IMAGE_COMPLEX) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN X_GEN_TAC `x:real^M` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s0:real^M->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `lam:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s0:real^M->bool`; `x:real^M`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(sg:real^M->bool) IN k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s0:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `sg:real^M->bool` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `sg:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on k (c:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  SUBGOAL_THEN `(f:real^M->real^N) x IN relative_interior (IMAGE f sg)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `sg:real^M->bool`]
      MOI_LCA_AFFINE_RELINT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) sg IN IMAGE (IMAGE f) k /\
                lam IN IMAGE (IMAGE (f:real^M->real^N)) k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_MESON_TAC[simplicial_subcomplex; SUBSET]];
    ALL_TAC] THEN
  UNDISCH_TAC `simplicial_subcomplex L (IMAGE (IMAGE (f:real^M->real^N)) k)` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `lam:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
  EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) k` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (IMAGE (f:real^M->real^N)) k`; `(f:real^M->real^N) x`] THEN
  ASM_REWRITE_TAC[]);;

(* The derived neighbourhood pulls back where its points off |L| have one   *)
(* preimage.                                                                 *)

let MOI_LCP_NBHD_PULLBACK = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f L.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
     simplicial_subcomplex L (IMAGE (IMAGE f) k) /\
     (!x x'. x IN UNIONS k /\ x' IN UNIONS k /\ f x = f x' /\
             f x IN derived_nbhd (IMAGE (IMAGE f) k) L /\ ~(f x IN UNIONS L)
             ==> x = x')
     ==> {x | x IN UNIONS k /\ f x IN derived_nbhd (IMAGE (IMAGE f) k) L} =
         derived_nbhd k {s | s IN k /\ IMAGE f s IN L}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
    MOI_LCP_SD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`;
                 `L:(real^N->bool)->bool`] MOI_LCP_PREIMAGE_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `KL = {s:real^M->bool | s IN k /\ IMAGE (f:real^M->real^N) s IN L}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x:real^M. x IN UNIONS k /\ (f:real^M->real^N) x IN UNIONS L <=>
                           x IN UNIONS KL` ASSUME_TAC THENL
   [UNDISCH_TAC `{x:real^M | x IN UNIONS k /\ (f:real^M->real^N) x IN UNIONS L} =
                 UNIONS KL` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[derived_nbhd] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(s:real^N->bool) IN
                 barycentric_subdivision (barycentric_subdivision
                   (IMAGE (IMAGE (f:real^M->real^N)) k))` THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) o
      check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `IMAGE (IMAGE (f:real^M->real^N))`)) (lhs(concl th)))) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^M->bool` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      ASSUME_TAC)) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(f:real^M->real^N) x IN UNIONS L` THENL
     [SUBGOAL_THEN `(x:real^M) IN UNIONS KL` ASSUME_TAC THENL
        [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?tau0:real^M->bool.
                      tau0 IN barycentric_subdivision (barycentric_subdivision k) /\
                      x IN tau0`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^M) IN UNIONS k` THEN
        UNDISCH_TAC `UNIONS (barycentric_subdivision (barycentric_subdivision k)) =
                     UNIONS (k:(real^M->bool)->bool)` THEN SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `tau0:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^M` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `tau:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(tau:real^M->bool) SUBSET UNIONS k` ASSUME_TAC THENL
     [UNDISCH_TAC `(tau:real^M->bool) IN barycentric_subdivision (barycentric_subdivision k)` THEN
      UNDISCH_TAC `UNIONS (barycentric_subdivision (barycentric_subdivision k)) =
                   UNIONS (k:(real^M->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~(IMAGE (f:real^M->real^N) tau INTER UNIONS L = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?w:real^M. w IN tau /\ (f:real^M->real^N) w = z` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^N) IN IMAGE (f:real^M->real^N) tau` THEN
        REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `w:real^M` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(w:real^M) IN UNIONS k /\ (f:real^M->real^N) w IN UNIONS L` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `?x':real^M. x' IN tau /\ (f:real^M->real^N) x' = f x`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(f:real^M->real^N) x IN IMAGE f tau` THEN REWRITE_TAC[IN_IMAGE] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `x':real^M = x` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `derived_nbhd:((real^N->bool)->bool)->((real^N->bool)->bool)->real^N->bool`))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `IMAGE (f:real^M->real^N) tau` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
        check (fun th -> is_eq(concl th) &&
          can (find_term ((=) `IMAGE (IMAGE (f:real^M->real^N))`)) (lhs(concl th)))) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^M->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(tau:real^M->bool) IN barycentric_subdivision (barycentric_subdivision k)` THEN
      UNDISCH_TAC `UNIONS (barycentric_subdivision (barycentric_subdivision k)) =
                   UNIONS (k:(real^M->bool)->bool)` THEN
      UNDISCH_TAC `(x:real^M) IN tau` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) tau` THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
          check (fun th -> is_eq(concl th) &&
            can (find_term ((=) `IMAGE (IMAGE (f:real^M->real^N))`)) (lhs(concl th)))) THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE];
        UNDISCH_TAC `~((tau:real^M->bool) INTER UNIONS KL = {})` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `(f:real^M->real^N) w` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_MESON_TAC[]]];
      ASM_SIMP_TAC[FUN_IN_IMAGE]]]);;


(* ------------------------------------------------------------------------- *)
(* Iterated subdivision of a simplicial map injective on                    *)
(* simplices; a locally injective map that is affine on the simplices of a  *)
(* triangulation is injective on them, and two simplices with the same      *)
(* image that meet are equal.                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_ITER_SD = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x')
     ==> !n. simplicial_complex (ITER n barycentric_subdivision k) /\
             lf_simplicial_complex (ITER n barycentric_subdivision c) /\
             simplicial_map_on (ITER n barycentric_subdivision k)
                               (ITER n barycentric_subdivision c) f /\
             (!s x x'. s IN ITER n barycentric_subdivision k /\ x IN s /\ x' IN s /\
                       f x = f x' ==> x = x') /\
             IMAGE (IMAGE f) (ITER n barycentric_subdivision k) =
             ITER n barycentric_subdivision (IMAGE (IMAGE f) k) /\
             UNIONS (ITER n barycentric_subdivision k) = UNIONS k /\
             UNIONS (ITER n barycentric_subdivision c) = UNIONS c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (k:(real^M->bool)->bool)`;
                 `ITER n barycentric_subdivision (c:(real^N->bool)->bool)`;
                 `f:real^M->real^N`] MOI_LCP_SD_INJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX];
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
    MP_TAC(ISPECL [`ITER n barycentric_subdivision (k:(real^M->bool)->bool)`;
                   `ITER n barycentric_subdivision (c:(real^N->bool)->bool)`;
                   `f:real^M->real^N`] MOI_LCP_SD_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION; MOI_FMB_SC_LF];
    ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION]]);;

(* Local injectivity plus affineness on a convex set: injective on it.     *)

let MOI_LCP_LOCAL_INJ_CONVEX = prove
 (`!(f:real^M->real^N) l y s u.
     linear l /\ convex s /\ s SUBSET u /\ (!x. x IN s ==> f x = l x + y) /\
     (!x. x IN u ==> ?n. open n /\ x IN n /\
                         !a b. a IN n INTER u /\ b IN n INTER u /\ f a = f b ==> a = b)
     ==> !x x'. x IN s /\ x' IN s /\ f x = f x' ==> x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:real^M->bool`] OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`norm(x' - x:real^M)`; `norm(x' - x:real^M)`; `e:real`] MOI_LCA_SMALL_T) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&1 - t) % x + t % x':real^M IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(s:real^M->bool)`)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) % x + t % x':real^M = x` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `(s:real^M->bool) SUBSET u` THEN
        UNDISCH_TAC `(&1 - t) % x + t % x':real^M IN s` THEN SET_TAC[]] THEN
      UNDISCH_TAC `ball(x:real^M,e) SUBSET n` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[dist; VECTOR_ARITH `x - ((&1 - t) % x + t % x'):real^M = t % (x - x')`;
                  NORM_MUL] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
      REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(s:real^M->bool) SUBSET u` THEN
      UNDISCH_TAC `(x:real^M) IN s` THEN SET_TAC[];
      MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `s:real^M->bool`;
                     `x:real^M`; `x':real^M`; `t:real`] MOI_LCA_AFFINE_COMB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `t % (x' - x):real^M = vec 0` MP_TAC THENL
     [UNDISCH_TAC `(&1 - t) % x + t % x':real^M = x` THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ]]]);;

(* Two convex pieces on which f is affine, meeting at z, with f injective   *)
(* near z: points with the same image are equal (as MOI_LCA_SEGMENT).       *)

let MOI_LCP_SEGMENT = prove
 (`!(f:real^M->real^N) u L1 L2 l1 y1 l2 y2 z p p2 e.
     L1 SUBSET u /\ L2 SUBSET u /\ convex L1 /\ convex L2 /\
     linear l1 /\ (!x. x IN L1 ==> f x = l1 x + y1) /\
     linear l2 /\ (!x. x IN L2 ==> f x = l2 x + y2) /\
     z IN L1 /\ z IN L2 /\ p IN L1 /\ p2 IN L2 /\ f p = f p2 /\ &0 < e /\
     (!x y. x IN u /\ y IN u /\ dist(z,x) < e /\ dist(z,y) < e /\ f x = f y ==> x = y)
     ==> p = p2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "inj"))))))))))))))) THEN
  MP_TAC(ISPECL [`norm(p - z:real^M)`; `norm(p2 - z:real^M)`; `e:real`] MOI_LCA_SMALL_T) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&1 - t) % z + t % p:real^M IN L1 /\ (&1 - t) % z + t % p2:real^M IN L2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(L1:real^M->bool)`));
      MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(L2:real^M->bool)`))] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) ((&1 - t) % z + t % p) = (&1 - t) % f z + t % f p /\
                f ((&1 - t) % z + t % p2) = (&1 - t) % f z + t % f p2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LCA_AFFINE_COMB THENL
     [MAP_EVERY EXISTS_TAC [`l1:real^M->real^N`; `y1:real^N`; `L1:real^M->bool`];
      MAP_EVERY EXISTS_TAC [`l2:real^M->real^N`; `y2:real^N`; `L2:real^M->bool`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) % z + t % p:real^M = (&1 - t) % z + t % p2` MP_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(L1:real^M->bool) SUBSET u` THEN
      UNDISCH_TAC `(&1 - t) % z + t % p:real^M IN L1` THEN SET_TAC[];
      UNDISCH_TAC `(L2:real^M->bool) SUBSET u` THEN
      UNDISCH_TAC `(&1 - t) % z + t % p2:real^M IN L2` THEN SET_TAC[];
      REWRITE_TAC[dist; VECTOR_ARITH `z - ((&1 - t) % z + t % p):real^M = t % (z - p)`;
                  NORM_MUL] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
      REWRITE_TAC[dist; VECTOR_ARITH `z - ((&1 - t) % z + t % p):real^M = t % (z - p)`;
                  NORM_MUL] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`]];
    DISCH_TAC THEN
    SUBGOAL_THEN `t % (p - p2):real^M = vec 0` MP_TAC THENL
     [UNDISCH_TAC `(&1 - t) % z + t % p:real^M = (&1 - t) % z + t % p2` THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ]]]);;


(* ------------------------------------------------------------------------- *)
(* The double-point structure of a locally injective map that               *)
(* is simplicial on a triangulation K of std_triangle.  Simplices with the  *)
(* same image are equal or disjoint; the double image and its preimage are  *)
(* unions of simplices.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_LOCAL_BALL = prove
 (`!(f:real^M->real^N) u z.
     (!x. x IN u ==> ?n. open n /\ x IN n /\
                         !a b. a IN n INTER u /\ b IN n INTER u /\ f a = f b ==> a = b) /\
     z IN u
     ==> ?e. &0 < e /\
             !x y. x IN u /\ y IN u /\ dist(z,x) < e /\ dist(z,y) < e /\ f x = f y
                   ==> x = y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `n:real^M->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ball(z:real^M,e) SUBSET n` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  ASM_MESON_TAC[]);;

(* Simplices of K with the same image that meet are equal.                  *)

let MOI_LCP_PAIR_EQ = prove
 (`!(K:(real^M->bool)->bool) (t:(real^N->bool)->bool) f u s1 s2.
     simplicial_complex K /\ UNIONS K SUBSET u /\ simplicial_map_on K t f /\
     (!x. x IN u ==> ?n. open n /\ x IN n /\
                         !a b. a IN n INTER u /\ b IN n INTER u /\ f a = f b ==> a = b) /\
     s1 IN K /\ s2 IN K /\ IMAGE f s1 = IMAGE f s2 /\ ~DISJOINT s1 s2
     ==> s1 = s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!A B:real^M->bool. A IN K /\ B IN K /\ IMAGE (f:real^M->real^N) A = IMAGE f B /\
                       ~DISJOINT A B ==> A SUBSET B`
  (fun th -> MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN MATCH_MP_TAC th THEN
             ASM_REWRITE_TAC[] THEN ASM SET_TAC[]) THEN
  MAP_EVERY X_GEN_TAC [`A:real^M->bool`; `B:real^M->bool`] THEN STRIP_TAC THEN
  UNDISCH_TAC `~DISJOINT (A:real^M->bool) B` THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `u:real^M->bool`; `z:real^M`] MOI_LCP_LOCAL_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p2:real^M. p2 IN B /\ (f:real^M->real^N) p = f p2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^M->real^N) A = IMAGE f B` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) p`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `A:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on K (t:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lA:real^M->real^N` (X_CHOOSE_THEN `yA:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MP_TAC(ISPEC `B:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on K (t:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lB:real^M->real^N` (X_CHOOSE_THEN `yB:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  SUBGOAL_THEN `(A:real^M->bool) SUBSET u /\ B SUBSET u /\ convex A /\ convex B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ASM_MESON_TAC[MOI_FM3_LF_CONVEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p:real^M = p2` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_LCP_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `u:real^M->bool`; `A:real^M->bool`;
    `B:real^M->bool`; `lA:real^M->real^N`; `yA:real^N`; `lB:real^M->real^N`; `yB:real^N`;
    `z:real^M`; `e:real`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LCP_CARRIER = prove
 (`!(K:(real^M->bool)->bool) x.
     lf_simplicial_complex K /\ x IN UNIONS K
     ==> ?s. s IN K /\ x IN relative_interior s`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `(x:real^M) IN UNIONS K` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t0:real^M->bool`; `x:real^M`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^M->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_FACE THEN
  EXISTS_TAC `t0:real^M->bool` THEN ASM_REWRITE_TAC[]);;

(* A simplicial map injective on simplices, with the image complex lf: two  *)
(* points with the same image have carriers with the same image.            *)

let MOI_LCP_CARRIER_IMAGE = prove
 (`!(K:(real^M->bool)->bool) (t:(real^N->bool)->bool) f s s' x x'.
     simplicial_complex K /\ lf_simplicial_complex t /\ simplicial_map_on K t f /\
     s IN K /\ s' IN K /\ x IN relative_interior s /\ x' IN relative_interior s' /\
     f x = f x'
     ==> IMAGE f s = IMAGE f s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (IMAGE (IMAGE (f:real^M->real^N)) K) /\
                lf_simplicial_complex (K:(real^M->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`K:(real^M->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^M->real^N`]
      MOI_LNS_IMAGE_COMPLEX) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r z:real^M. r IN K /\ z IN relative_interior r
                 ==> (f:real^M->real^N) z IN relative_interior (IMAGE f r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `r:real^M->bool` (REWRITE_RULE[simplicial_map_on]
      (ASSUME `simplicial_map_on K (t:(real^N->bool)->bool) (f:real^M->real^N)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `r:real^M->bool`]
      MOI_LCA_AFFINE_RELINT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) x IN relative_interior (IMAGE f s) /\
                f x IN relative_interior (IMAGE f s') /\
                IMAGE f s IN IMAGE (IMAGE f) K /\ IMAGE f s' IN IMAGE (IMAGE f) K`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (IMAGE (f:real^M->real^N)) K`; `(f:real^M->real^N) x`] THEN
  ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]);;

(* Abbreviation-free hypotheses H: K triangulates the triangle, f simplicial *)
(* into t and locally injective on the triangle.                            *)

let MOI_LCP_CARRIER_PAIRED = prove
 (`!(K:(real^2->bool)->bool) (t:(real^N->bool)->bool) f s x.
     simplicial_complex K /\ UNIONS K = std_triangle /\ lf_simplicial_complex t /\
     simplicial_map_on K t f /\
     (!x. x IN std_triangle
          ==> ?n. open n /\ x IN n /\
                  !a b. a IN n INTER std_triangle /\ b IN n INTER std_triangle /\
                        f a = f b ==> a = b) /\
     s IN K /\ x IN relative_interior s /\ f x IN moi_lt_double_image f
     ==> ?s'. s' IN K /\ ~(s' = s) /\ IMAGE f s' = IMAGE f s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN s /\ x IN std_triangle` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; IN_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `?x':real^2. x' IN std_triangle /\ ~(x' = x) /\
                            (f:real^2->real^N) x' = f x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^2->real^N) x IN moi_lt_double_image f` THEN
    REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `x':real^2`] MOI_LCP_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s':real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(x':real^2 = x)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^2->bool` (REWRITE_RULE[simplicial_map_on]
      (ASSUME `simplicial_map_on K (t:(real^N->bool)->bool) (f:real^2->real^N)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    MP_TAC(ISPECL [`f:real^2->real^N`; `l:real^2->real^N`; `y:real^N`; `s:real^2->bool`;
                   `std_triangle`] MOI_LCP_LOCAL_INJ_CONVEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ASM SET_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `(x':real^2) IN s` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `s':real^2->bool = s` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    MATCH_MP_TAC MOI_LCP_CARRIER_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`;
                          `x':real^2`; `x:real^2`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LCP_DOUBLE_SIMPLICES = prove
 (`!(K:(real^2->bool)->bool) (t:(real^N->bool)->bool) f.
     simplicial_complex K /\ UNIONS K = std_triangle /\ lf_simplicial_complex t /\
     simplicial_map_on K t f /\
     (!x. x IN std_triangle
          ==> ?n. open n /\ x IN n /\
                  !a b. a IN n INTER std_triangle /\ b IN n INTER std_triangle /\
                        f a = f b ==> a = b)
     ==> {x | x IN std_triangle /\ f x IN moi_lt_double_image f} =
         UNIONS {s | s IN K /\ ?s'. s' IN K /\ ~(s' = s) /\ IMAGE f s' = IMAGE f s} /\
         moi_lt_double_image f =
         UNIONS {IMAGE f s | s | s IN K /\ ?s'. s' IN K /\ ~(s' = s) /\ IMAGE f s' = IMAGE f s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f} =
    UNIONS {s | s IN K /\ ?s'. s' IN K /\ ~(s' = s) /\ IMAGE f s' = IMAGE f s}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `x:real^2`] MOI_LCP_CARRIER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`;
                             `f:real^2->real^N`; `s:real^2->bool`; `x:real^2`]
                      MOI_LCP_CARRIER_PAIRED) THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^2`; `s:real^2->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `s':real^2->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?x':real^2. x' IN s' /\ (f:real^2->real^N) x' = f x`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~(s':real^2->bool = s)` THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`;
                             `f:real^2->real^N`; `std_triangle`] MOI_LCP_PAIR_EQ) THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^2. x IN std_triangle /\ (f:real^2->real^N) x = y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN moi_lt_double_image f` THEN
      REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN UNIONS {s | s IN K /\ ?s'. s' IN K /\ ~(s' = s) /\
                                         IMAGE (f:real^2->real^N) s' = IMAGE f s}`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `moi_lt_double_image (f:real^2->real^N)`)) (lhs(concl th)))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (f:real^2->real^N) s` THEN CONJ_TAC THENL
     [EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[FUN_IN_IMAGE]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^2->bool` THEN
    STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN UNIONS {s | s IN K /\ ?s'. s' IN K /\ ~(s' = s) /\
                                         IMAGE (f:real^2->real^N) s' = IMAGE f s}`
    MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `moi_lt_double_image (f:real^2->real^N)`)) (lhs(concl th)))) THEN
      SIMP_TAC[IN_ELIM_THM]]]);;


(* ------------------------------------------------------------------------- *)
(* Step S1: the simplicial setting.  GP_SIMPLICIAL gives t0, K0 with         *)
(* f simplicial; t0 is a combinatorial 3-manifold with the boundary of c    *)
(* (PL invariance under the identity); iterated barycentric subdivision of  *)
(* both makes all simplices small, keeping f simplicial and injective on    *)
(* simplices.                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_PLH_ID = prove
 (`!s:real^N->bool. pl_polyhedron s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_LCP_LF_POLYHEDRON = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c ==> pl_polyhedron (UNIONS c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_MESON_TAC[MOI_FM3_LF_POLYTOPE]);;

let MOI_LCP_LF_SC = prove
 (`!c:(real^N->bool)->bool. FINITE c /\ lf_simplicial_complex c ==> simplicial_complex c`,
  REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN MESON_TAC[]);;

let MOI_LCP_MESH_SD = prove
 (`!(c:(real^N->bool)->bool) e.
     lf_simplicial_complex c /\ &0 < e /\ (!s. s IN c ==> diameter s < e)
     ==> !n. lf_simplicial_complex (ITER n barycentric_subdivision c) /\
             !s. s IN ITER n barycentric_subdivision c ==> diameter s < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL [ASM_REWRITE_TAC[DIAMETER_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPEC `ITER n barycentric_subdivision (c:(real^N->bool)->bool)`
    BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `diameter(u:real^N->bool)` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC DIAMETER_SUBSET THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_BOUNDED]);;

let MOI_LCP_ITER_ADD = prove
 (`!(g:A->A) m n x. ITER (m + n) g x = ITER m g (ITER n g x)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; ADD_CLAUSES]);;

let MOI_LCP_S1 = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lt_singular_disk c f /\
     &0 < e
     ==> ?t K. FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
               UNIONS t = UNIONS c /\ complex_boundary t = complex_boundary c /\
               simplicial_complex K /\ UNIONS K = std_triangle /\
               simplicial_map_on K t f /\
               (!s x x'. s IN K /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
               (!s. s IN t ==> diameter s < e) /\ (!s. s IN K ==> diameter s < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`] GP_SIMPLICIAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(real^N->bool)->bool` (X_CHOOSE_THEN
    `K0:(real^2->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `UNIONS t0 = UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[subdivides]; ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (t0:(real^N->bool)->bool) /\
                complex_boundary t0 = complex_boundary c` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t0:(real^N->bool)->bool`;
                   `\x:real^N. x`; `\x:real^N. x`] MOI_FMB_PL_INVARIANT_LF) THEN
    ASM_REWRITE_TAC[IMAGE_ID] THEN ANTS_TAC THENL
     [MATCH_MP_TAC MOI_LCP_PLH_ID THEN MATCH_MP_TAC MOI_LCP_LF_POLYHEDRON THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s x x'. s IN K0 /\ x IN s /\ x' IN s /\ (f:real^2->real^N) x = f x'
                         ==> x = x'` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `s:real^2->bool` (REWRITE_RULE[simplicial_map_on]
      (ASSUME `simplicial_map_on K0 (t0:(real^N->bool)->bool) (f:real^2->real^N)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    MP_TAC(ISPECL [`f:real^2->real^N`; `l:real^2->real^N`; `y:real^N`; `s:real^2->bool`;
                   `std_triangle`] MOI_LCP_LOCAL_INJ_CONVEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FMB_SC_LF];
        ASM SET_TAC[];
        UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) f` THEN
        REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:(real^2->bool)->bool`; `t0:(real^N->bool)->bool`; `f:real^2->real^N`]
    MOI_LCP_ITER_SD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_SIMP_TAC[MOI_LCP_LF_SC] THEN DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
  MP_TAC(ISPECL [`K0:(real^2->bool)->bool`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n2:num`) THEN
  MAP_EVERY EXISTS_TAC
   [`ITER (n2 + n1) barycentric_subdivision (t0:(real^N->bool)->bool)`;
    `ITER (n2 + n1) barycentric_subdivision (K0:(real^2->bool)->bool)`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n2 + n1:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n2 + n1:num`; `t0:(real^N->bool)->bool`]
    (MATCH_MP MOI_LTD_ITER_SD COMBINATORIAL_WB_BARYCENTRIC)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_LCP_ITER_ADD] THEN
    MP_TAC(ISPECL [`ITER n1 barycentric_subdivision (t0:(real^N->bool)->bool)`; `e:real`]
      MOI_LCP_MESH_SD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOI_LCP_ITER_ADD] THEN
    MP_TAC(ISPECL [`ITER n2 barycentric_subdivision (K0:(real^2->bool)->bool)`; `e:real`]
      MOI_LCP_MESH_SD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FMB_SC_LF]; MESON_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* The common facts.  f maps j1 and j2 bijectively onto k                   *)
(* (a clopen nonempty image in the connected component k: local preimages, *)
(* MOI_LCC_LOCAL_PREIMAGE; at most two preimages, MOI_LCC_FIBER_TWO); f is  *)
(* injective on D1 = j1 UNION inside j1; the preimage of E1 = f(D1) is      *)
(* D1 UNION j2; E1 meets the double image in k and misses the boundary.     *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_IMAGE_COMPONENT = prove
 (`!c (f:real^2->real^N) k j j'.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     {x | x IN std_triangle /\ f x IN k} = j UNION j' /\ DISJOINT j j' /\
     compact j /\ compact j' /\ ~(j = {})
     ==> IMAGE f j = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_singular_disk; PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f /\ connected k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^2->bool) SUBSET std_triangle /\ IMAGE (f:real^2->real^N) j SUBSET k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = j UNION j'` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^2->real^N) j`) THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ (c ==> d) /\ ~e ==> (a /\ b ==> e \/ c) ==> d`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?r. &0 < r /\ !x:real^2. x IN j' ==> r <= dist(x0,x)` STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `j':real^2->bool = {}` THENL
       [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
      MP_TAC(ISPECL [`{x0:real^2}`; `j':real^2->bool`] SEPARATE_COMPACT_CLOSED) THEN
      ASM_SIMP_TAC[COMPACT_SING; COMPACT_IMP_CLOSED] THEN ANTS_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_SING] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `x0:real^2`; `r:real`]
      MOI_LCC_LOCAL_PREIMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^2) IN j UNION j'` MP_TAC THENL
     [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
        check (fun th -> is_eq(concl th) && rand(concl th) = `j UNION j':real^2->bool`)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[REAL_NOT_LE]];
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    SIMP_TAC[];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]]);;

let MOI_LCP_CASE2_BIJ = prove
 (`!c (f:real^2->real^N) k j1 j2.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\ DISJOINT j1 j2 /\
     compact j1 /\ compact j2 /\ ~(j1 = {}) /\ ~(j2 = {})
     ==> IMAGE f j1 = k /\ IMAGE f j2 = k /\
         (!x y. x IN j1 /\ y IN j1 /\ f x = f y ==> x = y) /\
         (!x y. x IN j2 /\ y IN j2 /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) j1 = k /\ IMAGE f j2 = k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LCP_IMAGE_COMPONENT THENL
     [MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `j2:real^2->bool`];
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `j1:real^2->bool`]] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j j':real^2->bool. j UNION j' = j1 UNION j2 /\ DISJOINT j j' /\
                        IMAGE (f:real^2->real^N) j' = k
                        ==> !x y. x IN j /\ y IN j /\ f x = f y ==> x = y`
  (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THENL
     [EXISTS_TAC `j2:real^2->bool`; EXISTS_TAC `j1:real^2->bool`] THEN
   ASM_REWRITE_TAC[] THEN ASM SET_TAC[]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle /\ y IN std_triangle /\
                (f:real^2->real^N) x IN k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = j1 UNION j2` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^2. z IN j' /\ (f:real^2->real^N) z = f x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN std_triangle` ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = j1 UNION j2` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `x:real^2`]
    MOI_LCC_FIBER_TWO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `y:real^2 = v' /\ z = v'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2`) THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ASM SET_TAC[]]);;

(* The facts about D1 = j1 UNION inside j1 and E1 = f(D1).                   *)

let MOI_LCP_D1_FACTS = prove
 (`!c (f:real^2->real^N) k j1 j2.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\ DISJOINT j1 j2 /\
     compact j1 /\ compact j2 /\ ~(j1 = {}) /\ ~(j2 = {}) /\
     j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {} /\
     DISJOINT (j1 UNION inside j1) j2
     ==> (!x y. x IN j1 UNION inside j1 /\ y IN j1 UNION inside j1 /\ f x = f y
                ==> x = y) /\
         {x | x IN std_triangle /\ f x IN IMAGE f (j1 UNION inside j1)} =
         (j1 UNION inside j1) UNION j2 /\
         IMAGE f (j1 UNION inside j1) INTER moi_lt_double_image f = k /\
         IMAGE f (j1 UNION inside j1) INTER complex_boundary c = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`] MOI_LCP_CASE2_BIJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^2->bool) SUBSET std_triangle /\ j2 SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = j1 UNION j2` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* a point of D1 off j1 is not a double point *)
  SUBGOAL_THEN
   `!x:real^2. x IN j1 UNION inside j1 /\ (f:real^2->real^N) x IN moi_lt_double_image f
               ==> x IN j1`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{x | x IN inside j1 /\ (f:real^2->real^N) x IN moi_lt_double_image f} = {}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN j1 UNION inside j1 /\ y IN j1 UNION inside j1 /\
          (f:real^2->real^N) x = f y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN moi_lt_double_image f` ASSUME_TAC THENL
     [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `y:real^2`] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN j1 /\ y IN j1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the preimage of E1 *)
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x1:real^2` STRIP_ASSUME_TAC)) THEN
      ASM_CASES_TAC `(x:real^2) IN j1 UNION inside j1` THEN ASM_REWRITE_TAC[IN_UNION] THEN
      SUBGOAL_THEN `(f:real^2->real^N) x IN moi_lt_double_image f` ASSUME_TAC THENL
       [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`x:real^2`; `x1:real^2`] THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x1:real^2) IN j1` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^2) IN j1 UNION j2` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rand(concl th) = `j1 UNION j2:real^2->bool`)) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
        CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
        CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]]];
    (* E1 meets the double image in k *)
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^2) IN j1` MP_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
      ASM SET_TAC[]];
    (* E1 misses the boundary *)
    UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) f` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The local two-sidedness of a 2-sphere s in real^3.  If an                *)
(* injective continuous phi on a ball meets s exactly in the plane z1 = 0,  *)
(* then the two half balls lie in different components of the complement   *)
(* of s (JORDAN_BROUWER_SEPARATION, JORDAN_BROUWER_FRONTIER and            *)
(* INVARIANCE_OF_DOMAIN), so no connected set missing s meets both.         *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_SEP3 = prove
 (`!(s:real^3->bool) (phi:real^3->real^3) r z xp xm.
     s homeomorphic sphere(vec 0:real^3,&1) /\ &0 < r /\
     phi continuous_on ball(vec 0,r) /\
     (!x y. x IN ball(vec 0,r) /\ y IN ball(vec 0,r) /\ phi x = phi y ==> x = y) /\
     (!x. x IN ball(vec 0,r) ==> (phi x IN s <=> x$1 = &0)) /\
     connected z /\ DISJOINT z s /\
     xp IN ball(vec 0,r) /\ &0 < xp$1 /\ phi xp IN z /\
     xm IN ball(vec 0,r) /\ xm$1 < &0 /\ phi xm IN z
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (phi:real^3->real^3) (ball(vec 0,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  ABBREV_TAC `C = connected_component ((:real^3) DIFF s) ((phi:real^3->real^3) xp)` THEN
  SUBGOAL_THEN `(phi:real^3->real^3) xp IN (:real^3) DIFF s` ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3->bool) SUBSET C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^3->bool. convex h /\ h SUBSET ball(vec 0,r) /\
                     (!x. x IN h ==> ~(x$1 = &0)) /\
                     (?x. x IN h /\ (phi:real^3->real^3) x IN z)
                     ==> IMAGE phi h SUBSET C`
  ASSUME_TAC THENL
   [X_GEN_TAC `h:real^3->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `connected (IMAGE (phi:real^3->real^3) h)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `C = connected_component ((:real^3) DIFF s) ((phi:real^3->real^3) x0)`
    SUBST1_TAC THENL
     [EXPAND_TAC "C" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN ball(vec 0,r)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (phi:real^3->real^3) (ball(vec 0,r) INTER {x | x$1 > &0}) SUBSET C /\
    IMAGE phi (ball(vec 0,r) INTER {x | x$1 < &0}) SUBSET C`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_GT;
             CONVEX_HALFSPACE_COMPONENT_LT; INTER_SUBSET] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN CONJ_TAC THENL
     [MESON_TAC[REAL_LT_IMP_NZ];
      EXISTS_TAC `xp:real^3` THEN ASM_REWRITE_TAC[];
      MESON_TAC[REAL_LT_IMP_NE];
      EXISTS_TAC `xm:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~connected ((:real^3) DIFF s)` ASSUME_TAC THENL
   [MATCH_MP_TAC JORDAN_BROUWER_SEPARATION THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^3`; `&1`] THEN ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^3. w IN (:real^3) DIFF s /\ ~(w IN C)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~connected ((:real^3) DIFF s)` THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(:real^3) DIFF s = C` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET]; EXPAND_TAC "C" THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]];
      EXPAND_TAC "C" THEN REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT]];
    ALL_TAC] THEN
  ABBREV_TAC `C' = connected_component ((:real^3) DIFF s) (w:real^3)` THEN
  SUBGOAL_THEN `frontier C' = (s:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^3`; `&1`] THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN EXPAND_TAC "C'" THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) (vec 0) IN closure C'` ASSUME_TAC THENL
   [SUBGOAL_THEN `(phi:real^3->real^3) (vec 0) IN s` MP_TAC THENL
     [SUBGOAL_THEN `(vec 0:real^3) IN ball(vec 0,r)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
      UNDISCH_TAC `!x. x IN ball(vec 0,r) ==> ((phi:real^3->real^3) x IN s <=> x$1 = &0)` THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN ASM_REWRITE_TAC[VEC_COMPONENT];
      UNDISCH_TAC `frontier C' = (s:real^3->bool)` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN ball(vec 0,r) /\ (phi:real^3->real^3) x IN C'`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi:real^3->real^3) (ball(vec 0,r))`; `C':real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (TAUT `(a <=> b) ==> ~a ==> ~b`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(phi:real^3->real^3) (vec 0)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) x IN (:real^3) DIFF s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DIFF s`; `w:real^3`] CONNECTED_COMPONENT_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(phi:real^3->real^3) x IN C'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3)$1 = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(phi:real^3->real^3) x IN (:real^3) DIFF s` THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    UNDISCH_TAC `!x. x IN ball(vec 0,r) ==> ((phi:real^3->real^3) x IN s <=> x$1 = &0)` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) x IN C` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
      `~(a = &0) ==> a > &0 \/ a < &0`)) THENL
     [UNDISCH_TAC `IMAGE (phi:real^3->real^3) (ball(vec 0,r) INTER {x | x$1 > &0})
                   SUBSET C`;
      UNDISCH_TAC `IMAGE (phi:real^3->real^3) (ball(vec 0,r) INTER {x | x$1 < &0})
                   SUBSET C`] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C' = C:real^3->bool` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DIFF s`; `(phi:real^3->real^3) xp`;
                   `(phi:real^3->real^3) x`] CONNECTED_COMPONENT_EQ) THEN
    MP_TAC(ISPECL [`(:real^3) DIFF s`; `w:real^3`;
                   `(phi:real^3->real^3) x`] CONNECTED_COMPONENT_EQ) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~((w:real^3) IN C)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "C'" THEN
  REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[GSYM IN; CONNECTED_COMPONENT_REFL_EQ]);;


(* ------------------------------------------------------------------------- *)
(* The crossing chart near a double point y0 with exactly two               *)
(* preimages x1 (sheet n1, plane z1 = 0) and x2 (sheet n2, plane z2 = 0).   *)
(* For a closed A near x1 missing x2 and a B near x2, the inverse chart    *)
(* psi on a small ball meets f(A) exactly in z1 = 0, maps the points of     *)
(* z2 = 0 off the axis to images of points of B that are not double        *)
(* points, and lands in a given neighbourhood W of y0.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_CHART_LOCAL_0 = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) y0 u (h:real^N->real^3) h'
    n1 n2 x1 x2 A B W.
     f continuous_on std_triangle /\
     u SUBSET UNIONS c /\ y0 IN u /\ homeomorphism (u,IMAGE h u) (h,h') /\
     h y0 = vec 0 /\ IMAGE h u = ball(vec 0,&1) /\
     {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
     IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
     IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
     IMAGE h (moi_lt_double_image f INTER u) =
     IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
     open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n1 /\
     open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n2 /\
     x1 IN n1 /\ x2 IN n2 /\
     (!x. x IN std_triangle /\ f x = y0 ==> x = x1 \/ x = x2) /\
     A SUBSET std_triangle /\ closed A /\ ~(x2 IN A) /\
     (?dA. &0 < dA /\ ball(x1,dA) INTER std_triangle SUBSET A) /\
     B SUBSET std_triangle /\ (?dB. &0 < dB /\ ball(x2,dB) INTER std_triangle SUBSET B) /\
     open_in (subtopology euclidean (UNIONS c)) W /\ y0 IN W
     ==> ?r (psi:real^3->real^N). &0 < r /\ psi continuous_on ball(vec 0,r) /\
                 (!z w. z IN ball(vec 0,r) /\ w IN ball(vec 0,r) /\ psi z = psi w
                        ==> z = w) /\
                 IMAGE psi (ball(vec 0,r)) SUBSET W /\ psi (vec 0) = y0 /\
                 (!z. z IN ball(vec 0,r) ==> (psi z IN IMAGE f A <=> z$1 = &0)) /\
                 (!z. z IN ball(vec 0,r) /\ z$2 = &0 /\ ~(z$1 = &0)
                      ==> ?b. b IN B /\ psi z = f b /\
                              ~(f b IN moi_lt_double_image f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x:real^2. x IN n1 UNION n2 <=> x IN std_triangle /\ (f:real^2->real^N) x IN u`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `n1 UNION n2:real^2->bool`)) THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (n1 UNION n2)) (n1:real^2->bool) /\
    open_in (subtopology euclidean (n1 UNION n2)) (n2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`open_in (subtopology euclidean {x | x IN std_triangle /\ (f:real^2->real^N) x IN u})
               (n1:real^2->bool)`;
      `open_in (subtopology euclidean {x | x IN std_triangle /\ (f:real^2->real^N) x IN u})
               (n2:real^2->bool)`] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the radius delta in the source *)
  SUBGOAL_THEN
   `?d. &0 < d /\ ball(x1:real^2,d) INTER std_triangle SUBSET A /\
        ball(x2,d) INTER std_triangle SUBSET B /\ DISJOINT (ball(x2,d)) A /\
        ball(x1,d) INTER (n1 UNION n2) SUBSET n1 /\
        ball(x2,d) INTER (n1 UNION n2) SUBSET n2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real^2->bool`; `x2:real^2`] SEPARATE_POINT_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `open_in (subtopology euclidean (n1 UNION n2)) (n1:real^2->bool)` THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x1:real^2` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `open_in (subtopology euclidean (n1 UNION n2)) (n2:real^2->bool)` THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x2:real^2` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d5:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min dA (min dB (min d3 (min d4 d5)))` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; DISJOINT; EXTENSION; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      UNDISCH_TAC `ball(x1:real^2,dA) INTER std_triangle SUBSET A` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      UNDISCH_TAC `ball(x2:real^2,dB) INTER std_triangle SUBSET B` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (term_match [] `!x:real^2. x IN A ==> d <= dist(x2,x)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      UNDISCH_TAC `ball(x1:real^2,d4) INTER (n1 UNION n2) SUBSET n1` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      UNDISCH_TAC `ball(x2:real^2,d5) INTER (n1 UNION n2) SUBSET n2` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the radius epsilon around y0 *)
  SUBGOAL_THEN
   `?e. &0 < e /\
        !x. x IN std_triangle /\ dist(y0,(f:real^2->real^N) x) < e
            ==> x IN ball(x1,d) \/ x IN ball(x2,d)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f:real^2->real^N)
                     (std_triangle DIFF (ball(x1,d) UNION ball(x2,d)))`;
                   `y0:real^N`] SEPARATE_POINT_CLOSED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `std_triangle` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
          MATCH_MP_TAC COMPACT_DIFF THEN
          SIMP_TAC[MOI_LTD_STD_TRIANGLE_BASIC; OPEN_UNION; OPEN_BALL]];
        REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
          can (term_match [] `!x:real^2. x IN std_triangle /\ (f:real^2->real^N) x = y0 ==> P x`)
              (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_MESON_TAC[CENTRE_IN_BALL]];
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^2->real^N) x`) THEN ANTS_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e'. &0 < e' /\ !y:real^N. y IN UNIONS (c:(real^N->bool)->bool) /\ dist(y0,y) < e' ==> y IN W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (W:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^3->real^N) continuous (at (vec 0))` MP_TAC THENL
   [UNDISCH_TAC `(h':real^3->real^N) continuous_on IMAGE (h:real^N->real^3) u` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `min e e'`) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(h':real^3->real^N) (vec 0) = y0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min r0 (&1)` THEN EXISTS_TAC `h':real^3->real^N` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,min r0 (&1)) SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ball(vec 0:real^3,min r0 (&1))
        ==> z IN IMAGE (h:real^N->real^3) u /\ (h':real^3->real^N) z IN u /\ h(h' z) = z /\
            dist(y0,h' z) < e /\ (h':real^3->real^N) z IN W`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (h:real^N->real^3) u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^N) z IN u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(y0,(h':real^3->real^N) z) < e /\ dist(y0,h' z) < e'`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN
      SUBGOAL_THEN `y0 = (h':real^3->real^N) (vec 0)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,min r0 (&1))` THEN
      REWRITE_TAC[IN_BALL; DIST_SYM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ASM SET_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(a:real^2) IN std_triangle` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(a:real^2) IN n1` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real^2) IN ball(x1,d) \/ a IN ball(x2,d)` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        STRIP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        UNDISCH_TAC `ball(x1:real^2,d) INTER (n1 UNION n2) SUBSET n1` THEN
        REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1`
      MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `a:real^2` THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1`
      MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; o_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(a:real^2) IN std_triangle /\ (f:real^2->real^N) a IN u`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_UNION]; ALL_TAC] THEN
      SUBGOAL_THEN `(h':real^3->real^N) z = f (a:real^2)` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `a:real^2` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:real^2) IN ball(x1,d) \/ a IN ball(x2,d)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(a:real^2) IN n2` MP_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n2`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(b:real^2) IN std_triangle /\ (f:real^2->real^N) b IN u`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^N) z = f (b:real^2)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `b:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(b:real^2) IN ball(x1,d) \/ b IN ball(x2,d)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `(b:real^2) IN n1` MP_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE (h:real^N->real^3)
                                   (moi_lt_double_image f INTER u)` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `(f:real^2->real^N) b` THEN
        ASM_MESON_TAC[];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]]]]);;

(* The swap of the first two coordinates of real^3.                         *)

let moi_lcp_sw = new_definition
 `moi_lcp_sw (z:real^3) = vector[z$2; z$1; z$3]:real^3`;;

let MOI_LCP_SW = prove
 (`(!z. moi_lcp_sw (moi_lcp_sw z) = z) /\ linear moi_lcp_sw /\
   (!z. (moi_lcp_sw z)$1 = z$2 /\ (moi_lcp_sw z)$2 = z$1 /\ (moi_lcp_sw z)$3 = z$3) /\
   (!z. norm (moi_lcp_sw z) = norm z) /\ moi_lcp_sw (vec 0) = vec 0 /\
   (!s. IMAGE moi_lcp_sw s = {z | moi_lcp_sw z IN s}) /\
   (!s. homeomorphism (s,IMAGE moi_lcp_sw s) (moi_lcp_sw,moi_lcp_sw))`,
  SUBGOAL_THEN `!z. moi_lcp_sw (moi_lcp_sw z) = z` ASSUME_TAC THENL
   [REWRITE_TAC[moi_lcp_sw; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]; ALL_TAC] THEN
  SUBGOAL_THEN `linear moi_lcp_sw` ASSUME_TAC THENL
   [REWRITE_TAC[linear; moi_lcp_sw; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. IMAGE moi_lcp_sw s = {z | moi_lcp_sw z IN s}` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_lcp_sw; VECTOR_3];
    GEN_TAC THEN REWRITE_TAC[NORM_EQ; DOT_3; moi_lcp_sw; VECTOR_3] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_lcp_sw; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT];
    GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

(* The chart lemma for a crossing2 chart at an interior double point with   *)
(* fibre {x1, x2}; the sheet of x1 is made the plane z1 = 0, swapping the   *)
(* first two coordinates of the chart if necessary.                          *)

let MOI_LCP_CHART_LOCAL = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) y0 x1 x2 A B W.
     moi_lt_singular_disk c f /\ moi_lt_crossing2_at c f y0 /\
     ~(y0 IN complex_boundary c) /\
     x1 IN std_triangle /\ x2 IN std_triangle /\ ~(x1 = x2) /\
     f x1 = y0 /\ f x2 = y0 /\
     (!x. x IN std_triangle /\ f x = y0 ==> x = x1 \/ x = x2) /\
     A SUBSET std_triangle /\ closed A /\ ~(x2 IN A) /\
     (?dA. &0 < dA /\ ball(x1,dA) INTER std_triangle SUBSET A) /\
     B SUBSET std_triangle /\ (?dB. &0 < dB /\ ball(x2,dB) INTER std_triangle SUBSET B) /\
     open_in (subtopology euclidean (UNIONS c)) W /\ y0 IN W
     ==> ?r (psi:real^3->real^N). &0 < r /\ psi continuous_on ball(vec 0,r) /\
                 (!z w. z IN ball(vec 0,r) /\ w IN ball(vec 0,r) /\ psi z = psi w
                        ==> z = w) /\
                 IMAGE psi (ball(vec 0,r)) SUBSET W /\ psi (vec 0) = y0 /\
                 (!z. z IN ball(vec 0,r) ==> (psi z IN IMAGE f A <=> z$1 = &0)) /\
                 (!z. z IN ball(vec 0,r) /\ z$2 = &0 /\ ~(z$1 = &0)
                      ==> ?b. b IN B /\ psi z = f b /\
                              ~(f b IN moi_lt_double_image f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lt_crossing2_at]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                       `n1:real^2->bool`; `n2:real^2->bool`] THEN
  STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE (h:real^N->real^3) u) (h,h')` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(x1:real^2) IN n1 UNION n2 /\ (x2:real^2) IN n1 UNION n2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `n1 UNION n2:real^2->bool`)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* in each sheet some point maps to y0 *)
  SUBGOAL_THEN
   `!m:real^2->bool. m SUBSET n1 UNION n2 /\
                     (vec 0:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) m
                     ==> ?x. x IN m /\ (x = x1 \/ x = x2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:real^2->bool` THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}`
    MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1 /\
                (vec 0:real^3) IN IMAGE (h o f) n2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL; REAL_LT_01; VEC_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN n1 /\ x2 IN n2 \/ x1 IN n2 /\ x2 IN n1` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `n1:real^2->bool` th) THEN
                            MP_TAC(SPEC `n2:real^2->bool` th)) THEN
    ASM_REWRITE_TAC[SUBSET_UNION] THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN
    UNDISCH_TAC `~(x1:real^2 = x2)` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y0:real^N`;
                   `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                   `n1:real^2->bool`; `n2:real^2->bool`; `x1:real^2`; `x2:real^2`;
                   `A:real^2->bool`; `B:real^2->bool`; `W:real^N->bool`]
                  MOI_LCP_CHART_LOCAL_0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y0:real^N`;
                 `u:real^N->bool`; `moi_lcp_sw o (h:real^N->real^3)`;
                 `(h':real^3->real^N) o moi_lcp_sw`;
                 `n2:real^2->bool`; `n1:real^2->bool`; `x1:real^2`; `x2:real^2`;
                 `A:real^2->bool`; `B:real^2->bool`; `W:real^N->bool`]
                MOI_LCP_CHART_LOCAL_0) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  STRIP_ASSUME_TAC MOI_LCP_SW THEN
  SUBGOAL_THEN `IMAGE (moi_lcp_sw o (h:real^N->real^3)) u = ball(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o; IN_BALL_0; EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^3`; `h':real^3->real^N`; `moi_lcp_sw`; `moi_lcp_sw`;
                   `u:real^N->bool`; `IMAGE (h:real^N->real^3) u`;
                   `IMAGE moi_lcp_sw (IMAGE (h:real^N->real^3) u)`]
                  HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
    SUBGOAL_THEN `{z:real^3 | moi_lcp_sw z IN ball(vec 0,&1)} = ball(vec 0,&1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
    SET_TAC[];
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[];
    REWRITE_TAC[GSYM o_ASSOC] THEN ONCE_REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM o_ASSOC] THEN ONCE_REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The separation step S4 in a PL 3-cell nn of real^N with                  *)
(* frontier sphere fr.  A disk da in nn meeting fr in its boundary al, a    *)
(* disk fr2 of fr bounded by al, and a chart psi meeting da exactly in      *)
(* z1 = 0 inside the open cell: no connected set missing da and fr2 meets   *)
(* both sides of the chart (transport to a 3-simplex of real^3, DISK_UNION, *)
(* MOI_LCP_SEP3).                                                            *)
(* ------------------------------------------------------------------------- *)

(* PL cells are compact polyhedra (the same as MOI_FSP_CELL_POLYHEDRON of   *)
(* pc_moi_fnd_split, outside this closure), and contain their boundary.     *)

let MOI_LCP_CELL_POLYHEDRON = prove
 (`!n (d:real^N->bool) j.
     pl_cell_with_boundary n d j ==> pl_polyhedron d /\ compact d /\ j SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [homeomorphism]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{k:real^N->bool}` THEN
    REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; homeomorphism];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]]);;

(* A PL 2-sphere in real^3 is homeomorphic to the unit sphere.               *)

let MOI_LCP_SPHERE2_HOMEOMORPHIC = prove
 (`!s:real^3->bool. pl_sphere 2 s ==> s homeomorphic sphere(vec 0:real^3,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `relative_frontier k:real^3->bool`;
                 `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`] RELATIVE_FRONTIER_CBALL) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  ASM_SIMP_TAC[CONVEX_CBALL; BOUNDED_CBALL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
                  ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_3]);;

let MOI_LCP_S4_CORE = prove
 (`!(nn:real^N->bool) fr da al fr2 z (psi:real^3->real^N) r w xp xm.
     pl_cell_with_boundary 3 nn fr /\
     pl_cell_with_boundary 2 da al /\ da SUBSET nn /\ da INTER fr = al /\
     pl_cell_with_boundary 2 fr2 al /\ fr2 SUBSET fr /\
     w SUBSET nn DIFF fr /\
     &0 < r /\ psi continuous_on ball(vec 0,r) /\
     (!x y. x IN ball(vec 0,r) /\ y IN ball(vec 0,r) /\ psi x = psi y ==> x = y) /\
     IMAGE psi (ball(vec 0,r)) SUBSET w /\
     (!x. x IN ball(vec 0,r) ==> (psi x IN da <=> x$1 = &0)) /\
     connected z /\ z SUBSET nn /\ DISJOINT z da /\ DISJOINT z fr2 /\
     xp IN ball(vec 0,r) /\ &0 < xp$1 /\ psi xp IN z /\
     xm IN ball(vec 0,r) /\ xm$1 < &0 /\ psi xm IN z
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary] o check (fun th ->
    concl th = `pl_cell_with_boundary 3 (nn:real^N->bool) fr`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `vec 0:real^3` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k3:real^3->bool`; `k:real^N->bool`; `&3:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (nn:real^N->bool,k3:real^3->bool)
                     ((q:real^N->real^3) o (g0:real^N->real^N),
                      (f0:real^N->real^N) o (p:real^3->real^N))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g = (q:real^N->real^3) o (g0:real^N->real^N)` THEN
  ABBREV_TAC `G = (f0:real^N->real^N) o (p:real^3->real^N)` THEN
  SUBGOAL_THEN `homeomorphism (nn:real^N->bool,k3:real^3->bool) (g,G)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(fr:real^N->bool) SUBSET nn` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN `(al:real^N->bool) SUBSET da /\ al SUBSET fr2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!d:real^N->bool. pl_cell_with_boundary 2 d al /\ d SUBSET nn
                     ==> pl_cell_with_boundary 2 (IMAGE (g:real^N->real^3) d)
                                                 (IMAGE g al)`
  ASSUME_TAC THENL
   [X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCL_CELL_TRANSFER THEN
    EXISTS_TAC `d:real^N->bool` THEN EXISTS_TAC `G:real^3->real^N` THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`nn:real^N->bool`; `k3:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 2 (IMAGE (g:real^N->real^3) da UNION IMAGE g fr2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DISK_UNION THEN EXISTS_TAC `IMAGE (g:real^N->real^3) al` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(da:real^N->bool) INTER fr2 = al` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(fr2:real^N->bool) SUBSET nn` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!x. x IN nn ==> (G:real^3->real^N) ((g:real^N->real^3) x) = x` THEN
    UNDISCH_TAC `(da:real^N->bool) SUBSET nn` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^N->real^3) da UNION IMAGE g fr2`;
                 `(g:real^N->real^3) o (psi:real^3->real^N)`; `r:real`;
                 `IMAGE (g:real^N->real^3) z`; `xp:real^3`; `xm:real^3`] MOI_LCP_SEP3) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN ball(vec 0:real^3,r) ==> (psi:real^3->real^N) x IN nn /\
                                                 ~(psi x IN fr)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_MESON_TAC[MOI_LCP_SPHERE2_HOMEOMORPHIC];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `nn:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP th
      (ASSUME `(x:real^3) IN ball(vec 0,r)`))]) o check (fun th ->
      can (term_match [] `!x:real^3. x IN ball(vec 0,r) ==> (P x <=> Q x)`) (concl th))) THEN
    REWRITE_TAC[o_THM; IN_UNION; IN_IMAGE] THEN
    SUBGOAL_THEN `(fr2:real^N->bool) SUBSET nn` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    SUBGOAL_THEN `(fr2:real^N->bool) SUBSET nn` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`!x. x IN nn ==> (G:real^3->real^N) ((g:real^N->real^3) x) = x`;
      `(da:real^N->bool) SUBSET nn`; `(z:real^N->bool) SUBSET nn`;
      `DISJOINT (z:real^N->bool) da`; `DISJOINT (z:real^N->bool) fr2`] THEN
    SET_TAC[];
    ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Three disjoint polygons al, bi, bo on a PL 2-sphere fr.                   *)
(* Either bo bounds a disk of fr missing al and bi, or al bounds two disks   *)
(* of fr, one containing both bi and bo (the configuration excluded by      *)
(* MOI_LCP_S4_CORE).                                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_CONNECTED_SPLIT = prove
 (`!s e1 e2:real^N->bool.
     connected s /\ closed e1 /\ closed e2 /\ s SUBSET e1 UNION e2 /\
     DISJOINT s (e1 INTER e2)
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (s:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
  MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_LCP_CELL_CONNECTED = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> connected d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `d:real^N->bool`)) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]);;

let MOI_LCP_CHOOSE_CAP = prove
 (`!(fr:real^N->bool) al bi bo.
     pl_sphere 2 fr /\ pl_sphere 1 al /\ pl_sphere 1 bi /\ pl_sphere 1 bo /\
     al SUBSET fr /\ bi SUBSET fr /\ bo SUBSET fr /\
     DISJOINT al bi /\ DISJOINT al bo /\ DISJOINT bi bo
     ==> (?d. pl_cell_with_boundary 2 d bo /\ d SUBSET fr /\
              DISJOINT d al /\ DISJOINT d bi) \/
         (?fr1 fr2. pl_cell_with_boundary 2 fr1 al /\ pl_cell_with_boundary 2 fr2 al /\
                    fr1 UNION fr2 = fr /\ fr1 INTER fr2 = al /\
                    bi SUBSET fr1 /\ bo SUBSET fr1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fr:real^N->bool`; `bo:real^N->bool`] MOI_S4O_SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^N->bool` (X_CHOOSE_THEN `d2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed (d1:real^N->bool) /\ closed (d2:real^N->bool) /\
                bo SUBSET d1 /\ bo SUBSET d2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. connected s /\ s SUBSET fr /\ DISJOINT s bo
                     ==> s SUBSET d1 \/ s SUBSET d2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCP_CONNECTED_SPLIT THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(al:real^N->bool) SUBSET d1 \/ al SUBSET d2` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MOI_S4O_SPHERE1_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bi:real^N->bool) SUBSET d1 \/ bi SUBSET d2` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MOI_S4O_SPHERE1_CONNECTED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fr:real^N->bool`; `al:real^N->bool`] MOI_S4O_SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed (e1:real^N->bool) /\ closed (e2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  (* a disk of bo containing bi and missing al lies in e1 or e2 *)
  SUBGOAL_THEN
   `!d:real^N->bool. pl_cell_with_boundary 2 d bo /\ d SUBSET fr /\ DISJOINT d al /\
                     bi SUBSET d
                     ==> ?fr1 fr2. pl_cell_with_boundary 2 fr1 al /\
                                   pl_cell_with_boundary 2 fr2 al /\
                                   fr1 UNION fr2 = fr /\ fr1 INTER fr2 = al /\
                                   bi SUBSET fr1 /\ bo SUBSET fr1`
  ASSUME_TAC THENL
   [X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(bo:real^N->bool) SUBSET d` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON]; ALL_TAC] THEN
    MP_TAC(ISPECL [`d:real^N->bool`; `e1:real^N->bool`; `e2:real^N->bool`]
      MOI_LCP_CONNECTED_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_LCP_CELL_CONNECTED];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`e2:real^N->bool`; `e1:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(al SUBSET d1 /\ bi SUBSET d1) \/ (al SUBSET d2 /\ bi SUBSET d2) \/
    (al SUBSET d1 /\ bi SUBSET (d2:real^N->bool)) \/ (al SUBSET d2 /\ bi SUBSET d1)`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `d2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    DISJ1_TAC THEN EXISTS_TAC `d1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `d2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `d1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;



(* ------------------------------------------------------------------------- *)
(* The planar source capped to a closed surface.  K                         *)
(* triangulates std_triangle, so it is a combinatorial surface with         *)
(* boundary the relative frontier (MOI_FRB_SURF_INVARIANT); the cap of      *)
(* pc_moi_fnd_cap is a closed combinatorial surface m, and near the lift of *)
(* an interior point of the triangle the second derived subdivision of m is *)
(* the lift of that of K.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Components under a homeomorphism (the same as MOI_S4W_COMPONENTS_HOMEO  *)
(* of pc_moi_s34_op2b, outside this closure).                               *)

let MOI_LCP_COMPONENTS_HOMEO = prove
 (`!(f:real^M->real^N) g s t.
     homeomorphism (s,t) (f,g)
     ==> components t = IMAGE (IMAGE f) (components s) /\
         (FINITE (components s) ==> CARD (components t) = CARD (components s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `components t = IMAGE (IMAGE (f:real^M->real^N)) (components s)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[components; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(g:real^N->real^M) y IN s` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `connected_component s ((g:real^N->real^M) y)` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`; `s:real^M->bool`;
                       `t:real^N->bool`; `(g:real^N->real^M) y`]
          HOMEOMORPHISM_CONNECTED_COMPONENT) THEN
        ASM_SIMP_TAC[];
        EXISTS_TAC `(g:real^N->real^M) y` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `(f:real^M->real^N) x` THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`; `s:real^M->bool`;
                     `t:real^N->bool`; `x:real^M`]
        HOMEOMORPHISM_CONNECTED_COMPONENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c1:real^M->bool`; `c2:real^M->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c1:real^M->bool) SUBSET s /\ (c2:real^M->bool) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^M->bool. c SUBSET s ==> IMAGE (g:real^N->real^M) (IMAGE f c) = c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The surface boundary of the faces of a 2-simplex (the same as             *)
(* MOI_FSP_FACE_SB of pc_moi_fnd_split, outside this closure).              *)

let MOI_LCP_FACE_SB = prove
 (`!k:real^N->bool.
     &2 simplex k ==> surface_boundary {f | f face_of k} = relative_frontier k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim (k:real^N->bool) = &2 /\ convex k /\ polyhedron k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYHEDRON]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON] THEN
  REWRITE_TAC[surface_boundary; IN_ELIM_THM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; facet_of] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  ASM_CASES_TAC `(s:real^N->bool) face_of k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `aff_dim (s:real^N->bool) = &1` THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (s:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{r:real^N->bool | r face_of k /\ aff_dim r = &2 /\ s SUBSET r} = {k}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `k:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    REWRITE_TAC[CARD_SING]]);;

(* Simplices of the subdivision through a point all of whose carriers lie in *)
(* a subcomplex n lie in the subdivision of n.                              *)

let MOI_LCP_BSD_LOCAL = prove
 (`!(m:(real^N->bool)->bool) n x.
     lf_simplicial_complex m /\ simplicial_subcomplex n m /\
     (!s. s IN m /\ x IN s ==> s IN n)
     ==> !s. s IN barycentric_subdivision m /\ x IN s
             ==> s IN barycentric_subdivision n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [UNDISCH_TAC `(x:real^N) IN s` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `f:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_bar_chain] o check (fun th ->
    concl th = `moi_bar_chain (m:(real^N->bool)->bool) f`)) THEN
  SUBGOAL_THEN `UNIONS f IN (n:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `!s:real^N->bool. s IN m /\ x IN s ==> s IN n` THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_bar_chain] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
  UNDISCH_TAC `simplicial_subcomplex (n:(real^N->bool)->bool) m` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  EXISTS_TAC `UNIONS f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t = t INTER UNIONS f:real^N->bool` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lf_simplicial_complex (m:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real^N->bool`; `UNIONS f:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

(* A triangulation of std_triangle is a combinatorial surface bounded by   *)
(* the relative frontier, a single boundary component.                      *)

let MOI_LCP_TRI_CM2 = prove
 (`!K:(real^2->bool)->bool.
     simplicial_complex K /\ UNIONS K = std_triangle
     ==> combinatorial_manifold_with_boundary 2 K /\
         surface_boundary K = relative_frontier std_triangle /\
         components (surface_boundary K) = {relative_frontier std_triangle}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{f:real^2->bool | f face_of std_triangle}`; `K:(real^2->bool)->bool`;
                 `I:real^2->real^2`; `I:real^2->real^2`] MOI_FRB_SURF_INVARIANT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
      MATCH_MP_TAC MOI_FRB_FACE_COMPLEX_CMWB2 THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX];
      ASM_MESON_TAC[simplicial_complex];
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `UNIONS {f:real^2->bool | f face_of std_triangle} = std_triangle`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[FACE_OF_IMP_SUBSET];
          MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN t ==> s SUBSET UNIONS t`) THEN
          REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC FACE_OF_REFL THEN
          REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC]];
        ASM_REWRITE_TAC[HOMEOMORPHISM_I]]];
    ALL_TAC] THEN
  SIMP_TAC[MOI_LCP_FACE_SB; MOI_LTD_STD_TRIANGLE_SIMPLEX; IMAGE_I] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM o CONJUNCT1)) THEN
  ASM_REWRITE_TAC[COMPONENTS_EQ_SING] THEN
  SUBGOAL_THEN `aff_dim std_triangle = &2` ASSUME_TAC THENL
   [MESON_TAC[AFF_DIM_SIMPLEX; MOI_LTD_STD_TRIANGLE_SIMPLEX]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
    ASM_SIMP_TAC[MOI_LTD_STD_TRIANGLE_BASIC; COMPACT_IMP_BOUNDED] THEN INT_ARITH_TAC;
    REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `std_triangle` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_SIMP_TAC[MOI_LTD_STD_TRIANGLE_BASIC; COMPACT_IMP_BOUNDED] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `aff_dim {a:real^2} = &2` THEN REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The cap m of a triangulation K of std_triangle; near the                 *)
(* lift of an interior point the second derived subdivision of m consists   *)
(* of lifts of simplices of the second derived subdivision of K.            *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_CAP_SETUP = prove
 (`!K:(real^2->bool)->bool.
     simplicial_complex K /\ UNIONS K = std_triangle
     ==> FINITE (moi_fcb_cap K (\P:real^2->bool. 0)) /\
         combinatorial_manifold 2 (moi_fcb_cap K (\P:real^2->bool. 0)) /\
         lf_simplicial_complex (moi_fcb_cap K (\P:real^2->bool. 0)) /\
         simplicial_subcomplex (IMAGE (IMAGE moi_fcb_lift) K)
                               (moi_fcb_cap K (\P:real^2->bool. 0)) /\
         IMAGE (IMAGE moi_fcb_lift) (barycentric_subdivision (barycentric_subdivision K))
         SUBSET barycentric_subdivision
                  (barycentric_subdivision (moi_fcb_cap K (\P:real^2->bool. 0))) /\
         (!x s. x IN std_triangle DIFF relative_frontier std_triangle /\
                s IN barycentric_subdivision
                       (barycentric_subdivision (moi_fcb_cap K (\P:real^2->bool. 0))) /\
                moi_fcb_lift x IN s
                ==> s IN IMAGE (IMAGE moi_fcb_lift)
                               (barycentric_subdivision (barycentric_subdivision K)))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `K:(real^2->bool)->bool` MOI_LCP_TRI_CM2) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `m = moi_fcb_cap (K:(real^2->bool)->bool) (\P:real^2->bool. 0)` THEN
  ABBREV_TAC `n = IMAGE (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum)) K` THEN
  SUBGOAL_THEN `FINITE (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `\P:real^2->bool. 0`] MOI_FCB_CAP_CM2) THEN
  ASM_REWRITE_TAC[IN_SING] THEN ANTS_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^(2,2)finite_sum->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `\P:real^2->bool. 0`] MOI_FCB_LIFT_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `m:(real^(2,2)finite_sum->bool)->bool`;
                 `moi_fcb_lift:real^2->real^(2,2)finite_sum`] MOI_LCP_SD2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[simplicial_map_on] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [EXPAND_TAC "m" THEN REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ1_TAC THEN
        EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`moi_fcb_lift:real^2->real^(2,2)finite_sum`;
                              `vec 0:real^(2,2)finite_sum`] THEN
        REWRITE_TAC[MOI_FCB_LIFT; VECTOR_ADD_RID]];
      MESON_TAC[MOI_FCB_LIFT]];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `simplicial_subcomplex (barycentric_subdivision (n:(real^(2,2)finite_sum->bool)->bool))
                          (barycentric_subdivision m) /\
    simplicial_subcomplex (barycentric_subdivision (barycentric_subdivision n))
                          (barycentric_subdivision (barycentric_subdivision m))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[BARYCENTRIC_SUBDIVISION_SUBCOMPLEX];
      ASM_MESON_TAC[BARYCENTRIC_SUBDIVISION_SUBCOMPLEX; BARYCENTRIC_SUBDIVISION_LF]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `sg:real^(2,2)finite_sum->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN m /\ moi_fcb_lift (x:real^2) IN t
        ==> (t:real^(2,2)finite_sum->bool) IN n`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^(2,2)finite_sum->bool` THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_fcb_lift (x:real^2) IN t` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `convex (s:real^2->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE] THEN DISCH_TAC THEN
      UNDISCH_TAC `(P:real^2->bool) IN components (surface_boundary K)` THEN
      REWRITE_TAC[ASSUME `components (surface_boundary (K:(real^2->bool)->bool)) =
                          {relative_frontier std_triangle}`; IN_SING] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^2) IN std_triangle DIFF relative_frontier std_triangle` THEN
      UNDISCH_TAC `(x:real^2) IN s` THEN
      UNDISCH_TAC `(s:real^2->bool) SUBSET relative_frontier std_triangle` THEN
      MATCH_MP_TAC(TAUT `~(a /\ b /\ c) ==> a ==> b ==> c ==> d`) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^(2,2)finite_sum->bool)->bool`;
                 `n:(real^(2,2)finite_sum->bool)->bool`;
                 `moi_fcb_lift (x:real^2)`] MOI_LCP_BSD_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^(2,2)finite_sum->bool)->bool)`;
                 `barycentric_subdivision (n:(real^(2,2)finite_sum->bool)->bool)`;
                 `moi_fcb_lift (x:real^2)`] MOI_LCP_BSD_LOCAL) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]);;


(* ------------------------------------------------------------------------- *)
(* For a subcomplex L of K inside the open triangle, the                    *)
(* derived neighbourhood and frontier of the lifted L in the cap are the    *)
(* lifts of those of L in K (the frontier when the neighbourhood itself     *)
(* misses the relative frontier).                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_CAP_DNC = prove
 (`!(K:(real^2->bool)->bool) L s.
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_subcomplex L K /\
     UNIONS L SUBSET std_triangle DIFF relative_frontier std_triangle /\
     s IN barycentric_subdivision (barycentric_subdivision K)
     ==> (IMAGE moi_fcb_lift s IN
          derived_nbhd_complex (moi_fcb_cap K (\P:real^2->bool. 0))
                               (IMAGE (IMAGE moi_fcb_lift) L) <=>
          s IN derived_nbhd_complex K L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `K:(real^2->bool)->bool` MOI_LCP_CAP_SETUP) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = moi_fcb_cap (K:(real^2->bool)->bool) (\P:real^2->bool. 0)` THEN
  STRIP_TAC THEN
  STRIP_ASSUME_TAC(INST_TYPE [`:2`,`:N`] MOI_FCB_LIFT) THEN
  REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM; GSYM IMAGE_UNIONS] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real^(2,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(r INTER IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) (UNIONS L) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^(2,2)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(r:real^(2,2)finite_sum->bool) IN
                  IMAGE (IMAGE moi_fcb_lift) (barycentric_subdivision
                                                (barycentric_subdivision K))`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r0:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^(2,2)finite_sum) IN r` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) s face_of r` THEN
      ASM_SIMP_TAC[FACE_OF_LINEAR_IMAGE]];
    DISCH_THEN(X_CHOOSE_THEN `r0:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) r0` THEN
    ASM_SIMP_TAC[FACE_OF_LINEAR_IMAGE] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `~(r0 INTER UNIONS (L:(real^2->bool)->bool) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(moi_fcb_lift:real^2->real^(2,2)finite_sum) x` THEN
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]]);;

let MOI_LCP_CAP_NBHD = prove
 (`!(K:(real^2->bool)->bool) L.
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_subcomplex L K /\
     UNIONS L SUBSET std_triangle DIFF relative_frontier std_triangle
     ==> simplicial_subcomplex (IMAGE (IMAGE moi_fcb_lift) L)
                               (moi_fcb_cap K (\P:real^2->bool. 0)) /\
         UNIONS (IMAGE (IMAGE moi_fcb_lift) L) = IMAGE moi_fcb_lift (UNIONS L) /\
         derived_nbhd (moi_fcb_cap K (\P:real^2->bool. 0)) (IMAGE (IMAGE moi_fcb_lift) L) =
         IMAGE moi_fcb_lift (derived_nbhd K L) /\
         (derived_nbhd K L SUBSET std_triangle DIFF relative_frontier std_triangle
          ==> derived_frontier (moi_fcb_cap K (\P:real^2->bool. 0))
                               (IMAGE (IMAGE moi_fcb_lift) L) =
              IMAGE moi_fcb_lift (derived_frontier K L))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `K:(real^2->bool)->bool` MOI_LCP_CAP_SETUP) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = moi_fcb_cap (K:(real^2->bool)->bool) (\P:real^2->bool. 0)` THEN
  STRIP_TAC THEN
  STRIP_ASSUME_TAC(INST_TYPE [`:2`,`:N`] MOI_FCB_LIFT) THEN
  SUBGOAL_THEN `simplicial_subcomplex (IMAGE (IMAGE moi_fcb_lift) L)
                  (m:(real^(2,2)finite_sum->bool)->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (IMAGE (IMAGE moi_fcb_lift) K)
                   (m:(real^(2,2)finite_sum->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex (L:(real^2->bool)->bool) K` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `f:real^(2,2)finite_sum->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^2->bool` STRIP_ASSUME_TAC o
        MATCH_MP MOI_FCB_LIFT_FACES) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_UNIONS] THEN
  SUBGOAL_THEN
   `derived_nbhd (m:(real^(2,2)finite_sum->bool)->bool) (IMAGE (IMAGE moi_fcb_lift) L) =
    IMAGE moi_fcb_lift (derived_nbhd K L)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_nbhd; GSYM IMAGE_UNIONS] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `sg:real^(2,2)finite_sum->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^(2,2)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN `(sg:real^(2,2)finite_sum->bool) IN
                    IMAGE (IMAGE moi_fcb_lift) (barycentric_subdivision
                                                  (barycentric_subdivision K))`
      MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `s0:real^2->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN t ==> s SUBSET UNIONS t`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^(2,2)finite_sum) IN sg` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^2` THEN
      DISCH_THEN(X_CHOOSE_THEN `s0:real^2->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) s0` THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(s0 INTER UNIONS (L:(real^2->bool)->bool) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(moi_fcb_lift:real^2->real^(2,2)finite_sum) z` THEN
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^(2,2)finite_sum` THEN
  MP_TAC(ISPECL [`m:(real^(2,2)finite_sum->bool)->bool`;
                 `IMAGE (IMAGE moi_fcb_lift) (L:(real^2->bool)->bool)`;
                 `y:real^(2,2)finite_sum`] MOI_FN2_FRONTIER_NC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `sg:real^(2,2)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`; `x:real^2`]
      MOI_FN2_FRONTIER_NC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(sg:real^(2,2)finite_sum->bool) IN
                  IMAGE (IMAGE moi_fcb_lift) (barycentric_subdivision
                                                (barycentric_subdivision K))`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s0:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^(2,2)finite_sum) IN sg` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `~((sg:real^(2,2)finite_sum->bool) IN
                     derived_nbhd_complex m (IMAGE (IMAGE moi_fcb_lift) L))` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
      MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`; `s0:real^2->bool`]
        MOI_LCP_CAP_DNC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^2) IN derived_frontier K L` THEN
    MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`; `x:real^2`]
      MOI_FN2_FRONTIER_NC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s0:real^2->bool` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) s0` THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "m" THEN
      MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`; `s0:real^2->bool`]
        MOI_LCP_CAP_DNC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* Planar facts (Jordan curve theorem and PL Schoenflies for                *)
(* PL circles in the plane) and the transfer of PL circles through the lift *)
(* of pc_moi_fnd_cap.                                                        *)
(* ------------------------------------------------------------------------- *)

(* The open triangle (the same as MOI_LC1_OPEN_TRIANGLE of pc_moi_lt_case1, *)
(* outside this closure).                                                    *)

let MOI_LCP_OPEN_TRIANGLE = prove
 (`std_triangle DIFF relative_frontier std_triangle = interior std_triangle`,
  SUBGOAL_THEN `~(interior std_triangle = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `std_triangle` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DIMINDEX_2] THEN MATCH_MP_TAC AFF_DIM_SIMPLEX THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; GSYM RELATIVE_INTERIOR_NONEMPTY_INTERIOR] THEN
  SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC] THEN
  MP_TAC(ISPEC `std_triangle` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* PL circles in the plane (MOI_LCP_PL_SPHERE_1_HOMEOMORPHIC and            *)
(* MOI_LCP_JORDAN_DISK are the same as MOI_LA2_PL_SPHERE_1_HOMEOMORPHIC and  *)
(* MOI_LA2_JORDAN_DISK of pc_moi_lt_cuta2, not in this                       *)
(* closure).                                                                 *)

let MOI_LCP_PL_SPHERE_1_HOMEOMORPHIC = prove
 (`!j:real^2->bool. pl_sphere 1 j ==> j homeomorphic sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `relative_frontier k:real^2->bool`;
                 `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] RELATIVE_FRONTIER_CBALL) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  ASM_SIMP_TAC[CONVEX_CBALL; BOUNDED_CBALL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
                  ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_2]);;

let MOI_LCP_JORDAN_FACTS = prove
 (`!j:real^2->bool.
     pl_sphere 1 j
     ==> compact j /\ connected j /\ ~(j = {}) /\
         ~(inside j = {}) /\ open (inside j) /\ connected (inside j) /\
         ~(outside j = {}) /\ open (outside j) /\ connected (outside j) /\
         bounded (inside j) /\ ~bounded (outside j) /\
         inside j INTER outside j = {} /\
         inside j UNION outside j = (:real^2) DIFF j /\
         frontier (inside j) = j /\ frontier (outside j) = j /\
         inside j INTER j = {} /\ outside j INTER j = {} /\
         inside j IN components ((:real^2) DIFF j)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LCP_PL_SPHERE_1_HOMEOMORPHIC) THEN
  MP_TAC(ISPEC `j:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP; INSIDE_IN_COMPONENTS] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`j:real^2->bool`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    MP_TAC(ISPECL [`j:real^2->bool`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_CONNECTEDNESS) THEN
    ASM_REWRITE_TAC[CONNECTED_SPHERE_EQ; DIMINDEX_2; LE_REFL];
    DISCH_TAC THEN UNDISCH_TAC `~(inside j:real^2->bool = {})` THEN
    ASM_REWRITE_TAC[INSIDE_EMPTY]]);;

let MOI_LCP_JORDAN_DISK = prove
 (`!j:real^2->bool.
     pl_sphere 1 j
     ==> pl_cell_with_boundary 2 (j UNION inside j) j /\
         compact (j UNION inside j) /\ frontier (j UNION inside j) = j /\
         interior (j UNION inside j) = inside j /\ connected (j UNION inside j)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS) THEN
  SUBGOAL_THEN `frontier (j UNION inside j:real^2->bool) = j` ASSUME_TAC THENL
   [SUBGOAL_THEN `j UNION inside j:real^2->bool = (:real^2) DIFF outside j`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`inside j UNION outside j:real^2->bool = (:real^2) DIFF j`;
        `inside j INTER outside j:real^2->bool = {}`;
        `outside j INTER j:real^2->bool = {}`] THEN
      SET_TAC[];
      ASM_REWRITE_TAC[FRONTIER_COMPLEMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (j UNION inside j:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_WITH_INSIDE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior (j UNION inside j:real^2->bool) = inside j` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `j UNION inside j:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `frontier (j UNION inside j:real^2->bool) = j` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `j:real^2->bool` (REWRITE_RULE[PL_SCHOENFLIES_2_STATEMENT]
      PL_SCHOENFLIES_2)) THEN
    ASM_REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `p:real^2->real^2`
      (X_CHOOSE_THEN `q:real^2->real^2` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `p:real^2->real^2`; `q:real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier (j UNION inside j:real^2->bool) = j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_PL2_FRONTIER_PL_BALL_2 THEN
    EXISTS_TAC `q:real^2->real^2` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_WITH_INSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

(* The lift x |-> (x,0) of pc_moi_fnd_cap is a homeomorphism onto its image; *)
(* PL circles transfer both ways.                                            *)

let MOI_LCP_LIFT_HOMEO = prove
 (`!s:real^2->bool.
     homeomorphism (s,IMAGE moi_fcb_lift s) (moi_fcb_lift,fstcart) /\
     homeomorphism (IMAGE moi_fcb_lift s,s) (fstcart,moi_fcb_lift)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphism] THEN
  STRIP_ASSUME_TAC(INST_TYPE [`:2`,`:N`] MOI_FCB_LIFT) THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN
  REWRITE_TAC[ETA_AX]);;

let MOI_LCP_LIFT_SPHERE = prove
 (`!j:real^2->bool. pl_sphere 1 j ==> pl_sphere 1 (IMAGE moi_fcb_lift j)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`j:real^2->bool`; `IMAGE moi_fcb_lift (j:real^2->bool)`;
                       `moi_fcb_lift:real^2->real^(2,2)finite_sum`;
                       `fstcart:real^(2,2)finite_sum->real^2`; `1`]
                      MOI_FM3_PL_SPHERE_TRANSFER) THEN
  ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  REWRITE_TAC[MOI_LCP_LIFT_HOMEO] THEN
  STRIP_ASSUME_TAC(INST_TYPE [`:2`,`:N`] MOI_FCB_LIFT) THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `moi_fcb_lift:real^2->real^(2,2)finite_sum`;
                 `vec 0:real^(2,2)finite_sum`] PL_MAP_ON_AFFINE) THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_S4O_SPHERE_POLY] THEN
  TRY(ANTS_TAC THENL
   [ASM_MESON_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_S4O_SPHERE_POLY];
    ALL_TAC]) THEN
  REWRITE_TAC[VECTOR_ADD_RID; ETA_AX]);;

let MOI_LCP_UNLIFT_SPHERE = prove
 (`!c:real^(2,2)finite_sum->bool.
     pl_sphere 1 c /\ c SUBSET IMAGE moi_fcb_lift (:real^2)
     ==> pl_sphere 1 (IMAGE fstcart c) /\ IMAGE moi_fcb_lift (IMAGE fstcart c) = c`,
  GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(INST_TYPE [`:2`,`:N`] MOI_FCB_LIFT) THEN
  SUBGOAL_THEN `IMAGE moi_fcb_lift (IMAGE fstcart c) = c:real^(2,2)finite_sum->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`c:real^(2,2)finite_sum->bool`;
                       `IMAGE fstcart (c:real^(2,2)finite_sum->bool)`;
                       `fstcart:real^(2,2)finite_sum->real^2`;
                       `moi_fcb_lift:real^2->real^(2,2)finite_sum`; `1`]
                      MOI_FM3_PL_SPHERE_TRANSFER) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [MP_TAC(SPEC `IMAGE fstcart (c:real^(2,2)finite_sum->bool)` MOI_LCP_LIFT_HOMEO) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`c:real^(2,2)finite_sum->bool`; `fstcart:real^(2,2)finite_sum->real^2`;
                   `vec 0:real^2`] PL_MAP_ON_AFFINE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_S4O_SPHERE_POLY;
                    LINEAR_FSTCART];
      REWRITE_TAC[VECTOR_ADD_RID; ETA_AX]]]);;


(* ------------------------------------------------------------------------- *)
(* The derived neighbourhood of a PL circle L of K inside the               *)
(* open triangle, from MOI_FND_DERIVED_NBHD_POLYGON_2 on the cap; then the  *)
(* collars: the frontier is two PL circles, one inside and one outside      *)
(* (the inner one by a Borsuk-map argument with the deformation retraction  *)
(* of the neighbourhood onto the circle), and the outer circle bounds the   *)
(* union of the disk of the circle and its neighbourhood.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_NBHD_SUPERSET = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> UNIONS l SUBSET derived_nbhd t l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS (barycentric_subdivision (barycentric_subdivision t))`
  MP_TAC THENL
   [ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION; BARYCENTRIC_SUBDIVISION_LF] THEN
    UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) t` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

let MOI_LCP_LIFT_COMPONENTS = prove
 (`!A:real^2->bool.
     FINITE (components (IMAGE moi_fcb_lift A))
     ==> FINITE (components A) /\
         CARD (components A) = CARD (components (IMAGE moi_fcb_lift A)) /\
         components (IMAGE moi_fcb_lift A) = IMAGE (IMAGE moi_fcb_lift) (components A)`,
  X_GEN_TAC `A:real^2->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `A:real^2->bool` MOI_LCP_LIFT_HOMEO) THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (components (A:real^2->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(2,2)finite_sum->real^2`;
                   `moi_fcb_lift:real^2->real^(2,2)finite_sum`;
                   `IMAGE moi_fcb_lift (A:real^2->bool)`; `A:real^2->bool`]
                  MOI_LCP_COMPONENTS_HOMEO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fcb_lift:real^2->real^(2,2)finite_sum`;
                 `fstcart:real^(2,2)finite_sum->real^2`;
                 `A:real^2->bool`; `IMAGE moi_fcb_lift (A:real^2->bool)`]
                MOI_LCP_COMPONENTS_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_LCP_POLY2_K = prove
 (`!(K:(real^2->bool)->bool) L.
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_subcomplex L K /\
     pl_sphere 1 (UNIONS L) /\
     derived_nbhd K L SUBSET std_triangle DIFF relative_frontier std_triangle
     ==> FINITE (components (derived_frontier K L)) /\
         (CARD (components (derived_frontier K L)) = 1 \/
          CARD (components (derived_frontier K L)) = 2) /\
         (!c. c IN components (derived_frontier K L) ==> pl_sphere 1 c) /\
         FINITE (components (derived_nbhd K L DIFF UNIONS L)) /\
         CARD (components (derived_nbhd K L DIFF UNIONS L)) =
         CARD (components (derived_frontier K L))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (L:(real^2->bool)->bool) SUBSET
                std_triangle DIFF relative_frontier std_triangle`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `derived_nbhd K (L:(real^2->bool)->bool)` THEN
    ASM_SIMP_TAC[MOI_LCP_NBHD_SUPERSET];
    ALL_TAC] THEN
  ABBREV_TAC `FR = derived_frontier K (L:(real^2->bool)->bool)` THEN
  ABBREV_TAC `NB = derived_nbhd K L DIFF UNIONS (L:(real^2->bool)->bool)` THEN
  SUBGOAL_THEN
   `FINITE (components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) FR)) /\
    (CARD (components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) FR)) = 1 \/
     CARD (components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) FR)) = 2) /\
    (!k. k IN components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) FR)
         ==> pl_sphere 1 k) /\
    FINITE (components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) NB)) /\
    CARD (components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) NB)) =
    CARD (components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) FR))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`] MOI_LCP_CAP_NBHD) THEN
    MP_TAC(ISPEC `K:(real^2->bool)->bool` MOI_LCP_CAP_SETUP) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `m = moi_fcb_cap (K:(real^2->bool)->bool) (\P:real^2->bool. 0)` THEN
    STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) NB =
      derived_nbhd m (IMAGE (IMAGE moi_fcb_lift) L) DIFF
      UNIONS (IMAGE (IMAGE moi_fcb_lift) (L:(real^2->bool)->bool))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "NB" THEN
      MATCH_MP_TAC IMAGE_DIFF_INJ THEN MESON_TAC[MOI_FCB_LIFT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) FR =
      derived_frontier m (IMAGE (IMAGE moi_fcb_lift) (L:(real^2->bool)->bool))`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `FINITE (components (derived_nbhd m (IMAGE (IMAGE moi_fcb_lift) L) DIFF
                          UNIONS (IMAGE (IMAGE moi_fcb_lift) (L:(real^2->bool)->bool))))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`m:(real^(2,2)finite_sum->bool)->bool`;
                     `IMAGE (IMAGE moi_fcb_lift) (L:(real^2->bool)->bool)`]
                    MOI_FN2_COMPONENTS_NL) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[MOI_LCP_LIFT_SPHERE]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `barycentric_subdivision (m:(real^(2,2)finite_sum->bool)->bool)` THEN
      ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[moi_frn_vp];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^(2,2)finite_sum->bool)->bool`;
                   `IMAGE (IMAGE moi_fcb_lift) (L:(real^2->bool)->bool)`]
                  DERIVED_NBHD_POLYGON_2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[MOI_LCP_LIFT_SPHERE]; ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
           DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      STRIP_ASSUME_TAC))] THEN
  MP_TAC(SPEC `FR:real^2->bool` MOI_LCP_LIFT_COMPONENTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC `NB:real^2->bool` MOI_LCP_LIFT_COMPONENTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_MESON_TAC[];
    ALL_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_MESON_TAC[]] THEN
  X_GEN_TAC `c:real^2->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) c)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match []
        `!k. k IN components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) s)
             ==> pl_sphere 1 k`)
          (concl th))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) &&
      lhs(concl th) = `components (IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) FR)`))
    THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (moi_fcb_lift:real^2->real^(2,2)finite_sum) c`
    MOI_LCP_UNLIFT_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[MOI_FCB_LIFT; IMAGE_ID] THEN SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Planar collars.  For a PL circle j in the plane with a                    *)
(* compact neighbourhood nb retracting onto j, whose frontier fr = nb DIFF u *)
(* (u open) has one or two PL circle components, as many as nb DIFF j:      *)
(* fr is one circle jm inside j and one circle jp outside j, nb meets each  *)
(* side of j in a connected set, and the disk of j together with nb is the  *)
(* disk of jp.                                                               *)
(* ------------------------------------------------------------------------- *)

(* A PL circle is not a retract of a set containing its inside (Borsuk).    *)

let MOI_LCP_BORSUK_RETRACT = prove
 (`!(j:real^2->bool) nb r.
     pl_sphere 1 j /\ retraction (nb,j) r ==> ~(inside j SUBSET nb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [retraction]) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `a:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(inside j:real^2->bool = {})`)) THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `inside j:real^2->bool`; `a:real^2`]
    NON_EXTENSIBLE_BORSUK_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(\x. inv(norm(x - a)) % (x - a)) o (r:real^2->real^2)` THEN
  SUBGOAL_THEN `~((a:real^2) IN j)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (r:real^2->real^2) (j UNION inside j) SUBSET j` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `nb:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_BORSUK_MAP THEN ASM SET_TAC[]];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (\x. inv(norm(x - a)) % (x - a)) (j:real^2->bool)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET; BORSUK_MAP_INTO_SPHERE];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]]);;

(* A clopen piece of a connected open set. *)

let MOI_LCP_CLOPEN_SIDE = prove
 (`!s u nb p:real^N->bool.
     connected s /\ open s /\ open u /\ closed nb /\ u SUBSET nb /\
     p = nb INTER s /\ p SUBSET u
     ==> p = {} \/ p = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (s:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `p:real^N->bool = s INTER (u INTER s)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER];
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]]);;

(* The region bounded by the outer circle. *)

let MOI_LCP_REGION = prove
 (`!(j:real^2->bool) jm jp nb u.
     pl_sphere 1 j /\ pl_sphere 1 jp /\ compact nb /\ open u /\
     j SUBSET u /\ u SUBSET nb /\ nb DIFF u = jm UNION jp /\
     jm SUBSET inside j /\ jp SUBSET outside j
     ==> (j UNION inside j) UNION nb = jp UNION inside jp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS o check (fun th ->
    concl th = `pl_sphere 1 (j:real^2->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_DISK o check (fun th ->
    concl th = `pl_sphere 1 (j:real^2->bool)`)) THEN
  MP_TAC(ISPEC `jp:real^2->bool` MOI_LCP_JORDAN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `V = inside j UNION (u:real^2->bool)` THEN
  SUBGOAL_THEN `(j UNION inside j) UNION nb = (V:real^2->bool) UNION jp /\
                DISJOINT V (jp:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open (V:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_SIMP_TAC[OPEN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `closed ((V:real^2->bool) UNION jp)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `(V:real^2->bool) UNION jp`)) THEN
    MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (V:real^2->bool) SUBSET V UNION jp` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded (V:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[BOUNDED_UNION] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `nb:real^2->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  (* V misses the outside of jp *)
  SUBGOAL_THEN `(V:real^2->bool) INTER outside jp = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`outside jp:real^2->bool`; `V:real^2->bool`;
                   `V UNION jp:real^2->bool`; `(V:real^2->bool) INTER outside jp`]
      MOI_LCP_CLOPEN_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_UNION] THEN
      UNDISCH_TAC `outside jp INTER jp:real^2->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~bounded (outside jp:real^2->bool)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `V:real^2->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `V:real^2->bool = inside jp` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`inside jp:real^2->bool`; `V:real^2->bool`;
                   `V UNION jp:real^2->bool`; `(V:real^2->bool) INTER inside jp`]
      MOI_LCP_CLOPEN_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_UNION] THEN
      UNDISCH_TAC `inside jp INTER jp:real^2->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(V:real^2->bool) INTER inside jp = V` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(V:real^2->bool) INTER outside jp = {}`; `DISJOINT (V:real^2->bool) jp`;
        `inside jp UNION outside jp:real^2->bool = (:real^2) DIFF jp`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(V:real^2->bool) = {}` THEN EXPAND_TAC "V" THEN
    ASM_REWRITE_TAC[EMPTY_UNION];
    SET_TAC[]]);;

(* A connected set missing s lies inside or outside s (the same as         *)
(* MOI_LA2_CONNECTED_SIDE of pc_moi_lt_cuta2, outside this closure).        *)

let MOI_LCP_CONNECTED_SIDE = prove
 (`!s t:real^N->bool.
     connected t /\ DISJOINT s t ==> t SUBSET inside s \/ t SUBSET outside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
    INSIDE_OUTSIDE_INTERSECT_CONNECTED) THEN
  MP_TAC(ISPEC `s:real^N->bool` INSIDE_UNION_OUTSIDE) THEN
  ASM SET_TAC[]);;

let MOI_LCP_PLANAR_COLLARS = prove
 (`!(nb:real^2->bool) fr u j.
     pl_sphere 1 j /\ compact nb /\ open u /\ j SUBSET u /\ u SUBSET nb /\
     fr = nb DIFF u /\ (?r. retraction (nb,j) r) /\
     FINITE (components fr) /\ CARD (components fr) <= 2 /\
     (!c. c IN components fr ==> pl_sphere 1 c) /\
     FINITE (components (nb DIFF j)) /\
     CARD (components (nb DIFF j)) = CARD (components fr)
     ==> ?jm jp. pl_sphere 1 jm /\ pl_sphere 1 jp /\ DISJOINT jm jp /\
                 fr = jm UNION jp /\ jm SUBSET inside j /\ jp SUBSET outside j /\
                 connected (nb INTER inside j) /\ connected (nb INTER outside j) /\
                 (j UNION inside j) UNION nb = jp UNION inside jp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(fr:real^2->bool) SUBSET nb /\ fr INTER u = {} /\ nb SUBSET u UNION fr`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `fr:real^2->bool = nb DIFF u` THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `fr:real^2->bool = nb DIFF u`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS) THEN
  SUBGOAL_THEN `closed (nb:real^2->bool) /\ bounded (nb:real^2->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  (* both sides meet nb *)
  SUBGOAL_THEN `!S:real^2->bool. frontier S = j ==> ~(nb INTER S = {})` ASSUME_TAC THENL
   [X_GEN_TAC `S:real^2->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `x:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(j:real^2->bool = {})`)) THEN
    SUBGOAL_THEN `(x:real^2) IN closure S` ASSUME_TAC THENL
     [UNDISCH_TAC `frontier S = (j:real^2->bool)` THEN REWRITE_TAC[frontier] THEN
      UNDISCH_TAC `(x:real^2) IN j` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((u:real^2->bool) INTER closure S = {})` MP_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(j:real^2->bool) SUBSET u` THEN UNDISCH_TAC `(x:real^2) IN j` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN
    UNDISCH_TAC `(u:real^2->bool) SUBSET nb` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((nb:real^2->bool) INTER inside j = {}) /\ ~(nb INTER outside j = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the components of nb DIFF j lie on one side each *)
  SUBGOAL_THEN
   `!C. C IN components (nb DIFF j)
        ==> C SUBSET inside j \/ C SUBSET outside (j:real^2->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCP_CONNECTED_SIDE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x1:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~((nb:real^2->bool) INTER inside j = {})`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x2:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~((nb:real^2->bool) INTER outside j = {})`)) THEN
  SUBGOAL_THEN `(x1:real^2) IN nb DIFF j /\ (x2:real^2) IN nb DIFF j` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x1:real^2) IN nb INTER inside j`; `(x2:real^2) IN nb INTER outside j`;
      `inside j INTER j:real^2->bool = {}`; `outside j INTER j:real^2->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C1 = connected_component (nb DIFF j) (x1:real^2)` THEN
  ABBREV_TAC `C2 = connected_component (nb DIFF j) (x2:real^2)` THEN
  SUBGOAL_THEN `(C1:real^2->bool) IN components (nb DIFF j) /\
                (C2:real^2->bool) IN components (nb DIFF j) /\
                (x1:real^2) IN C1 /\ (x2:real^2) IN C2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C1"; "C2"] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C1:real^2->bool) SUBSET inside j /\ (C2:real^2->bool) SUBSET outside j`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!C. C IN components (nb DIFF j)
          ==> C SUBSET inside j \/ C SUBSET outside (j:real^2->bool)`
    (fun th -> MP_TAC(MATCH_MP th (ASSUME `(C1:real^2->bool) IN components (nb DIFF j)`)) THEN
               MP_TAC(MATCH_MP th (ASSUME `(C2:real^2->bool) IN components (nb DIFF j)`)))
    THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x1:real^2) IN C1`; `(x1:real^2) IN nb INTER inside j`;
      `(x2:real^2) IN C2`; `(x2:real^2) IN nb INTER outside j`;
      `inside j INTER outside j:real^2->bool = {}`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(C1:real^2->bool = C2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(C1:real^2->bool) = C2`; `(x1:real^2) IN C1`; `(C2:real^2->bool) SUBSET outside j`;
      `(x1:real^2) IN nb INTER inside j`;
      `inside j INTER outside j:real^2->bool = {}`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {C1:real^2->bool,C2} = 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `components (nb DIFF j) = {C1:real^2->bool,C2}` ASSUME_TAC THENL
   [MATCH_MP_TAC(GSYM CARD_SUBSET_EQ) THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `CARD {C1:real^2->bool,C2} = 2`)) THEN
      MATCH_MP_TAC(ARITH_RULE `2 <= n /\ n <= 2 ==> n = 2`) THEN CONJ_TAC THENL
       [SUBGOAL_THEN `CARD {C1:real^2->bool,C2} <= CARD (components (nb DIFF j:real^2->bool))`
        MP_TAC THENL
         [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
          ASM_REWRITE_TAC[]];
        UNDISCH_TAC `CARD (components (nb DIFF j:real^2->bool)) =
                     CARD (components (fr:real^2->bool))` THEN
        DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (components (fr:real^2->bool)) = 2` ASSUME_TAC THENL
   [UNDISCH_TAC `CARD (components (nb DIFF j:real^2->bool)) =
                 CARD (components (fr:real^2->bool))` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(nb:real^2->bool) INTER inside j = C1 /\ nb INTER outside j = C2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `nb DIFF j:real^2->bool` UNIONS_COMPONENTS) THEN
    ASM_REWRITE_TAC[UNIONS_2] THEN
    MAP_EVERY UNDISCH_TAC
     [`(C1:real^2->bool) SUBSET inside j`; `(C2:real^2->bool) SUBSET outside j`;
      `inside j INTER outside j:real^2->bool = {}`;
      `inside j INTER j:real^2->bool = {}`; `outside j INTER j:real^2->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the frontier meets both sides *)
  SUBGOAL_THEN `(fr:real^2->bool) SUBSET nb DIFF j` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(fr:real^2->bool) SUBSET nb`; `(fr:real^2->bool) INTER u = {}`;
      `(j:real^2->bool) SUBSET u`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!S:real^2->bool. connected S /\ open S /\ fr INTER S = {}
                     ==> nb INTER S = {} \/ nb INTER S = S`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^2->bool`; `u:real^2->bool`; `nb:real^2->bool`;
                   `(nb:real^2->bool) INTER S`] MOI_LCP_CLOPEN_SIDE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(nb:real^2->bool) SUBSET u UNION fr`; `(fr:real^2->bool) INTER S = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((fr:real^2->bool) INTER inside j = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inside j:real^2->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(nb:real^2->bool) INTER inside j = C1`] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [UNDISCH_TAC `(x1:real^2) IN C1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      MP_TAC(ISPECL [`j:real^2->bool`; `nb:real^2->bool`; `r:real^2->real^2`]
        MOI_LCP_BORSUK_RETRACT) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(nb:real^2->bool) INTER inside j = C1` THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((fr:real^2->bool) INTER outside j = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `outside j:real^2->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(nb:real^2->bool) INTER outside j = C2`] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [UNDISCH_TAC `(x2:real^2) IN C2` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      UNDISCH_TAC `~bounded (outside j:real^2->bool)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `nb:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(nb:real^2->bool) INTER outside j = C2` THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the two frontier circles *)
  SUBGOAL_THEN `?D1 D2:real^2->bool. ~(D1 = D2) /\ components fr = {D1,D2}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(HAS_SIZE_CONV `(components (fr:real^2->bool)) HAS_SIZE 2`) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 1 (D1:real^2->bool) /\ pl_sphere 1 (D2:real^2->bool) /\
    DISJOINT D1 D2 /\ fr = D1 UNION D2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
      REWRITE_TAC[DISJOINT] THEN
      MP_TAC(ISPECL [`fr:real^2->bool`; `D1:real^2->bool`; `D2:real^2->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[IN_INSERT];
      MP_TAC(ISPEC `fr:real^2->bool` UNIONS_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!D:real^2->bool. pl_sphere 1 D /\ D SUBSET fr
                     ==> D SUBSET inside j \/ D SUBSET outside j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCP_CONNECTED_SIDE THEN
    ASM_SIMP_TAC[MOI_S4O_SPHERE1_CONNECTED] THEN
    MAP_EVERY UNDISCH_TAC
     [`(D:real^2->bool) SUBSET fr`; `(fr:real^2->bool) SUBSET nb DIFF j`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!jm jp:real^2->bool.
      pl_sphere 1 jm /\ pl_sphere 1 jp /\ DISJOINT jm jp /\ fr = jm UNION jp /\
      jm SUBSET inside j /\ jp SUBSET outside j
      ==> ?jm jp. pl_sphere 1 jm /\ pl_sphere 1 jp /\ DISJOINT jm jp /\
                  fr = jm UNION jp /\ jm SUBSET inside j /\ jp SUBSET outside j /\
                  connected (nb INTER inside j) /\ connected (nb INTER outside j) /\
                  (j UNION inside j) UNION nb = jp UNION inside jp`
  MATCH_MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`jm:real^2->bool`; `jp:real^2->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[ASSUME `(nb:real^2->bool) INTER inside j = C1`] THEN
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      REWRITE_TAC[ASSUME `(nb:real^2->bool) INTER outside j = C2`] THEN
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      MATCH_MP_TAC(ISPECL [`j:real^2->bool`; `jm:real^2->bool`; `jp:real^2->bool`;
                           `nb:real^2->bool`; `u:real^2->bool`] MOI_LCP_REGION) THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MAP_EVERY UNDISCH_TAC
       [`fr:real^2->bool = jm UNION jp`; `(fr:real^2->bool) SUBSET nb`;
        `(fr:real^2->bool) INTER u = {}`; `(nb:real^2->bool) SUBSET u UNION fr`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D1:real^2->bool) SUBSET fr /\ (D2:real^2->bool) SUBSET fr`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((D1:real^2->bool) SUBSET inside j \/ D1 SUBSET outside j) /\
    ((D2:real^2->bool) SUBSET inside j \/ D2 SUBSET outside j)`
  MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~((fr:real^2->bool) INTER outside j = {})`; `fr:real^2->bool = D1 UNION D2`;
      `(D1:real^2->bool) SUBSET inside j`; `(D2:real^2->bool) SUBSET inside j`;
      `inside j INTER outside j:real^2->bool = {}`] THEN SET_TAC[];
    MAP_EVERY EXISTS_TAC [`D1:real^2->bool`; `D2:real^2->bool`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY EXISTS_TAC [`D2:real^2->bool`; `D1:real^2->bool`] THEN
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC
     [`~((fr:real^2->bool) INTER inside j = {})`; `fr:real^2->bool = D1 UNION D2`;
      `(D1:real^2->bool) SUBSET outside j`; `(D2:real^2->bool) SUBSET outside j`;
      `inside j INTER outside j:real^2->bool = {}`] THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The collars of a PL circle j = UNIONS L of K inside the                   *)
(* open triangle (MOI_LCP_PLANAR_COLLARS with u the interior of the derived *)
(* neighbourhood in the triangle, open in the plane, and the retraction of  *)
(* DERIVED_NBHD_DEFORMATION_RETRACT).                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_NBHD_INTERIOR = prove
 (`!(K:(real^2->bool)->bool) L.
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_subcomplex L K /\
     derived_nbhd K L SUBSET std_triangle DIFF relative_frontier std_triangle
     ==> compact (derived_nbhd K L) /\
         open ((subtopology euclidean std_triangle) interior_of (derived_nbhd K L)) /\
         (subtopology euclidean std_triangle) interior_of (derived_nbhd K L) SUBSET
         derived_nbhd K L /\
         derived_frontier K L =
         derived_nbhd K L DIFF
         (subtopology euclidean std_triangle) interior_of (derived_nbhd K L) /\
         UNIONS L SUBSET
         (subtopology euclidean std_triangle) interior_of (derived_nbhd K L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (derived_nbhd K (L:(real^2->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_DERIVED_NBHD_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `u = (subtopology euclidean std_triangle) interior_of
                  (derived_nbhd K (L:(real^2->bool)->bool))` THEN
  SUBGOAL_THEN `(u:real^2->bool) SUBSET derived_nbhd K L` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[INTERIOR_OF_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `open_in (subtopology euclidean std_triangle) (u:real^2->bool)` MP_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[OPEN_IN_INTERIOR_OF]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `u:real^2->bool = V INTER interior std_triangle` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MOI_LCP_OPEN_TRIANGLE] THEN
      MAP_EVERY UNDISCH_TAC
       [`u:real^2->bool = std_triangle INTER V`; `(u:real^2->bool) SUBSET derived_nbhd K L`;
        `derived_nbhd K (L:(real^2->bool)->bool) SUBSET
         std_triangle DIFF relative_frontier std_triangle`] THEN
      SET_TAC[];
      ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR]];
    REWRITE_TAC[derived_frontier; frontier_of] THEN
    ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CLOSURE_OF_CLOSED_IN THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    ASM SET_TAC[];
    EXPAND_TAC "u" THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> concl th =
      `UNIONS (K:(real^2->bool)->bool) = std_triangle`)) THEN
    MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`; `x:real^2`]
      MOI_FN2_INTERIOR_NC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`]
        MOI_LCP_NBHD_SUPERSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC FACE_OF_REFL THEN
        SUBGOAL_THEN `simplicial_complex (barycentric_subdivision
                        (barycentric_subdivision (K:(real^2->bool)->bool)))` MP_TAC THENL
         [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
        REWRITE_TAC[simplicial_complex] THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]]]]);;

let MOI_LCP_COLLARS = prove
 (`!(K:(real^2->bool)->bool) L j.
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_subcomplex L K /\
     UNIONS L = j /\ pl_sphere 1 j /\
     derived_nbhd K L SUBSET std_triangle DIFF relative_frontier std_triangle
     ==> ?jm jp. pl_sphere 1 jm /\ pl_sphere 1 jp /\ DISJOINT jm jp /\
                 derived_frontier K L = jm UNION jp /\
                 jm SUBSET inside j /\ jp SUBSET outside j /\
                 connected (derived_nbhd K L INTER inside j) /\
                 connected (derived_nbhd K L INTER outside j) /\
                 (j UNION inside j) UNION derived_nbhd K L = jp UNION inside jp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `UNIONS (L:(real^2->bool)->bool) = j`)) THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`]
    MOI_LCP_NBHD_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = (subtopology euclidean std_triangle) interior_of
                  (derived_nbhd K (L:(real^2->bool)->bool))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`] MOI_LCP_POLY2_K) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_LCP_PLANAR_COLLARS THEN EXISTS_TAC `u:real^2->bool` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THENL
   [MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L:(real^2->bool)->bool`]
      DERIVED_NBHD_DEFORMATION_RETRACT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
    MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th))) THEN ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The pullback of derived frontiers (companion of                           *)
(* MOI_LCP_NBHD_PULLBACK): under the same condition (U), a point lies over   *)
(* the derived frontier of L in the image complex iff it lies in the        *)
(* derived frontier of the pulled-back subcomplex.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_SC_SUBSET_FACE = prove
 (`!(m:(real^N->bool)->bool) s t.
     lf_simplicial_complex m /\ s IN m /\ t IN m /\ s SUBSET t ==> s face_of t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s:real^N->bool = s INTER t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lf_simplicial_complex (m:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `t:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;

let MOI_LCP_PULLBACK_SUBCOMPLEX = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f L.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     simplicial_subcomplex L (IMAGE (IMAGE f) k)
     ==> simplicial_subcomplex {s | s IN k /\ IMAGE f s IN L} k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
    MOI_LNS_IMAGE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (IMAGE (IMAGE (f:real^M->real^N)) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX]; ALL_TAC] THEN
  REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
  SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^M->bool) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `simplicial_subcomplex L (IMAGE (IMAGE (f:real^M->real^N)) k)` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_LCP_SC_SUBSET_FACE THEN
  EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) k` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]);;

let MOI_LCP_FRONTIER_PULLBACK = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f L.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f /\
     (!s x x'. s IN k /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
     simplicial_subcomplex L (IMAGE (IMAGE f) k) /\
     (!x x'. x IN UNIONS k /\ x' IN UNIONS k /\ f x = f x' /\
             f x IN derived_nbhd (IMAGE (IMAGE f) k) L /\ ~(f x IN UNIONS L)
             ==> x = x')
     ==> {x | x IN UNIONS k /\ f x IN derived_frontier (IMAGE (IMAGE f) k) L} =
         derived_frontier k {s | s IN k /\ IMAGE f s IN L}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`;
                 `L:(real^N->bool)->bool`] MOI_LCP_NBHD_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`;
                 `L:(real^N->bool)->bool`] MOI_LCP_PREIMAGE_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`;
                 `L:(real^N->bool)->bool`] MOI_LCP_PULLBACK_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
    MOI_LCP_SD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `f:real^M->real^N`]
    MOI_LNS_IMAGE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `X = IMAGE (IMAGE (f:real^M->real^N)) k` THEN
  ABBREV_TAC `KL = {s:real^M->bool | s IN k /\ IMAGE (f:real^M->real^N) s IN L}` THEN
  SUBGOAL_THEN `lf_simplicial_complex (X:(real^N->bool)->bool) /\
                lf_simplicial_complex (k:(real^M->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX; MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision
                             (X:(real^N->bool)->bool))) /\
    lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision
                             (k:(real^M->bool)->bool)))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. x IN UNIONS k /\ (f:real^M->real^N) x IN UNIONS L <=>
                           x IN UNIONS KL` ASSUME_TAC THENL
   [UNDISCH_TAC `{x:real^M | x IN UNIONS k /\ (f:real^M->real^N) x IN UNIONS L} =
                 UNIONS KL` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (KL:(real^M->bool)->bool) SUBSET UNIONS k` ASSUME_TAC THENL
   [EXPAND_TAC "KL" THEN SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`X:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `(f:real^M->real^N) x`] MOI_FN2_FRONTIER_NC) THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `KL:(real^M->bool)->bool`; `x:real^M`]
    MOI_FN2_FRONTIER_NC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_CASES_TAC `(x:real^M) IN UNIONS k` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    UNDISCH_TAC `~((x:real^M) IN UNIONS k)` THEN
    MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> ~(b /\ c)`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `derived_nbhd (k:(real^M->bool)->bool) KL`)) (rhs(concl th)))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]] THEN
  SUBGOAL_THEN `(f:real^M->real^N) x IN derived_nbhd X L <=> x IN derived_nbhd k KL`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `derived_nbhd (k:(real^M->bool)->bool) KL`)) (rhs(concl th)))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^M) IN derived_nbhd k KL` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:real^M->real^N) x IN derived_nbhd X L` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^M) IN derived_nbhd k KL` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `derived_nbhd (k:(real^M->bool)->bool) KL`)) (rhs(concl th)))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* double points over the neighbourhood lie over L *)
  SUBGOAL_THEN
   `!z z'. z IN UNIONS k /\ z' IN UNIONS k /\ (f:real^M->real^N) z = f z' /\
           f z IN derived_nbhd X L /\ ~(z = z')
           ==> z IN UNIONS KL /\ z' IN UNIONS KL`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) z IN UNIONS L` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?s:real^M->bool. s IN barycentric_subdivision (barycentric_subdivision k) /\
                                  (s':real^N->bool) = IMAGE (f:real^M->real^N) s`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(s':real^N->bool) IN barycentric_subdivision (barycentric_subdivision X)` THEN
      UNDISCH_TAC `IMAGE (IMAGE (f:real^M->real^N))
                     (barycentric_subdivision (barycentric_subdivision k)) =
                   barycentric_subdivision (barycentric_subdivision X)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (f:real^M->real^N) s INTER UNIONS L = {}` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~(IMAGE (f:real^M->real^N) s IN derived_nbhd_complex X L)` THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN
      UNDISCH_TAC `lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision
                     (X:(real^N->bool)->bool)))` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^M->real^N) s` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(f:real^M->real^N) x IN IMAGE f s` THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':real^M` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `x:real^M = x'` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `x':real^M`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `UNIONS (KL:(real^M->bool)->bool)`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^M->real^N) x IN UNIONS L` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      UNDISCH_TAC `~(IMAGE (f:real^M->real^N) s IN derived_nbhd_complex X L)` THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM; CONTRAPOS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (f:real^M->real^N) r` THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (IMAGE (f:real^M->real^N))
                       (barycentric_subdivision (barycentric_subdivision k)) =
                     barycentric_subdivision (barycentric_subdivision X)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(r INTER UNIONS (KL:(real^M->bool)->bool) = {})` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `(f:real^M->real^N) w` THEN CONJ_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[SUBSET]];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_LCP_SC_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (X:(real^N->bool)->bool))` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [UNDISCH_TAC `IMAGE (IMAGE (f:real^M->real^N))
                       (barycentric_subdivision (barycentric_subdivision k)) =
                     barycentric_subdivision (barycentric_subdivision X)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]];
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (IMAGE (f:real^M->real^N))
                     (barycentric_subdivision (barycentric_subdivision k)) =
                   barycentric_subdivision (barycentric_subdivision X)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* s misses UNIONS KL *)
    SUBGOAL_THEN `s INTER UNIONS (KL:(real^M->bool)->bool) = {}` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((s:real^M->bool) IN derived_nbhd_complex k KL)` THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    UNDISCH_TAC `~((s:real^M->bool) IN derived_nbhd_complex k KL)` THEN
    REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM; CONTRAPOS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?r:real^M->bool. r IN barycentric_subdivision (barycentric_subdivision k) /\
                                  (r':real^N->bool) = IMAGE (f:real^M->real^N) r`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(r':real^N->bool) IN barycentric_subdivision (barycentric_subdivision X)` THEN
      UNDISCH_TAC `IMAGE (IMAGE (f:real^M->real^N))
                     (barycentric_subdivision (barycentric_subdivision k)) =
                   barycentric_subdivision (barycentric_subdivision X)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `r:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^M->bool) SUBSET UNIONS k /\ r SUBSET UNIONS k` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f:real^M->real^N) r SUBSET derived_nbhd X L` ASSUME_TAC THENL
     [REWRITE_TAC[derived_nbhd] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN t ==> s SUBSET UNIONS t`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^M->bool) SUBSET r` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^M->real^N) z IN IMAGE f r` MP_TAC THENL
       [SUBGOAL_THEN `IMAGE (f:real^M->real^N) s SUBSET IMAGE f r` MP_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ASM SET_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z':real^M` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `z:real^M = z'` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^M`; `z':real^M`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `UNIONS (KL:(real^M->bool)->bool)`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~(r' INTER UNIONS (L:(real^N->bool)->bool) = {})` THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `w:real^M` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
        can (term_match [] `!x:real^M. x IN UNIONS k /\ P x <=> x IN UNIONS KL`)
            (concl th))) THEN
      ASM_MESON_TAC[SUBSET];
      MATCH_MP_TAC MOI_LCP_SC_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (k:(real^M->bool)->bool))` THEN
      ASM_REWRITE_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* The source subcomplexes.  The simplices of K inside a set                *)
(* form a subcomplex; the preimage of a component of the double image, and  *)
(* the disk of a polygon that is a subcomplex, are unions of simplices.     *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_SUB_IN = prove
 (`!(K:(real^N->bool)->bool) A.
     lf_simplicial_complex K ==> simplicial_subcomplex {s | s IN K /\ s SUBSET A} K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
  SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]]);;

(* The preimage of a component k of the double image is a union of          *)
(* simplices of K (paired simplices map into the double image, connected).  *)

let MOI_LCP_COMPONENT_UNIONS = prove
 (`!(K:(real^2->bool)->bool) (t:(real^N->bool)->bool) f k.
     simplicial_complex K /\ UNIONS K = std_triangle /\ lf_simplicial_complex t /\
     simplicial_map_on K t f /\
     (!x. x IN std_triangle
          ==> ?n. open n /\ x IN n /\
                  !a b. a IN n INTER std_triangle /\ b IN n INTER std_triangle /\
                        f a = f b ==> a = b) /\
     k IN components (moi_lt_double_image f)
     ==> {x | x IN std_triangle /\ f x IN k} =
         UNIONS {s | s IN K /\ s SUBSET {x | x IN std_triangle /\ f x IN k}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`]
    MOI_LCP_DOUBLE_SIMPLICES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}`
  MP_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) s SUBSET moi_lt_double_image f` ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [th]) o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `moi_lt_double_image (f:real^2->real^N)`)) THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN t ==> s SUBSET UNIONS t`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real^2->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) s SUBSET k` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `moi_lt_double_image (f:real^2->real^N)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [UNDISCH_TAC `simplicial_map_on K t (f:real^2->real^N)` THEN
        REWRITE_TAC[simplicial_map_on] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
          STRIP_ASSUME_TAC) o CONJUNCT2) THEN
        MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC `\x:real^2. (l:real^2->real^N) x + y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(f:real^2->real^N) x` THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]);;

(* The closed disk of a polygon that is a subcomplex is a union of simplices. *)

let MOI_LCP_DISK_UNIONS = prove
 (`!(K:(real^2->bool)->bool) L j.
     simplicial_complex K /\ simplicial_subcomplex L K /\ UNIONS L = j /\
     pl_sphere 1 j /\ j UNION inside j SUBSET UNIONS K
     ==> j UNION inside j = UNIONS {s | s IN K /\ s SUBSET j UNION inside j}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_DISK) THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `(L:(real^2->bool)->bool) SUBSET K` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN j` THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> concl th = `UNIONS (L:(real^2->bool)->bool) = j`)) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(s:real^2->bool) IN L`; `(L:(real^2->bool)->bool) SUBSET K`;
      `UNIONS (L:(real^2->bool)->bool) = j`] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `x:real^2`] MOI_LCP_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j UNION inside j SUBSET UNIONS (K:(real^2->bool)->bool)` THEN
    UNDISCH_TAC `(x:real^2) IN inside j` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex (s:real^2->bool) /\ closed s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
  SUBGOAL_THEN `DISJOINT j (relative_interior s:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^2) IN j` THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> concl th = `UNIONS (L:(real^2->bool)->bool) = j`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^2->bool) SUBSET s0` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`K:(real^2->bool)->bool`; `z:real^2`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN j` MP_TAC THENL
     [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
        check (fun th -> concl th = `UNIONS (L:(real^2->bool)->bool) = j`)) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s0:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      UNDISCH_TAC `(x:real^2) IN inside j` THEN
      UNDISCH_TAC `inside j INTER j:real^2->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `relative_interior s:real^2->bool`]
    MOI_LCP_CONNECTED_SIDE) THEN
  ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR; CONVEX_CONNECTED] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:real^2) IN relative_interior s` THEN
    UNDISCH_TAC `(x:real^2) IN inside j` THEN
    UNDISCH_TAC `relative_interior s SUBSET outside (j:real^2->bool)` THEN
    UNDISCH_TAC `inside j INTER outside j:real^2->bool = {}` THEN SET_TAC[]] THEN
  SUBGOAL_THEN `(s:real^2->bool) SUBSET j UNION inside j` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (relative_interior s:real^2->bool)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_SUBSET];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `relative_interior s SUBSET inside (j:real^2->bool)` THEN SET_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNION]]);;


(* ------------------------------------------------------------------------- *)
(* Small facts on derived neighbourhoods and frontiers: they                *)
(* depend on UNIONS l only, are additive in l, lie in the closed star of    *)
(* l; frontiers of disjoint closed unions; interiors and frontiers in the   *)
(* triangle of sets in the open triangle.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_NBHD_UNIONS_EQ = prove
 (`!(t:(real^N->bool)->bool) l l'.
     UNIONS l = UNIONS l'
     ==> derived_nbhd t l = derived_nbhd t l' /\
         derived_frontier t l = derived_frontier t l'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `derived_nbhd (t:(real^N->bool)->bool) l = derived_nbhd t l'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[derived_nbhd]; ASM_REWRITE_TAC[derived_frontier]]);;

let MOI_LCP_NBHD_UNION = prove
 (`!(t:(real^N->bool)->bool) l1 l2.
     derived_nbhd t (l1 UNION l2) = derived_nbhd t l1 UNION derived_nbhd t l2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[derived_nbhd; UNIONS_UNION] THEN
  REWRITE_TAC[SET_RULE `~((s:real^N->bool) INTER (a UNION b) = {}) <=>
                        ~(s INTER a = {}) \/ ~(s INTER b = {})`] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_LCP_NBHD_IN_STAR = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t
     ==> derived_nbhd t l SUBSET UNIONS {s | s IN t /\ ~(s INTER UNIONS l = {})}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[derived_nbhd; UNIONS_SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `barycentric_subdivision (t:(real^N->bool)->bool)`
    BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `r1:real^N->bool` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE `!q. r SUBSET q /\ q IN f ==> (r:real^N->bool) SUBSET UNIONS f`) THEN
  EXISTS_TAC `r2:real^N->bool` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]]);;

let MOI_LCP_FRONTIER_OF_DISJOINT_UNION = prove
 (`!top a b:A->bool.
     closed_in top a /\ closed_in top b /\ DISJOINT a b
     ==> top frontier_of (a UNION b) = top frontier_of a UNION top frontier_of b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of] THEN
  ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN; CLOSED_IN_UNION] THEN
  SUBGOAL_THEN `top interior_of (a UNION b:A->bool) =
                top interior_of a UNION top interior_of b`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:A` THEN DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(x:A) IN a` THENL
       [DISJ1_TAC THEN EXISTS_TAC `u DIFF b:A->bool` THEN
        ASM_SIMP_TAC[OPEN_IN_DIFF] THEN ASM SET_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `u DIFF a:A->bool` THEN
        ASM_SIMP_TAC[OPEN_IN_DIFF] THEN ASM SET_TAC[]];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
      MATCH_MP_TAC INTERIOR_OF_MONO THEN SET_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `a:A->bool`] INTERIOR_OF_SUBSET) THEN
    MP_TAC(ISPECL [`top:A topology`; `b:A->bool`] INTERIOR_OF_SUBSET) THEN
    ASM SET_TAC[]]);;

let MOI_LCP_T_INTERIOR = prove
 (`!s:real^2->bool.
     s SUBSET std_triangle DIFF relative_frontier std_triangle
     ==> (subtopology euclidean std_triangle) interior_of s = interior s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
    X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `V:real^2->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[IN_INTERIOR] THEN
    SUBGOAL_THEN `open (V INTER interior std_triangle)` MP_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTER; GSYM MOI_LCP_OPEN_TRIANGLE] THEN ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      REWRITE_TAC[GSYM MOI_LCP_OPEN_TRIANGLE] THEN ASM SET_TAC[]];
    MP_TAC(ISPECL [`euclidean:(real^2)topology`; `s:real^2->bool`; `std_triangle`]
      INTERIOR_OF_SUBTOPOLOGY_SUBSET) THEN
    REWRITE_TAC[EUCLIDEAN_INTERIOR_OF] THEN
    MP_TAC(ISPEC `s:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]);;

let MOI_LCP_T_FRONTIER = prove
 (`!s:real^2->bool.
     compact s /\ s SUBSET std_triangle DIFF relative_frontier std_triangle
     ==> (subtopology euclidean std_triangle) frontier_of s = frontier s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of; frontier] THEN
  ASM_SIMP_TAC[MOI_LCP_T_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CLOSURE_OF_CLOSED_IN THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The hypotheses of MOI_LT3_CLEAN_CAP as one predicate, their               *)
(* first consequences, and the fine simplicial setting (S1 with a mesh      *)
(* below the distances between E1 and the rest of the double image and the *)
(* boundary, between D1 and j2, and between the disks and the frontier of   *)
(* the triangle).                                                            *)
(* ------------------------------------------------------------------------- *)

let moi_lcp_hyp = new_definition
 `moi_lcp_hyp (c:(real^N->bool)->bool) (f:real^2->real^N) k (j1:real^2->bool) j2 <=>
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal2_disk c f /\
     k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\
     pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\
     j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     j2 UNION inside j2 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {} /\
     DISJOINT (j1 UNION inside j1) (j2 UNION inside j2)`;;

let MOI_LCP_REST_CLOSED = prove
 (`!d k:real^N->bool.
     closed d /\ FINITE (components d) /\ k IN components d ==> closed (d DIFF k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d DIFF k = UNIONS (components d DELETE (k:real^N->bool))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_DELETE] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `c:real^N->bool` THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`d:real^N->bool`; `c:real^N->bool`; `k:real^N->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    ASM_MESON_TAC[CLOSED_COMPONENTS]]);;

let MOI_LCP_HYP_FACTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2.
     moi_lcp_hyp c f k j1 j2
     ==> moi_lt_singular_disk c f /\ f continuous_on std_triangle /\
         lf_simplicial_complex c /\ closed (complex_boundary c) /\
         IMAGE f std_triangle SUBSET UNIONS c /\
         compact (moi_lt_double_image f) /\
         FINITE (components (moi_lt_double_image f)) /\
         closed (moi_lt_double_image f DIFF k) /\
         k SUBSET moi_lt_double_image f /\
         compact j1 /\ compact j2 /\ ~(j1 = {}) /\ ~(j2 = {}) /\
         compact (j1 UNION inside j1) /\ compact (j2 UNION inside j2) /\
         compact (IMAGE f (j1 UNION inside j1)) /\
         IMAGE f j1 = k /\ IMAGE f j2 = k /\
         (!x y. x IN j1 /\ y IN j1 /\ f x = f y ==> x = y) /\
         (!x y. x IN j2 /\ y IN j2 /\ f x = f y ==> x = y) /\
         (!x y. x IN j1 UNION inside j1 /\ y IN j1 UNION inside j1 /\ f x = f y
                ==> x = y) /\
         {x | x IN std_triangle /\ f x IN IMAGE f (j1 UNION inside j1)} =
         (j1 UNION inside j1) UNION j2 /\
         IMAGE f (j1 UNION inside j1) INTER moi_lt_double_image f = k /\
         IMAGE f (j1 UNION inside j1) INTER complex_boundary c = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lcp_hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk (c:(real^N->bool)->bool) f` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_IMP; moi_lt_normal_disk]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS o check (fun th ->
    concl th = `pl_sphere 1 (j1:real^2->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_DISK o check (fun th ->
    concl th = `pl_sphere 1 (j1:real^2->bool)`)) THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LCP_JORDAN_FACTS) THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LCP_JORDAN_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IMP_CONJ]) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IMP_CONJ]) THEN
  SUBGOAL_THEN `FINITE (components (moi_lt_double_image (f:real^2->real^N)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (moi_lt_double_image (f:real^2->real^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LGC_DOUBLE_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`] MOI_LCP_D1_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`] MOI_LCP_CASE2_BIJ) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (j1 UNION inside j1) (j2:real^2->bool)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_LTD_FINITE_COMPLEX_CLOSED];
    ASM_MESON_TAC[moi_lt_singular_disk];
    MATCH_MP_TAC MOI_LCP_REST_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Points in a small set near a set A: a set of diameter below e meeting A   *)
(* lies within e of A.                                                       *)

let MOI_LCP_SMALL_NEAR = prove
 (`!(s:real^N->bool) e p q.
     bounded s /\ diameter s < e /\ p IN s /\ q IN s ==> dist(p,q) < e`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`s:real^N->bool`; `p:real^N`; `q:real^N`]
    DIAMETER_BOUNDED_BOUND) THEN
  ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC);;

let MOI_LCP_FINE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2.
     moi_lcp_hyp c f k j1 j2
     ==> ?t K. FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
               UNIONS t = UNIONS c /\ complex_boundary t = complex_boundary c /\
               simplicial_complex K /\ UNIONS K = std_triangle /\
               simplicial_map_on K t f /\
               (!s x x'. s IN K /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
               (!s. s IN t /\ ~(s INTER IMAGE f (j1 UNION inside j1) = {})
                    ==> s INTER (moi_lt_double_image f DIFF k) = {} /\
                        s INTER complex_boundary c = {}) /\
               (!s s'. s IN K /\ s' IN K /\ ~(s INTER (j1 UNION inside j1) = {}) /\
                       ~(s' INTER j2 = {})
                       ==> s INTER s' = {}) /\
               (!s. s IN K /\
                    ~(s INTER ((j1 UNION inside j1) UNION (j2 UNION inside j2)) = {})
                    ==> s SUBSET std_triangle DIFF relative_frontier std_triangle)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN
  ABBREV_TAC `E1 = IMAGE (f:real^2->real^N) (j1 UNION inside j1)` THEN
  ABBREV_TAC `D1 = (j1:real^2->bool) UNION inside j1` THEN
  ABBREV_TAC `D2 = (j2:real^2->bool) UNION inside j2` THEN
  (* the three separations *)
  MP_TAC(ISPECL [`E1:real^N->bool`;
                 `(moi_lt_double_image f DIFF k) UNION complex_boundary (c:(real^N->bool)->bool)`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_UNION] THEN
    MAP_EVERY UNDISCH_TAC
     [`(E1:real^N->bool) INTER moi_lt_double_image f = k`;
      `(E1:real^N->bool) INTER complex_boundary c = {}`] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`D1:real^2->bool`; `j2:real^2->bool`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `DISJOINT (D1:real^2->bool) D2` THEN EXPAND_TAC "D2" THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`(D1:real^2->bool) UNION D2`; `relative_frontier std_triangle`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION; MOI_LTD_FRONTIER_SUBSET_TRIANGLE; COMPACT_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC
     [`(D1:real^2->bool) SUBSET std_triangle DIFF relative_frontier std_triangle`;
      `(D2:real^2->bool) SUBSET std_triangle DIFF relative_frontier std_triangle`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
                 `min d1 (min (d2 / &2) d3)`] MOI_LCP_S1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:(real^N->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:(real^2->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(!s:real^N->bool. s IN t ==> bounded s) /\
                (!s:real^2->bool. s IN K ==> bounded s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` MP_TAC THENL
       [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
      X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER] o
      check (fun th -> concl th = `~((s:real^N->bool) INTER E1 = {})`)) THEN
    SUBGOAL_THEN
     `!q:real^N. q IN s
                 ==> ~(q IN (moi_lt_double_image f DIFF k) UNION complex_boundary c)`
    MP_TAC THENL
     [X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `min d1 (min (d2 / &2) d3)`; `p:real^N`; `q:real^N`]
        MOI_LCP_SMALL_NEAR) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^N`; `q:real^N`] o check (fun th ->
        can (find_term ((=) `d1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `s':real^2->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER] o
      check (fun th -> concl th = `~((s:real^2->bool) INTER D1 = {})`)) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `q:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER] o
      check (fun th -> concl th = `~((s':real^2->bool) INTER j2 = {})`)) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^2` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `min d1 (min (d2 / &2) d3)`; `p:real^2`; `z:real^2`]
      MOI_LCP_SMALL_NEAR) THEN
    MP_TAC(ISPECL [`s':real^2->bool`; `min d1 (min (d2 / &2) d3)`; `z:real^2`; `q:real^2`]
      MOI_LCP_SMALL_NEAR) THEN
    ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^2`; `q:real^2`] o check (fun th ->
      can (find_term ((=) `d2:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:real^2`; `z:real^2`; `q:real^2`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER] o
      check (fun th -> concl th = `~((s:real^2->bool) INTER (D1 UNION D2) = {})`)) THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `min d1 (min (d2 / &2) d3)`; `p:real^2`; `q:real^2`]
      MOI_LCP_SMALL_NEAR) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^2`; `q:real^2`] o check (fun th ->
      can (find_term ((=) `d3:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The source configuration: the subcomplexes of K for j1, j2               *)
(* and D1, their derived neighbourhoods inside the open triangle, the       *)
(* collars of j1 and j2, and the derived neighbourhood of D1 as the disk of *)
(* the outer collar circle of j1.                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_SOURCE_SUBCOMPLEXES = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2 t K.
     moi_lcp_hyp c f k j1 j2 /\ simplicial_complex K /\ UNIONS K = std_triangle /\
     lf_simplicial_complex t /\ simplicial_map_on K t f
     ==> simplicial_subcomplex {s | s IN K /\ s SUBSET j1} K /\
         UNIONS {s | s IN K /\ s SUBSET j1} = j1 /\
         simplicial_subcomplex {s | s IN K /\ s SUBSET j2} K /\
         UNIONS {s | s IN K /\ s SUBSET j2} = j2 /\
         simplicial_subcomplex {s | s IN K /\ s SUBSET j1 UNION inside j1} K /\
         UNIONS {s | s IN K /\ s SUBSET j1 UNION inside j1} = j1 UNION inside j1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_LCP_SUB_IN] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`;
                 `k:real^N->bool`] MOI_LCP_COMPONENT_UNIONS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_lt_singular_disk]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j j':real^2->bool. compact j /\ compact j' /\ DISJOINT j j' /\
                        j UNION j' = UNIONS {s | s IN K /\ s SUBSET j UNION j'}
                        ==> UNIONS {s | s IN K /\ s SUBSET j} = j`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN UNIONS {s | s IN K /\ s SUBSET j UNION j'}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `j UNION j':real^2->bool`)) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `j:real^2->bool`; `j':real^2->bool`]
      MOI_LCP_CONNECTED_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
        ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s | s IN K /\ s SUBSET j1} = j1:real^2->bool /\
                UNIONS {s | s IN K /\ s SUBSET j2} = j2:real^2->bool`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [EXISTS_TAC `j2:real^2->bool` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `j1:real^2->bool` THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; ASM_MESON_TAC[DISJOINT_SYM];
        SUBGOAL_THEN `j2 UNION j1:real^2->bool = j1 UNION j2` SUBST1_TAC THENL
         [SET_TAC[]; FIRST_ASSUM ACCEPT_TAC]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LCP_DISK_UNIONS THEN
  EXISTS_TAC `{s | s IN K /\ s SUBSET (j1:real^2->bool)}` THEN
  ASM_SIMP_TAC[MOI_LCP_SUB_IN] THEN ASM SET_TAC[]);;

let MOI_LCP_D1_NBHD = prove
 (`!(K:(real^2->bool)->bool) L1 L1j j1.
     simplicial_complex K /\ UNIONS L1 = j1 UNION inside j1 /\ UNIONS L1j = j1 /\
     pl_sphere 1 j1 /\ simplicial_subcomplex L1 K
     ==> derived_nbhd K L1 = (j1 UNION inside j1) UNION derived_nbhd K L1j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS) THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[derived_nbhd] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^2->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r INTER (j1:real^2->bool) = {}` THENL
     [MATCH_MP_TAC(SET_RULE `r SUBSET a ==> r SUBSET (a:real^2->bool) UNION b`) THEN
      SUBGOAL_THEN `connected (r:real^2->bool)` ASSUME_TAC THENL
       [SUBGOAL_THEN `simplicial_complex (barycentric_subdivision
                        (barycentric_subdivision (K:(real^2->bool)->bool)))` MP_TAC THENL
         [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
        REWRITE_TAC[simplicial_complex] THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`j1:real^2->bool`; `r:real^2->bool`] MOI_LCP_CONNECTED_SIDE) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(r INTER (j1 UNION inside j1:real^2->bool) = {})` THEN
      UNDISCH_TAC `r INTER (j1:real^2->bool) = {}` THEN
      UNDISCH_TAC `inside j1 INTER outside j1:real^2->bool = {}` THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `r SUBSET b ==> r SUBSET (a:real^2->bool) UNION b`) THEN
      REWRITE_TAC[derived_nbhd] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN t ==> s SUBSET UNIONS t`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    MATCH_MP_TAC(SET_RULE `a SUBSET c /\ b SUBSET c ==> (a:real^2->bool) UNION b SUBSET c`) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `j1 UNION inside j1:real^2->bool`)) THEN
      MATCH_MP_TAC MOI_LCP_NBHD_SUPERSET THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[derived_nbhd] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]]]);;

let MOI_LCP_NBHD_INT_T = prove
 (`!(K:(real^2->bool)->bool) L.
     simplicial_complex K /\
     (!s. s IN K /\ ~(s INTER UNIONS L = {})
          ==> s SUBSET std_triangle DIFF relative_frontier std_triangle)
     ==> derived_nbhd K L SUBSET std_triangle DIFF relative_frontier std_triangle`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS {s | s IN K /\ ~(s INTER UNIONS (L:(real^2->bool)->bool) = {})}` THEN
  ASM_SIMP_TAC[MOI_LCP_NBHD_IN_STAR; MOI_FMB_SC_LF] THEN
  REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The image configuration.  l = f(L1) triangulates E1 inside               *)
(* t and the image complex X = f(K); the derived neighbourhood N of l in t  *)
(* misses the rest of the double image and the boundary; N and its frontier *)
(* pull back to the derived neighbourhood and frontier of D1 UNION j2 in K. *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_SUBCOMPLEX_SC = prove
 (`!(K:(real^N->bool)->bool) L.
     simplicial_complex K /\ simplicial_subcomplex L K ==> simplicial_complex L`,
  REWRITE_TAC[simplicial_complex; simplicial_subcomplex] THEN
  MESON_TAC[FINITE_SUBSET; SUBSET]);;

let MOI_LCP_IMAGE_CONFIG = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2 t K.
     moi_lcp_hyp c f k j1 j2 /\
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     UNIONS t = UNIONS c /\ complex_boundary t = complex_boundary c /\
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_map_on K t f /\
     (!s x x'. s IN K /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
     (!s. s IN t /\ ~(s INTER IMAGE f (j1 UNION inside j1) = {})
          ==> s INTER (moi_lt_double_image f DIFF k) = {} /\
              s INTER complex_boundary c = {})
     ==> let L1 = {s | s IN K /\ s SUBSET j1 UNION inside j1} in
         let l = IMAGE (IMAGE f) L1 in
         let Lf = {s | s IN K /\ IMAGE f s IN l} in
         simplicial_subcomplex l t /\ FINITE l /\
         UNIONS l = IMAGE f (j1 UNION inside j1) /\
         UNIONS Lf = (j1 UNION inside j1) UNION j2 /\
         derived_nbhd t l INTER (moi_lt_double_image f DIFF k) = {} /\
         derived_nbhd t l INTER complex_boundary c = {} /\
         {x | x IN std_triangle /\ f x IN derived_nbhd t l} = derived_nbhd K Lf /\
         {x | x IN std_triangle /\ f x IN derived_frontier t l} = derived_frontier K Lf`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT LET_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `t:(real^N->bool)->bool`;
                 `K:(real^2->bool)->bool`] MOI_LCP_SOURCE_SUBCOMPLEXES) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_subcomplex (L1:(real^2->bool)->bool) K /\
                UNIONS L1 = j1 UNION inside j1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "L1" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (L1:(real^2->bool)->bool) /\
                simplicial_map_on L1 t (f:real^2->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_LCP_SUBCOMPLEX_SC];
      UNDISCH_TAC `simplicial_map_on K t (f:real^2->real^N)` THEN
      REWRITE_TAC[simplicial_map_on] THEN
      ASM_MESON_TAC[simplicial_subcomplex; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L1:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`]
    MOI_LNS_IMAGE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`]
    MOI_LNS_IMAGE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `X = IMAGE (IMAGE (f:real^2->real^N)) K` THEN
  SUBGOAL_THEN `simplicial_subcomplex (l:(real^N->bool)->bool) X` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) t` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["l"; "X"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the preimage of E1 *)
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`;
                 `l:(real^N->bool)->bool`] MOI_LCP_PREIMAGE_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `UNIONS (Lf:(real^2->bool)->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN
  (* N is in the closed star of E1 *)
  SUBGOAL_THEN
   `derived_nbhd t l SUBSET
    UNIONS {s | s IN t /\ ~(s INTER IMAGE (f:real^2->real^N) (j1 UNION inside j1) = {})}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) o
      check (fun th -> concl th = `UNIONS (l:(real^N->bool)->bool) =
                                   IMAGE (f:real^2->real^N) (j1 UNION inside j1)`)) THEN
    ASM_SIMP_TAC[MOI_LCP_NBHD_IN_STAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd t l INTER (moi_lt_double_image f DIFF k) = {} /\
                derived_nbhd t l INTER complex_boundary (c:(real^N->bool)->bool) = {}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `derived_nbhd t l SUBSET
                 UNIONS {s | s IN t /\
                             ~(s INTER IMAGE (f:real^2->real^N) (j1 UNION inside j1) = {})}` THEN
    UNDISCH_TAC
     `!s. s IN t /\ ~(s INTER IMAGE (f:real^2->real^N) (j1 UNION inside j1) = {})
          ==> s INTER (moi_lt_double_image f DIFF k) = {} /\
              s INTER complex_boundary (c:(real^N->bool)->bool) = {}` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* traces on the image complex *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `X:(real^N->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) INTER X = l` SUBST1_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SET_RULE `(s:(real^N->bool)->bool) SUBSET t ==> s INTER t = s`];
    ALL_TAC] THEN
  STRIP_TAC THEN
  (* condition (U) *)
  SUBGOAL_THEN
   `!x x'. x IN std_triangle /\ x' IN std_triangle /\ (f:real^2->real^N) x = f x' /\
           f x IN derived_nbhd X l /\ ~(f x IN IMAGE f (j1 UNION inside j1)) ==> x = x'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN moi_lt_double_image f` ASSUME_TAC THENL
     [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN derived_nbhd t l` ASSUME_TAC THENL
     [UNDISCH_TAC `(f:real^2->real^N) x IN derived_nbhd X l` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `derived_nbhd X (l:(real^N->bool)->bool)`)) THEN
      SIMP_TAC[IN_INTER];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`derived_nbhd (t:(real^N->bool)->bool) l INTER
       (moi_lt_double_image (f:real^2->real^N) DIFF k) = {}`;
      `(f:real^2->real^N) x IN derived_nbhd t l`;
      `(f:real^2->real^N) x IN moi_lt_double_image f`;
      `~((f:real^2->real^N) x IN IMAGE f (j1 UNION inside j1))`;
      `IMAGE (f:real^2->real^N) (j1 UNION inside j1) INTER moi_lt_double_image f = k`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`;
                 `l:(real^N->bool)->bool`] MOI_LCP_NBHD_PULLBACK) THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`;
                 `l:(real^N->bool)->bool`] MOI_LCP_FRONTIER_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `derived_nbhd K (Lf:(real^2->bool)->bool)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `derived_nbhd X (l:(real^N->bool)->bool)`));
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `derived_frontier K (Lf:(real^2->bool)->bool)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `derived_frontier X (l:(real^N->bool)->bool)`))] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[FUN_IN_IMAGE]);;


(* ------------------------------------------------------------------------- *)
(* Step S2.  The ambient dimension is at least 3 (a crossing chart          *)
(* and invariance of dimension), and the derived neighbourhood N of the     *)
(* PL 2-ball E1 = f(D1) in t is a PL 3-cell with frontier F                 *)
(* (DERIVED_NBHD_BALL_2).                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_DIM3 = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2.
     moi_lcp_hyp c f k j1 j2 ==> 3 <= dimindex(:N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN
  SUBGOAL_THEN `?y:real^N. y IN k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lt_crossing2_at c (f:real^2->real^N) y` MP_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal2_disk; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[moi_lt_crossing2_at; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                       `n1:real^2->bool`; `n2:real^2->bool`] THEN
  STRIP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  MP_TAC(ISPECL [`h':real^3->real^N`; `ball(vec 0:real^3,&1)`] INVARIANCE_OF_DIMENSION) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; REAL_LT_01] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_LCP_BALL = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2 t K.
     moi_lcp_hyp c f k j1 j2 /\
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     UNIONS t = UNIONS c /\ complex_boundary t = complex_boundary c /\
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_map_on K t f /\
     (!s x x'. s IN K /\ x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
     (!s. s IN t /\ ~(s INTER IMAGE f (j1 UNION inside j1) = {})
          ==> s INTER (moi_lt_double_image f DIFF k) = {} /\
              s INTER complex_boundary c = {})
     ==> pl_cell_with_boundary 3
          (derived_nbhd t (IMAGE (IMAGE f) {s | s IN K /\ s SUBSET j1 UNION inside j1}))
          (derived_frontier t (IMAGE (IMAGE f) {s | s IN K /\ s SUBSET j1 UNION inside j1}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `t:(real^N->bool)->bool`;
                 `K:(real^2->bool)->bool`] MOI_LCP_IMAGE_CONFIG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `l = IMAGE (IMAGE (f:real^2->real^N))
                    {s | s IN K /\ s SUBSET j1 UNION inside j1}` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LCP_DIM3) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BALL_2) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(v:real^N) IN UNIONS l` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) (j1 UNION inside j1) INTER
                   complex_boundary c = {}` THEN SET_TAC[]];
    DISJ1_TAC THEN EXISTS_TAC `2` THEN REWRITE_TAC[LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`j1 UNION inside j1:real^2->bool`;
                         `IMAGE (f:real^2->real^N) (j1 UNION inside j1)`;
                         `f:real^2->real^N`] MOI_FM3_PL_BALL_TRANSFER) THEN
    SUBGOAL_THEN `pl_cell_with_boundary 2 (j1 UNION inside j1) (j1:real^2->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[MOI_LCP_JORDAN_DISK]; ALL_TAC] THEN
    SUBGOAL_THEN `pl_polyhedron (j1 UNION inside j1:real^2->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON]; ALL_TAC] THEN
    MP_TAC(ISPECL [`j1 UNION inside j1:real^2->bool`; `f:real^2->real^N`]
      PL_INJECTIVE_INVERSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `std_triangle` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[moi_lt_singular_disk]; ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^2` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `pl_cell_with_boundary 2 (j1 UNION inside j1) (j1:real^2->bool)` THEN
      REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[];
      UNDISCH_TAC `3 <= dimindex(:N)` THEN ARITH_TAC]]);;


(* ------------------------------------------------------------------------- *)
(* The excluded configuration.  If the inner and outer traces               *)
(* bi, bo of the sheet through j2 lie on the same side fr1 of the trace al  *)
(* of the sheet through j1 on the frontier sphere F, the connected set      *)
(* f(Pm) UNION (fr1 DIFF al) UNION f(Pp) misses the sphere da UNION fr2,    *)
(* yet near a point y0 of k it meets both sides of the chart plane z1 = 0  *)
(* (MOI_LCP_CHART_LOCAL and MOI_LCP_S4_CORE).                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_NO_BAD = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) y0 x1 x2 A B Pm Pp nn fr al fr1 fr2.
     moi_lt_singular_disk c f /\ moi_lt_crossing2_at c f y0 /\
     ~(y0 IN complex_boundary c) /\
     x1 IN std_triangle /\ x2 IN std_triangle /\ ~(x1 = x2) /\
     f x1 = y0 /\ f x2 = y0 /\
     (!x. x IN std_triangle /\ f x = y0 ==> x = x1 \/ x = x2) /\
     A SUBSET std_triangle /\ closed A /\ ~(x2 IN A) /\
     (?dA. &0 < dA /\ ball(x1,dA) INTER std_triangle SUBSET A) /\
     B SUBSET std_triangle /\ (?dB. &0 < dB /\ ball(x2,dB) INTER std_triangle SUBSET B) /\
     (!b. b IN B /\ ~(f b IN moi_lt_double_image f) ==> b IN Pm UNION Pp) /\
     pl_cell_with_boundary 3 nn fr /\
     open_in (subtopology euclidean (UNIONS c)) (nn DIFF fr) /\ y0 IN nn DIFF fr /\
     pl_cell_with_boundary 2 (IMAGE f A) al /\ IMAGE f A SUBSET nn /\
     IMAGE f A INTER fr = al /\
     pl_cell_with_boundary 2 fr2 al /\ fr2 SUBSET fr /\ fr1 INTER fr2 = al /\
     connected (IMAGE f Pm UNION (fr1 DIFF al) UNION IMAGE f Pp) /\
     IMAGE f Pm UNION (fr1 DIFF al) UNION IMAGE f Pp SUBSET nn /\
     DISJOINT (IMAGE f Pm UNION (fr1 DIFF al) UNION IMAGE f Pp) (IMAGE f A) /\
     DISJOINT (IMAGE f Pm UNION (fr1 DIFF al) UNION IMAGE f Pp) fr2
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y0:real^N`;
                 `x1:real^2`; `x2:real^2`; `A:real^2->bool`; `B:real^2->bool`;
                 `nn DIFF fr:real^N->bool`] MOI_LCP_CHART_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `psi:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `z = IMAGE (f:real^2->real^N) Pm UNION (fr1 DIFF al) UNION IMAGE f Pp` THEN
  ABBREV_TAC `xp = (r / &2) % basis 1:real^3` THEN
  ABBREV_TAC `xm = --(r / &2) % basis 1:real^3` THEN
  SUBGOAL_THEN
   `(xp:real^3) IN ball(vec 0,r) /\ (xm:real^3) IN ball(vec 0,r) /\
    &0 < xp$1 /\ xm$1 < &0 /\ xp$2 = &0 /\ xm$2 = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xp"; "xm"] THEN
    SIMP_TAC[IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^N) xp IN z /\ psi xm IN z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `xp:real^3` o check (fun th ->
        can (find_term ((=) `moi_lt_double_image (f:real^2->real^N)`)) (concl th) &&
        is_forall(concl th) && can (find_term ((=) `B:real^2->bool`)) (concl th) &&
        can (find_term ((=) `psi:real^3->real^N`)) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPEC `xm:real^3` o check (fun th ->
        can (find_term ((=) `moi_lt_double_image (f:real^2->real^N)`)) (concl th) &&
        is_forall(concl th) && can (find_term ((=) `B:real^2->bool`)) (concl th) &&
        can (find_term ((=) `psi:real^3->real^N`)) (concl th)))] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN `(b:real^2) IN Pm UNION Pp` MP_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN EXPAND_TAC "z" THEN
     REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nn:real^N->bool`; `fr:real^N->bool`; `IMAGE (f:real^2->real^N) A`;
                 `al:real^N->bool`; `fr2:real^N->bool`; `z:real^N->bool`;
                 `psi:real^3->real^N`; `r:real`; `nn DIFF fr:real^N->bool`;
                 `xp:real^3`; `xm:real^3`] MOI_LCP_S4_CORE) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^N) Pm UNION (fr1 DIFF al) UNION IMAGE f Pp = z` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The source bundle.  With the fine setting of MOI_LCP_FINE:                *)
(* the derived neighbourhood A of D1 in K is the disk of the outer collar   *)
(* circle j1p of j1, with frontier j1p; the derived neighbourhood B of j2   *)
(* has frontier j2m UNION j2p (collars); A and B are disjoint compact sets  *)
(* in the open triangle.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_SOURCE_BUNDLE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2 t K.
     moi_lcp_hyp c f k j1 j2 /\
     lf_simplicial_complex t /\
     simplicial_complex K /\ UNIONS K = std_triangle /\ simplicial_map_on K t f /\
     (!s s'. s IN K /\ s' IN K /\ ~(s INTER (j1 UNION inside j1) = {}) /\
             ~(s' INTER j2 = {})
             ==> s INTER s' = {}) /\
     (!s. s IN K /\
          ~(s INTER ((j1 UNION inside j1) UNION (j2 UNION inside j2)) = {})
          ==> s SUBSET std_triangle DIFF relative_frontier std_triangle)
     ==> ?j1p j2m j2p.
           derived_nbhd K {s | s IN K /\ s SUBSET j1 UNION inside j1} =
           j1p UNION inside j1p /\
           derived_frontier K {s | s IN K /\ s SUBSET j1 UNION inside j1} = j1p /\
           pl_sphere 1 j1p /\ j1p SUBSET outside j1 /\
           j1 UNION inside j1 SUBSET inside j1p /\
           pl_sphere 1 j2m /\ pl_sphere 1 j2p /\ DISJOINT j2m j2p /\
           derived_frontier K {s | s IN K /\ s SUBSET j2} = j2m UNION j2p /\
           j2m SUBSET inside j2 /\ j2p SUBSET outside j2 /\
           connected (derived_nbhd K {s | s IN K /\ s SUBSET j2} INTER inside j2) /\
           connected (derived_nbhd K {s | s IN K /\ s SUBSET j2} INTER outside j2) /\
           (j2 UNION inside j2) UNION derived_nbhd K {s | s IN K /\ s SUBSET j2} =
           j2p UNION inside j2p /\
           compact (derived_nbhd K {s | s IN K /\ s SUBSET j1 UNION inside j1}) /\
           compact (derived_nbhd K {s | s IN K /\ s SUBSET j2}) /\
           derived_nbhd K {s | s IN K /\ s SUBSET j1 UNION inside j1} SUBSET
           std_triangle DIFF relative_frontier std_triangle /\
           derived_nbhd K {s | s IN K /\ s SUBSET j2} SUBSET
           std_triangle DIFF relative_frontier std_triangle /\
           DISJOINT (derived_nbhd K {s | s IN K /\ s SUBSET j1 UNION inside j1})
                    (derived_nbhd K {s | s IN K /\ s SUBSET j2}) /\
           j2 SUBSET interior (derived_nbhd K {s | s IN K /\ s SUBSET j2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `t:(real^N->bool)->bool`;
                 `K:(real^2->bool)->bool`] MOI_LCP_SOURCE_SUBCOMPLEXES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN
  ABBREV_TAC `L1 = {s | s IN K /\ s SUBSET (j1:real^2->bool) UNION inside j1}` THEN
  ABBREV_TAC `L1j = {s | s IN K /\ s SUBSET (j1:real^2->bool)}` THEN
  ABBREV_TAC `L2 = {s | s IN K /\ s SUBSET (j2:real^2->bool)}` THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!L. UNIONS L SUBSET (j1 UNION inside j1) UNION (j2 UNION inside j2)
        ==> derived_nbhd K L SUBSET std_triangle DIFF relative_frontier std_triangle`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCP_NBHD_INT_T THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_nbhd K L1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
    derived_nbhd K L1j SUBSET std_triangle DIFF relative_frontier std_triangle /\
    derived_nbhd K L2 SUBSET std_triangle DIFF relative_frontier std_triangle`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (derived_nbhd K L1) (derived_nbhd K (L2:(real^2->bool)->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L1:(real^2->bool)->bool`]
      MOI_LCP_NBHD_IN_STAR) THEN
    MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L2:(real^2->bool)->bool`]
      MOI_LCP_NBHD_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `!s s'. s IN K /\ s' IN K /\ ~(s INTER (j1 UNION inside j1) = {}) /\
             ~(s' INTER (j2:real^2->bool) = {})
             ==> s INTER s' = {}` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; DISJOINT; EXTENSION; IN_INTER;
                NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (derived_nbhd K (L2:(real^2->bool)->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L2:(real^2->bool)->bool`]
      MOI_FDN_DERIVED_NBHD_FINITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `K:(real^2->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ASM_MESON_TAC[simplicial_subcomplex]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j2:real^2->bool) SUBSET interior (derived_nbhd K L2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L2:(real^2->bool)->bool`]
      MOI_LCP_NBHD_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `derived_nbhd K (L2:(real^2->bool)->bool)` MOI_LCP_T_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L1j:(real^2->bool)->bool`; `j1:real^2->bool`]
    MOI_LCP_COLLARS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1m:real^2->bool` (X_CHOOSE_THEN `j1p:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L2:(real^2->bool)->bool`; `j2:real^2->bool`]
    MOI_LCP_COLLARS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j2m:real^2->bool` (X_CHOOSE_THEN `j2p:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`j1p:real^2->bool`; `j2m:real^2->bool`; `j2p:real^2->bool`] THEN
  SUBGOAL_THEN `derived_nbhd K L1 = (j1p:real^2->bool) UNION inside j1p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L1:(real^2->bool)->bool`;
                   `L1j:(real^2->bool)->bool`; `j1:real^2->bool`] MOI_LCP_D1_NBHD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_JORDAN_FACTS o check (fun th ->
    concl th = `pl_sphere 1 (j1:real^2->bool)`)) THEN
  MP_TAC(ISPEC `j1p:real^2->bool` MOI_LCP_JORDAN_DISK) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* frontier of the disk of j1p *)
    REWRITE_TAC[derived_frontier] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `j1p UNION inside j1p:real^2->bool` MOI_LCP_T_FRONTIER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_MESON_TAC[]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    (* the disk of j1 lies inside j1p *)
    MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L1:(real^2->bool)->bool`]
      MOI_LCP_NBHD_SUPERSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(j1p:real^2->bool) SUBSET outside j1` THEN
    UNDISCH_TAC `inside j1 INTER outside j1:real^2->bool = {}` THEN
    UNDISCH_TAC `outside j1 INTER j1:real^2->bool = {}` THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Two small facts for the assembly: the interior of a finite               *)
(* derived neighbourhood in its complex is the neighbourhood minus its      *)
(* frontier and contains the subcomplex; a PL disk minus its boundary is    *)
(* connected.                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_N_INTERIOR = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ FINITE l
     ==> derived_nbhd t l SUBSET UNIONS t /\
         derived_frontier t l SUBSET derived_nbhd t l /\
         open_in (subtopology euclidean (UNIONS t))
                 (derived_nbhd t l DIFF derived_frontier t l) /\
         UNIONS l SUBSET derived_nbhd t l DIFF derived_frontier t l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (derived_nbhd (t:(real^N->bool)->bool) l)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_DERIVED_NBHD_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd (t:(real^N->bool)->bool) l SUBSET UNIONS t` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {s | s IN t /\ ~(s INTER UNIONS (l:(real^N->bool)->bool) = {})}` THEN
    ASM_SIMP_TAC[MOI_LCP_NBHD_IN_STAR] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_nbhd (t:(real^N->bool)->bool) l DIFF derived_frontier t l =
    (subtopology euclidean (UNIONS t)) interior_of (derived_nbhd t l)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier; frontier_of] THEN
    SUBGOAL_THEN `(subtopology euclidean (UNIONS t)) closure_of
                    (derived_nbhd (t:(real^N->bool)->bool) l) = derived_nbhd t l`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_CLOSED_IN THEN MATCH_MP_TAC CLOSED_SUBSET THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MP_TAC(ISPECL [`subtopology euclidean (UNIONS (t:(real^N->bool)->bool))`;
                     `derived_nbhd (t:(real^N->bool)->bool) l`] INTERIOR_OF_SUBSET) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_IN_INTERIOR_OF] THEN CONJ_TAC THENL
   [REWRITE_TAC[derived_frontier; frontier_of] THEN
    MATCH_MP_TAC(SET_RULE `(c:real^N->bool) SUBSET n ==> c DIFF i SUBSET n`) THEN
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    CONJ_TAC THENL [SET_TAC[]; MATCH_MP_TAC CLOSED_SUBSET] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FN2_INTERIOR_NC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
        MOI_LCP_NBHD_SUPERSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC FACE_OF_REFL THEN
        SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision
                        (barycentric_subdivision (t:(real^N->bool)->bool)))` MP_TAC THENL
         [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX]]]]);;

let MOI_LCP_CELL_OPEN_CONNECTED = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> connected (d DIFF j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (k:real^N->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF j = IMAGE (f:real^N->real^N) (relative_interior k)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `d:real^N->bool`)) THEN
    REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET]]);;


(* ------------------------------------------------------------------------- *)
(* The configuration.  From the hypotheses: the source sets                 *)
(* A (the disk of j1p), B (the neighbourhood of j2) with the collar circles *)
(* j1p, j2m, j2p, and the PL 3-cell N with frontier sphere F in |c|, with   *)
(* f^-1(N) = A UNION B and f^-1(F) = j1p UNION j2m UNION j2p.               *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_CONFIG = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2.
     moi_lcp_hyp c f k j1 j2
     ==> ?A B j1p j2m j2p nn fr.
           pl_sphere 1 j1p /\ pl_sphere 1 j2m /\ pl_sphere 1 j2p /\ DISJOINT j2m j2p /\
           A = j1p UNION inside j1p /\ j1p SUBSET outside j1 /\
           j1 UNION inside j1 SUBSET inside j1p /\
           j2m SUBSET inside j2 /\ j2p SUBSET outside j2 /\
           connected (B INTER inside j2) /\ connected (B INTER outside j2) /\
           (j2 UNION inside j2) UNION B = j2p UNION inside j2p /\
           j2m UNION j2p SUBSET B /\
           compact A /\ compact B /\
           A SUBSET std_triangle DIFF relative_frontier std_triangle /\
           B SUBSET std_triangle DIFF relative_frontier std_triangle /\
           DISJOINT A B /\ j2 SUBSET interior B /\
           pl_cell_with_boundary 3 nn fr /\ nn SUBSET UNIONS c /\
           nn INTER (moi_lt_double_image f DIFF k) = {} /\
           nn INTER complex_boundary c = {} /\
           open_in (subtopology euclidean (UNIONS c)) (nn DIFF fr) /\
           IMAGE f (j1 UNION inside j1) SUBSET nn DIFF fr /\
           {x | x IN std_triangle /\ f x IN nn} = A UNION B /\
           {x | x IN std_triangle /\ f x IN fr} = j1p UNION j2m UNION j2p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_FINE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `t:(real^N->bool)->bool`;
                 `K:(real^2->bool)->bool`] MOI_LCP_SOURCE_BUNDLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1p:real^2->bool` (X_CHOOSE_THEN `j2m:real^2->bool`
    (X_CHOOSE_THEN `j2p:real^2->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `t:(real^N->bool)->bool`;
                 `K:(real^2->bool)->bool`] MOI_LCP_IMAGE_CONFIG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `t:(real^N->bool)->bool`;
                 `K:(real^2->bool)->bool`] MOI_LCP_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `t:(real^N->bool)->bool`;
                 `K:(real^2->bool)->bool`] MOI_LCP_SOURCE_SUBCOMPLEXES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  (* name the subcomplexes *)
  SUBGOAL_THEN `?L1. L1 = {s | s IN K /\ s SUBSET (j1:real^2->bool) UNION inside j1}`
  (X_CHOOSE_THEN `L1:(real^2->bool)->bool` (SUBST_ALL_TAC o SYM)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?L2. L2 = {s | s IN K /\ s SUBSET (j2:real^2->bool)}`
  (X_CHOOSE_THEN `L2:(real^2->bool)->bool` (SUBST_ALL_TAC o SYM)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. l = IMAGE (IMAGE (f:real^2->real^N)) L1`
  (X_CHOOSE_THEN `l:(real^N->bool)->bool` (SUBST_ALL_TAC o SYM)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?Lf. Lf = {s | s IN K /\ IMAGE (f:real^2->real^N) s IN l}`
  (X_CHOOSE_THEN `Lf:(real^2->bool)->bool` (SUBST_ALL_TAC o SYM)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  (* the pulled back neighbourhood and frontier split *)
  SUBGOAL_THEN `UNIONS (Lf:(real^2->bool)->bool) = UNIONS (L1 UNION L2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_UNION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `Lf:(real^2->bool)->bool`;
                 `L1 UNION L2:(real^2->bool)->bool`] MOI_LCP_NBHD_UNIONS_EQ) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOI_LCP_NBHD_UNION] THEN STRIP_TAC THEN
  SUBGOAL_THEN `derived_frontier K (Lf:(real^2->bool)->bool) =
                derived_frontier K L1 UNION derived_frontier K L2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `derived_frontier K (Lf:(real^2->bool)->bool)`)) THEN
    REWRITE_TAC[derived_frontier; MOI_LCP_NBHD_UNION] THEN
    MATCH_MP_TAC MOI_LCP_FRONTIER_OF_DISJOINT_UNION THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd K (L1:(real^2->bool)->bool)`; `derived_nbhd K (L2:(real^2->bool)->bool)`;
    `j1p:real^2->bool`; `j2m:real^2->bool`; `j2p:real^2->bool`;
    `derived_nbhd t (l:(real^N->bool)->bool)`; `derived_frontier t (l:(real^N->bool)->bool)`] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_LCP_N_INTERIOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `L2:(real^2->bool)->bool`] MOI_LCP_N_INTERIOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `K:(real^2->bool)->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ASM_MESON_TAC[simplicial_subcomplex]];
    STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `derived_frontier K (L2:(real^2->bool)->bool)`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `UNIONS t = UNIONS (c:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `UNIONS t = UNIONS (c:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (l:(real^N->bool)->bool)`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `derived_nbhd K (Lf:(real^2->bool)->bool)` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `derived_frontier K (Lf:(real^2->bool)->bool)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `derived_frontier K L1 UNION derived_frontier K (L2:(real^2->bool)->bool)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* The image side of the configuration.  The only                          *)
(* identifications of f on A UNION B are between j1 and j2; hence f is    *)
(* injective on A and on B, the traces f(j1p), f(j2m), f(j2p) are disjoint *)
(* PL circles in the frontier sphere F, and f(A) is a PL disk bounded by    *)
(* f(j1p).                                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_CONFIG_DOUBLE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2 A B j1p nn.
     moi_lcp_hyp c f k j1 j2 /\
     A = j1p UNION inside j1p /\ j1 UNION inside j1 SUBSET inside j1p /\
     A SUBSET std_triangle /\ B SUBSET std_triangle /\
     DISJOINT A B /\ j2 SUBSET B /\
     nn INTER (moi_lt_double_image f DIFF k) = {} /\
     {x | x IN std_triangle /\ f x IN nn} = A UNION B
     ==> (!a b. a IN A /\ b IN A /\ f a = f b ==> a = b) /\
         (!a b. a IN B /\ b IN B /\ f a = f b ==> a = b) /\
         (!a b. a IN A /\ b IN B /\ f a = f b ==> a IN j1 /\ b IN j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN
  SUBGOAL_THEN
   `!a b. a IN A UNION B /\ b IN A UNION B /\ (f:real^2->real^N) a = f b /\ ~(a = b)
          ==> (a IN j1 \/ a IN j2) /\ (b IN j1 \/ b IN j2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^2) IN std_triangle /\ (b:real^2) IN std_triangle /\
                  (f:real^2->real^N) a IN nn`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN nn} = A UNION B` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N) a IN k` ASSUME_TAC THENL
     [SUBGOAL_THEN `(f:real^2->real^N) a IN moi_lt_double_image f` MP_TAC THENL
       [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `nn INTER (moi_lt_double_image (f:real^2->real^N) DIFF k) = {}` THEN
        UNDISCH_TAC `(f:real^2->real^N) a IN nn` THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = j1 UNION j2` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (A:real^2->bool) j2 /\ DISJOINT (B:real^2->bool) j1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT (A:real^2->bool) B`; `(j2:real^2->bool) SUBSET B`;
      `A:real^2->bool = j1p UNION inside j1p`;
      `j1 UNION inside j1 SUBSET inside (j1p:real^2->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `b:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `j1:real^2->bool`)) (concl th) &&
      can (find_term ((=) `A UNION B:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    SUBGOAL_THEN `~((a:real^2) IN j2) /\ ~((b:real^2) IN j2)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `b:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `j1:real^2->bool`)) (concl th) &&
      can (find_term ((=) `A UNION B:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    SUBGOAL_THEN `~((a:real^2) IN j1) /\ ~((b:real^2) IN j1)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `~(a:real^2 = b)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `b:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `j1:real^2->bool`)) (concl th) &&
      can (find_term ((=) `A UNION B:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN ASM SET_TAC[]]);;

let MOI_LCP_PL_IMAGE_CIRCLE = prove
 (`!(f:real^2->real^N) s j.
     pl_map_on std_triangle f /\ 2 <= dimindex(:N) /\ pl_sphere 1 j /\
     j SUBSET s /\ s SUBSET std_triangle /\
     (!a b. a IN s /\ b IN s /\ f a = f b ==> a = b)
     ==> pl_sphere 1 (IMAGE f j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (j:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `f:real^2->real^N`] PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^2`) THEN
  MATCH_MP_TAC(ISPECL [`j:real^2->bool`; `IMAGE (f:real^2->real^N) j`;
                       `f:real^2->real^N`; `g:real^N->real^2`; `1`]
                      MOI_FM3_PL_SPHERE_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MOI_LCP_PL_IMAGE_DISK = prove
 (`!(f:real^2->real^N) d j.
     pl_map_on std_triangle f /\ 2 <= dimindex(:N) /\ pl_cell_with_boundary 2 d j /\
     d SUBSET std_triangle /\
     (!a b. a IN d /\ b IN d /\ f a = f b ==> a = b)
     ==> pl_cell_with_boundary 2 (IMAGE f d) (IMAGE f j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `f:real^2->real^N`] PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `std_triangle` THEN ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^2`) THEN
  MATCH_MP_TAC MOI_FCL_CELL_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`d:real^2->bool`; `g:real^N->real^2`] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The two cases of MOI_LCP_CHOOSE_CAP.  In the good case the               *)
(* disk d of the frontier sphere bounded by f(j2p) and missing the other    *)
(* traces is the clean cap with j = j2p; the bad case is excluded by        *)
(* MOI_LCP_NO_BAD.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_GOOD_CASE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2 A B j1p j2m j2p nn fr d.
     moi_lcp_hyp c f k j1 j2 /\
     pl_sphere 1 j2p /\ j2p SUBSET outside j2 /\
     (j2 UNION inside j2) UNION B = j2p UNION inside j2p /\
     B SUBSET std_triangle DIFF relative_frontier std_triangle /\
     DISJOINT A B /\ j1 SUBSET A /\
     pl_cell_with_boundary 3 nn fr /\ nn SUBSET UNIONS c /\
     nn INTER (moi_lt_double_image f DIFF k) = {} /\
     nn INTER complex_boundary c = {} /\
     {x | x IN std_triangle /\ f x IN nn} = A UNION B /\
     {x | x IN std_triangle /\ f x IN fr} = j1p UNION j2m UNION j2p /\
     pl_cell_with_boundary 2 d (IMAGE f j2p) /\ d SUBSET fr /\
     DISJOINT d (IMAGE f j1p) /\ DISJOINT d (IMAGE f j2m)
     ==> pl_sphere 1 j2p /\ j2 UNION inside j2 SUBSET inside j2p /\
         j2p UNION inside j2p SUBSET std_triangle DIFF relative_frontier std_triangle /\
         {x | x IN (j2p UNION inside j2p) DIFF (j2 UNION inside j2) /\
              f x IN moi_lt_double_image f} = {} /\
         pl_cell_with_boundary 2 d (IMAGE f j2p) /\
         d INTER IMAGE f std_triangle = IMAGE f j2p /\
         d SUBSET UNIONS c DIFF complex_boundary c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LCP_JORDAN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(fr:real^N->bool) SUBSET nn /\ IMAGE (f:real^2->real^N) j2p SUBSET d`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the disk of j2 inside j2p *)
    MAP_EVERY UNDISCH_TAC
     [`(j2 UNION inside j2) UNION B = (j2p:real^2->bool) UNION inside j2p`;
      `(j2p:real^2->bool) SUBSET outside j2`;
      `inside j2 INTER outside j2:real^2->bool = {}`;
      `outside j2 INTER j2:real^2->bool = {}`] THEN SET_TAC[];
    (* in the open triangle *)
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `(j2p:real^2->bool) UNION inside j2p`)) THEN
    ASM_REWRITE_TAC[UNION_SUBSET];
    (* no double points in the collar *)
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_DIFF] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN B` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN j2p UNION inside j2p` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `(j2p:real^2->bool) UNION inside j2p`)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN std_triangle /\ (f:real^2->real^N) x IN nn`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN nn} = A UNION B` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN k` ASSUME_TAC THENL
     [UNDISCH_TAC `nn INTER (moi_lt_double_image (f:real^2->real^N) DIFF k) = {}` THEN
      UNDISCH_TAC `(f:real^2->real^N) x IN nn` THEN
      UNDISCH_TAC `(f:real^2->real^N) x IN moi_lt_double_image f` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN j1 UNION j2` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `j1 UNION j2:real^2->bool`)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~((x:real^2) IN j2 UNION inside j2)`; `(x:real^2) IN B`;
      `DISJOINT (A:real^2->bool) B`; `(j1:real^2->bool) SUBSET A`] THEN SET_TAC[];
    (* the cap meets the image in its boundary *)
    SUBGOAL_THEN `fr INTER IMAGE (f:real^2->real^N) std_triangle =
                  IMAGE f j1p UNION IMAGE f j2m UNION IMAGE f j2p`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `j1p UNION j2m UNION j2p:real^2->bool`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`fr INTER IMAGE (f:real^2->real^N) std_triangle =
       IMAGE f j1p UNION IMAGE f j2m UNION IMAGE f j2p`;
      `(d:real^N->bool) SUBSET fr`; `DISJOINT d (IMAGE (f:real^2->real^N) j1p)`;
      `DISJOINT d (IMAGE (f:real^2->real^N) j2m)`;
      `IMAGE (f:real^2->real^N) j2p SUBSET d`;
      `IMAGE (f:real^2->real^N) std_triangle SUBSET UNIONS c`] THEN
    SUBGOAL_THEN `IMAGE (f:real^2->real^N) j2p SUBSET IMAGE f std_triangle` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
    SET_TAC[];
    (* away from the boundary *)
    MAP_EVERY UNDISCH_TAC
     [`(d:real^N->bool) SUBSET fr`; `(fr:real^N->bool) SUBSET nn`;
      `(nn:real^N->bool) SUBSET UNIONS c`;
      `nn INTER complex_boundary (c:(real^N->bool)->bool) = {}`] THEN SET_TAC[]]);;

let MOI_LCP_BAD_CASE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2 A B j1p j2m j2p nn fr fr1 fr2.
     moi_lcp_hyp c f k j1 j2 /\
     pl_sphere 1 j1p /\ pl_sphere 1 j2m /\ pl_sphere 1 j2p /\
     A = j1p UNION inside j1p /\ j1p SUBSET outside j1 /\
     j1 UNION inside j1 SUBSET inside j1p /\
     j2m SUBSET inside j2 /\ j2p SUBSET outside j2 /\
     connected (B INTER inside j2) /\ connected (B INTER outside j2) /\
     j2m UNION j2p SUBSET B /\
     compact A /\
     A SUBSET std_triangle DIFF relative_frontier std_triangle /\
     B SUBSET std_triangle DIFF relative_frontier std_triangle /\
     DISJOINT A B /\ j2 SUBSET interior B /\
     pl_cell_with_boundary 3 nn fr /\
     nn INTER (moi_lt_double_image f DIFF k) = {} /\
     open_in (subtopology euclidean (UNIONS c)) (nn DIFF fr) /\
     IMAGE f (j1 UNION inside j1) SUBSET nn DIFF fr /\
     {x | x IN std_triangle /\ f x IN nn} = A UNION B /\
     {x | x IN std_triangle /\ f x IN fr} = j1p UNION j2m UNION j2p /\
     pl_cell_with_boundary 2 fr1 (IMAGE f j1p) /\
     pl_cell_with_boundary 2 fr2 (IMAGE f j1p) /\
     fr1 UNION fr2 = fr /\ fr1 INTER fr2 = IMAGE f j1p /\
     IMAGE f j2m SUBSET fr1 /\ IMAGE f j2p SUBSET fr1 /\
     DISJOINT (IMAGE f j1p) (IMAGE f j2m) /\ DISJOINT (IMAGE f j1p) (IMAGE f j2p)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LCP_DIM3) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LCP_JORDAN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `j1p:real^2->bool` MOI_LCP_JORDAN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `j1p:real^2->bool` MOI_LCP_JORDAN_DISK) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(j2:real^2->bool) SUBSET B` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `A:real^2->bool`; `B:real^2->bool`;
                 `j1p:real^2->bool`; `nn:real^N->bool`] MOI_LCP_CONFIG_DOUBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  (* the base point on k *)
  SUBGOAL_THEN `?y0:real^N. y0 IN k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `?x1:real^2. x1 IN j1 /\ (f:real^2->real^N) x1 = y0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^N) IN k` THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> concl th = `IMAGE (f:real^2->real^N) j1 = k`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x2:real^2. x2 IN j2 /\ (f:real^2->real^N) x2 = y0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^N) IN k` THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> concl th = `IMAGE (f:real^2->real^N) j2 = k`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y0:real^N`;
                 `x1:real^2`; `x2:real^2`; `A:real^2->bool`; `B:real^2->bool`;
                 `B INTER inside j2:real^2->bool`; `B INTER outside j2:real^2->bool`;
                 `nn:real^N->bool`; `fr:real^N->bool`;
                 `IMAGE (f:real^2->real^N) j1p`; `fr1:real^N->bool`; `fr2:real^N->bool`]
    MOI_LCP_NO_BAD) THEN
  SUBGOAL_THEN `(x1:real^2) IN std_triangle /\ (x2:real^2) IN std_triangle`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(fr:real^N->bool) SUBSET nn /\ fr2 SUBSET fr /\ fr1 SUBSET fr`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_LCP_CELL_POLYHEDRON]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) A INTER fr = IMAGE f j1p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      SUBGOAL_THEN `(a:real^2) IN j1p UNION j2m UNION j2p` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `j1p UNION j2m UNION j2p:real^2->bool`)) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(a:real^2) IN j2m` THEN UNDISCH_TAC `(a:real^2) IN A` THEN
        MAP_EVERY UNDISCH_TAC [`DISJOINT (A:real^2->bool) B`;
                               `j2m UNION j2p SUBSET (B:real^2->bool)`] THEN SET_TAC[];
        UNDISCH_TAC `(a:real^2) IN j2p` THEN UNDISCH_TAC `(a:real^2) IN A` THEN
        MAP_EVERY UNDISCH_TAC [`DISJOINT (A:real^2->bool) B`;
                               `j2m UNION j2p SUBSET (B:real^2->bool)`] THEN SET_TAC[]];
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(a:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN fr}`
        MP_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]]];
    ALL_TAC] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  SUBGOAL_THEN `!b:real^2. b IN B ==> b IN std_triangle /\ (f:real^2->real^N) b IN nn`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN nn} = A UNION B` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^2. a IN A ==> a IN std_triangle /\ (f:real^2->real^N) a IN nn`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN nn} = A UNION B` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* points of B over fr lie in j2m UNION j2p *)
  SUBGOAL_THEN
   `!b:real^2. b IN B /\ (f:real^2->real^N) b IN fr ==> b IN j2m UNION j2p`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(b:real^2) IN j1p UNION j2m UNION j2p` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `j1p UNION j2m UNION j2p:real^2->bool`)) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(b:real^2) IN B`; `DISJOINT (A:real^2->bool) B`;
      `A:real^2->bool = j1p UNION inside j1p`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (B INTER inside j2) INTER fr SUBSET IMAGE f j2m /\
                IMAGE (f:real^2->real^N) (B INTER outside j2) INTER fr SUBSET IMAGE f j2p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    (REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN
     X_GEN_TAC `y:real^N` THEN
     DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
     EXISTS_TAC `b:real^2` THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `b:real^2` o check (fun th ->
       is_forall(concl th) &&
       can (find_term ((=) `j2m UNION j2p:real^2->bool`)) (concl th))) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     MAP_EVERY UNDISCH_TAC
      [`(j2m:real^2->bool) SUBSET inside j2`; `(j2p:real^2->bool) SUBSET outside j2`;
       `inside j2 INTER outside j2:real^2->bool = {}`] THEN
     TRY(UNDISCH_TAC `(b:real^2) IN inside j2`) THEN
     TRY(UNDISCH_TAC `(b:real^2) IN outside j2`) THEN SET_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(IMAGE (f:real^2->real^N) j2m) SUBSET IMAGE f (B INTER inside j2) /\
                IMAGE (f:real^2->real^N) j2p SUBSET IMAGE f (B INTER outside j2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (f:real^2->real^N) j2m = {}) /\ ~(IMAGE (f:real^2->real^N) j2p = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[MOI_LCP_JORDAN_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on B` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* crossing chart *)
    ASM_MESON_TAC[moi_lt_normal2_disk; SUBSET];
    ASM SET_TAC[];
    ASM SET_TAC[];
    (* the fibre *)
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN j1 UNION j2` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `j1 UNION j2:real^2->bool`)) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[]];
    ASM SET_TAC[];
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ASM SET_TAC[];
    (* a ball around x1 in A *)
    MP_TAC(ISPEC `inside j1p:real^2->bool` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x1:real^2`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ASM SET_TAC[];
    (* a ball around x2 in B *)
    MP_TAC(ISPEC `interior B:real^2->bool` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `x2:real^2`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    MP_TAC(ISPEC `B:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    (* points of B off the double image *)
    X_GEN_TAC `b:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((b:real^2) IN j2)` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((f:real^2->real^N) b IN moi_lt_double_image f)` THEN
      REWRITE_TAC[] THEN
      UNDISCH_TAC `(k:real^N->bool) SUBSET moi_lt_double_image f` THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) j2 = k` THEN
      UNDISCH_TAC `(b:real^2) IN j2` THEN SET_TAC[];
      UNDISCH_TAC `inside j2 UNION outside j2:real^2->bool = (:real^2) DIFF j2` THEN
      UNDISCH_TAC `(b:real^2) IN B` THEN SET_TAC[]];
    (* y0 in the open cell *)
    UNDISCH_TAC `IMAGE (f:real^2->real^N) (j1 UNION inside j1) SUBSET nn DIFF fr` THEN
    UNDISCH_TAC `(x1:real^2) IN j1` THEN UNDISCH_TAC `(f:real^2->real^N) x1 = y0` THEN
    SET_TAC[];
    (* f(A) is a PL disk *)
    MATCH_MP_TAC MOI_LCP_PL_IMAGE_DISK THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_MESON_TAC[moi_lt_singular_disk];
      UNDISCH_TAC `3 <= dimindex(:N)` THEN ARITH_TAC;
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    (* the connected set *)
    MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_LCP_CELL_OPEN_CONNECTED];
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        MATCH_MP_TAC(SET_RULE
         `!e:real^N->bool. e SUBSET fr1 /\ DISJOINT al e /\ e SUBSET p /\ ~(e = {})
                           ==> ~((fr1 DIFF al) INTER p = {})`) THEN
        EXISTS_TAC `IMAGE (f:real^2->real^N) j2p` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(SET_RULE
       `!e:real^N->bool. e SUBSET fr1 /\ DISJOINT al e /\ e SUBSET p /\ ~(e = {})
                         ==> ~(p INTER ((fr1 DIFF al) UNION q) = {})`) THEN
      EXISTS_TAC `IMAGE (f:real^2->real^N) j2m` THEN ASM_REWRITE_TAC[]];
    (* inside nn *)
    REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
      ASM SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]];
    (* missing f(A) *)
    MATCH_MP_TAC(SET_RULE
     `!pm pp fa (fr:real^N->bool) fr1 al.
        DISJOINT pm fa /\ DISJOINT pp fa /\ fa INTER fr = al /\ fr1 SUBSET fr
        ==> DISJOINT (pm UNION (fr1 DIFF al) UNION pp) fa`) THEN
    EXISTS_TAC `fr:real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]] THEN
    (REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~((b:real^2) IN j2)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`inside j2 INTER j2:real^2->bool = {}`; `outside j2 INTER j2:real^2->bool = {}`] THEN
      TRY(UNDISCH_TAC `(b:real^2) IN inside j2`) THEN
      TRY(UNDISCH_TAC `(b:real^2) IN outside j2`) THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `b:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `j1:real^2->bool`)) (concl th) &&
      can (find_term ((=) `B:real^2->bool`)) (concl th) &&
      can (find_term ((=) `A:real^2->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]);
    (* missing fr2 *)
    MATCH_MP_TAC(SET_RULE
     `!pm pp bi bo (fr:real^N->bool) fr1 fr2 al.
        pm INTER fr SUBSET bi /\ pp INTER fr SUBSET bo /\ fr2 SUBSET fr /\
        fr1 INTER fr2 = al /\ bi SUBSET fr1 /\ bo SUBSET fr1 /\
        DISJOINT al bi /\ DISJOINT al bo
        ==> DISJOINT (pm UNION (fr1 DIFF al) UNION pp) fr2`) THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (f:real^2->real^N) j2m`; `IMAGE (f:real^2->real^N) j2p`;
                          `fr:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The clean cap.  The traces of the frontier sphere are three               *)
(* disjoint PL circles; MOI_LCP_CHOOSE_CAP gives a cap d of f(j2p) missing   *)
(* the others (MOI_LCP_GOOD_CASE) or the excluded configuration              *)
(* (MOI_LCP_BAD_CASE).                                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_LCP_MAIN = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k j1 j2.
     moi_lcp_hyp c f k j1 j2
     ==> ?j d. pl_sphere 1 j /\ j2 UNION inside j2 SUBSET inside j /\
               j UNION inside j SUBSET std_triangle DIFF relative_frontier std_triangle /\
               {x | x IN (j UNION inside j) DIFF (j2 UNION inside j2) /\
                    f x IN moi_lt_double_image f} = {} /\
               pl_cell_with_boundary 2 d (IMAGE f j) /\
               d INTER IMAGE f std_triangle = IMAGE f j /\
               d SUBSET UNIONS c DIFF complex_boundary c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LCP_CONFIG) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`A:real^2->bool`; `B:real^2->bool`; `j1p:real^2->bool`;
                       `j2m:real^2->bool`; `j2p:real^2->bool`; `nn:real^N->bool`;
                       `fr:real^N->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LCP_HYP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LCP_DIM3) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lcp_hyp]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j2:real^2->bool) SUBSET B` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `j1:real^2->bool`; `j2:real^2->bool`; `A:real^2->bool`; `B:real^2->bool`;
                 `j1p:real^2->bool`; `nn:real^N->bool`] MOI_LCP_CONFIG_DOUBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_map_on std_triangle (f:real^2->real^N) /\ 2 <= dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[moi_lt_singular_disk]; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 1 (IMAGE (f:real^2->real^N) j1p) /\ pl_sphere 1 (IMAGE f j2m) /\
    pl_sphere 1 (IMAGE f j2p)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_LCP_PL_IMAGE_CIRCLE THENL
     [EXISTS_TAC `A:real^2->bool`; EXISTS_TAC `B:real^2->bool`;
      EXISTS_TAC `B:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^N) j1p SUBSET fr /\ IMAGE f j2m SUBSET fr /\
    IMAGE f j2p SUBSET fr`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN fr} =
                 j1p UNION j2m UNION j2p` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; SUBSET; FORALL_IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (f:real^2->real^N) j1p) (IMAGE f j2m) /\
    DISJOINT (IMAGE (f:real^2->real^N) j1p) (IMAGE f j2p) /\
    DISJOINT (IMAGE (f:real^2->real^N) j2m) (IMAGE f j2p)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `j1:real^2->bool` MOI_LCP_JORDAN_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC)) THENL
     [SUBGOAL_THEN `(a:real^2) IN j1` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_UNION]; ASM SET_TAC[]];
      SUBGOAL_THEN `(a:real^2) IN j1` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_UNION]; ASM SET_TAC[]];
      SUBGOAL_THEN `a:real^2 = b` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_UNION]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (fr:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_CELL_SPHERE THEN EXISTS_TAC `nn:real^N->bool` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fr:real^N->bool`; `IMAGE (f:real^2->real^N) j1p`;
                 `IMAGE (f:real^2->real^N) j2m`; `IMAGE (f:real^2->real^N) j2p`]
    MOI_LCP_CHOOSE_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `j2p:real^2->bool` THEN EXISTS_TAC `d:real^N->bool` THEN
    MATCH_MP_TAC MOI_LCP_GOOD_CASE THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `j1:real^2->bool`; `A:real^2->bool`;
                          `B:real^2->bool`; `j1p:real^2->bool`; `j2m:real^2->bool`;
                          `nn:real^N->bool`; `fr:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC MOI_LCP_BAD_CASE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                          `j1:real^2->bool`; `j2:real^2->bool`; `A:real^2->bool`;
                          `B:real^2->bool`; `j1p:real^2->bool`; `j2m:real^2->bool`;
                          `j2p:real^2->bool`; `nn:real^N->bool`; `fr:real^N->bool`;
                          `fr1:real^N->bool`; `fr2:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let CLEAN_CAP = prove
 (MOI_LT3_CLEAN_CAP,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                       `j1:real^2->bool`; `j2:real^2->bool`] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                       `j1:real^2->bool`; `j2:real^2->bool`] MOI_LCP_MAIN) THEN
  ASM_REWRITE_TAC[moi_lcp_hyp]);;

