(* ========================================================================= *)
(* pc_moi_s26_level: level circles of a PL singular disk near a bicollared   *)
(* surface (Moise GTM 47, p.193 (a)-(b)).  Main theorem                      *)
(*   LEVEL_CIRCLES |- MOI_S26_LEVEL_CIRCLES   (pc_moi_s2628_stmt.ml)         *)
(* Route: triangulate the part P of the triangle mapped into the bicollar   *)
(* so that the collar coordinate H = sndcart o rho' o f is affine on the     *)
(* simplices; take a level e missed by the vertex values; the level set is  *)
(* a compact polyhedron with line charts (a generic planar lemma: near a     *)
(* level point H is strictly monotone along a fixed direction, so the map   *)
(* y |-> (H y, n dot y) is injective and invariance of domain applies); its *)
(* components are PL circles (MOI_S4L_LINE_CHART_CIRCLES).                   *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_s28_cut.ml";;
needs "src/pc_moi_loop_stmt.ml";;   (* std_triangle facts *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Level sets of piecewise affine functions in the plane.                   *)
(* CARRIER: a point of a simplicial complex lies in the relative interior   *)
(* of a simplex contained in every simplex through it.  SEGMENT_SHIFT: if   *)
(* the pieces of H through a convex set all have slope lam along d, then H  *)
(* grows by s lam from y to y + s d.  SLICE_CHART: a homeomorphism y |->    *)
(* (H y, k y) of an open set onto an open set gives k as a line chart of the *)
(* level sets of H.  LEVEL_LOCAL: the level set of H through a point x      *)
(* whose value is not a vertex value has a line chart at x.                  *)
(* ========================================================================= *)

let MOI_S6LV_CARRIER = prove
 (`!(K:(real^N->bool)->bool) x.
     simplicial_complex K /\ x IN UNIONS K
     ==> ?t. t IN K /\ x IN relative_interior t /\
             !s. s IN K /\ x IN s ==> t SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s0:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `convex (s0:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER t face_of t` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(s:real^N->bool) INTER t = t` THENL
   [UNDISCH_TAC `(s:real^N->bool) INTER t = t` THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `(s:real^N->bool) INTER t`]
    FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
  ASM_REWRITE_TAC[relative_frontier] THEN
  MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:real^N) IN relative_interior t`; `(x:real^N) IN s`] THEN
  SET_TAC[]);;

let MOI_S6LV_SIMPLEX_VERTEX = prove
 (`!(K:(real^N->bool)->bool) t.
     simplicial_complex K /\ t IN K /\ ~(t = {})
     ==> ?v. v IN t /\ {v} IN K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (t:real^N->bool) /\ convex t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
  EXISTS_TAC `v:real^N` THEN
  SUBGOAL_THEN `{v:real^N} face_of t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FACE_OF_SING]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S6LV_SEGMENT_SHIFT = prove
 (`!(FF:(real^2->bool)->bool) (L:(real^2->bool)->real^2->real^1) B
    (H:real^2->real^1) (d:real^2) lam u y s.
     FINITE FF /\ convex u /\ u SUBSET UNIONS FF /\ H continuous_on u /\
     (!k. k IN FF ==> linear (L k) /\ L k d = lam /\
                     !z. z IN k ==> H z = L k z + B k) /\
     y IN u /\ y + s % d IN u /\ &0 <= s
     ==> H(y + s % d) = H y + s % lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,lift s] ==> y + drop t % (d:real^2) IN u`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
     [SUBGOAL_THEN `drop t = &0` SUBST1_TAC THENL
       [UNDISCH_TAC `s = &0` THEN UNDISCH_TAC `&0 <= drop t` THEN
        UNDISCH_TAC `drop t <= s` THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `y + drop t % (d:real^2) =
      (&1 - drop t / s) % y + (drop t / s) % (y + s % d)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `convex (u:real^2->bool)` THEN REWRITE_TAC[convex] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `~(s = &0)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `drop t <= s` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t:real^1. (H:real^2->real^1)(y + drop t % d) - drop t % lam`;
    `interval[vec 0:real^1,lift s]`] CONTINUOUS_FINITE_RANGE_CONSTANT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONNECTED_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\t:real^1. (H:real^2->real^1)(y + drop t % d)) =
          H o (\t. y + drop t % d)`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
          REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^2->bool` THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID]];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\k:real^2->bool. (L:(real^2->bool)->real^2->real^1) k y + B k) FF` THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      SUBGOAL_THEN `y + drop t % (d:real^2) IN UNIONS FF` MP_TAC THENL
       [UNDISCH_TAC `(u:real^2->bool) SUBSET UNIONS FF` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (MP_TAC o SPEC `y + drop t % (d:real^2)`))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^1` (fun th ->
    MP_TAC(SPEC `lift s` th) THEN MP_TAC(SPEC `vec 0:real^1` th))) THEN
  REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1; DROP_VEC; LIFT_DROP] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_SUB_RZERO] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN VECTOR_ARITH_TAC);;

let MOI_S6LV_ORTHO_2 = prove
 (`!d w:real^2.
     ~(d = vec 0) /\ vector[--(d$2); d$1] dot w = &0
     ==> w = ((d dot w) / (d dot d)) % d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((d:real^2) dot d = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `vector[--((d:real^2)$2); d$1] dot (w:real^2) = &0` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; DOT_2; VECTOR_2; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_FIELD);;

(* A homeomorphism y |-> (H y, k y) of an open set u onto an open set makes *)
(* k a line chart of each level set of H in u.                               *)

let MOI_S6LV_SLICE_CHART = prove
 (`!(H:real^2->real^1) (k:real^2->real^1) g u e.
     open (IMAGE (\y. pastecart (H y) (k y)) u) /\ k continuous_on u /\
     homeomorphism (u,IMAGE (\y. pastecart (H y) (k y)) u)
                   ((\y. pastecart (H y) (k y)),g)
     ==> homeomorphism ({y | y IN u /\ H y = e},IMAGE k {y | y IN u /\ H y = e})
                       (k,(\t. g(pastecart e t))) /\
         open (IMAGE k {y | y IN u /\ H y = e})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!y. y IN u /\ (H:real^2->real^1) y = e
        ==> (g:real^(1,1)finite_sum->real^2)(pastecart e ((k:real^2->real^1) y)) = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (k:real^2->real^1) {y | y IN u /\ (H:real^2->real^1) y = e} =
    {t | pastecart e t IN IMAGE (\y. pastecart (H y) (k y)) u}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; PASTECART_INJ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN
       `(\t:real^1. (g:real^(1,1)finite_sum->real^2)(pastecart e t)) =
        g o (\t. pastecart e t)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (\y. pastecart ((H:real^2->real^1) y) ((k:real^2->real^1) y)) u` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        ASM_REWRITE_TAC[IN_ELIM_THM]]];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID]]);;

(* The local lemma.  The carrier t of x lies in every simplex through x; a *)
(* vertex v of t has H v <> e = H x, which gives p, q in t with H p < H q;  *)
(* every piece through x has slope lam = H q - H p along d = q - p.  On a   *)
(* ball meeting only the simplices through x, H(y + s d) = H y + s lam, so  *)
(* phi y = (H y, n dot y) with n orthogonal to d is injective, and          *)
(* invariance of domain makes it a homeomorphism onto an open set.          *)

let MOI_S6LV_LEVEL_LOCAL = prove
 (`!(K:(real^2->bool)->bool) (H:real^2->real^1) e x r.
     simplicial_complex K /\
     (!s. s IN K ==> ?l b. linear l /\ !z. z IN s ==> H z = l z + b) /\
     (!v. {v} IN K ==> ~(H v = e)) /\
     H continuous_on UNIONS K /\
     &0 < r /\ ball(x,r) SUBSET UNIONS K /\ H x = e
     ==> ?u (k:real^2->real^1) k'.
           open u /\ x IN u /\ u SUBSET ball(x,r) /\
           homeomorphism ({y | y IN u /\ H y = e},
                          IMAGE k {y | y IN u /\ H y = e}) (k,k') /\
           open (IMAGE k {y | y IN u /\ H y = e})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> t = `linear:(real^2->real^1)->bool`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^2->bool)->real^2->real^1`
    (X_CHOOSE_THEN `B:(real^2->bool)->real^1` (LABEL_TAC "pieces"))) THEN
  SUBGOAL_THEN `(x:real^2) IN UNIONS K` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(x:real^2,r) SUBSET UNIONS K` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^2) IN b ==> b SUBSET s ==> x IN s`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `x:real^2`] MOI_S6LV_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2) IN t` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^2) IN relative_interior t` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `t:real^2->bool`] MOI_S6LV_SIMPLEX_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^2) IN t` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `?p q:real^2. p IN t /\ q IN t /\ drop((H:real^2->real^1) p) < drop(H q)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(drop((H:real^2->real^1) v) = drop(H x))` MP_TAC THENL
     [REWRITE_TAC[DROP_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH `~(a = b) ==> a < b \/ b < a`)) THENL
     [MAP_EVERY EXISTS_TAC [`v:real^2`; `x:real^2`];
      MAP_EVERY EXISTS_TAC [`x:real^2`; `v:real^2`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN K /\ (x:real^2) IN s
        ==> (L:(real^2->bool)->real^2->real^1) s (q - p) = (H:real^2->real^1) q - H p`
  (LABEL_TAC "slope") THENL
   [X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^2) IN s /\ (q:real^2) IN s` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(t:real^2->bool) SUBSET s` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`(p:real^2) IN t`; `(q:real^2) IN t`] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "pieces" (fun th -> MP_TAC(MP (SPEC `s:real^2->bool` th)
      (ASSUME `(s:real^2->bool) IN K`))) THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
    ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d:real^2 = q - p` THEN
  ABBREV_TAC `lam:real^1 = (H:real^2->real^1) q - H p` THEN
  SUBGOAL_THEN `~(d:real^2 = vec 0) /\ ~(lam:real^1 = vec 0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d"; "lam"] THEN
    REWRITE_TAC[VECTOR_SUB_EQ; GSYM DROP_EQ] THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `drop((H:real^2->real^1) p) < drop(H p)` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `drop((H:real^2->real^1) p) < drop(H q)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r1. &0 < r1 /\ r1 <= r /\
         !y s. y IN ball(x:real^2,r1) /\ s IN K /\ y IN s ==> x IN s`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (UNIONS {s | s IN K /\ ~((x:real^2) IN s)})` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]];
      ALL_TAC] THEN
    REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r r2` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `s:real^2->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN ball(x,r2)` MP_TAC THENL
     [UNDISCH_TAC `(y:real^2) IN ball(x,min r r2)` THEN
      REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ball(x:real^2,r2) SUBSET
                 (:real^2) DIFF UNIONS {s | s IN K /\ ~((x:real^2) IN s)}` THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^2,r1) SUBSET ball(x,r) /\ ball(x,r1) SUBSET UNIONS K`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[SUBSET_BALL]; ASM_MESON_TAC[SUBSET_BALL; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y s. y IN ball(x:real^2,r1) /\ y + s % d IN ball(x,r1) /\ &0 <= s
          ==> (H:real^2->real^1)(y + s % d) = H y + s % lam`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S6LV_SEGMENT_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`{s:real^2->bool | s IN K /\ (x:real^2) IN s}`;
                          `L:(real^2->bool)->real^2->real^1`; `B:(real^2->bool)->real^1`;
                          `ball(x:real^2,r1)`] THEN
    ASM_REWRITE_TAC[CONVEX_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^2) IN UNIONS K` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS K:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
      USE_THEN "pieces" (fun th -> MP_TAC(MP (SPEC `s:real^2->bool` th)
        (ASSUME `(s:real^2->bool) IN K`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "slope" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `n:real^2 = vector[--((d:real^2)$2); d$1]` THEN
  ABBREV_TAC `phi = \y:real^2. pastecart ((H:real^2->real^1) y) (lift(n dot y))` THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN ball(x:real^2,r1) /\ y2 IN ball(x,r1) /\
            (phi:real^2->real^(1,1)finite_sum) y1 = phi y2
            ==> y1 = y2`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y1:real^2`; `y2:real^2`] THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[PASTECART_INJ; LIFT_EQ] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d:real^2`; `y2 - y1:real^2`] MOI_S6LV_ORTHO_2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[DOT_RSUB; REAL_SUB_0]; ALL_TAC] THEN
    ABBREV_TAC `s0 = ((d:real^2) dot (y2 - y1)) / (d dot d)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `y2:real^2 = y1 + s0 % d` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `y2 - y1:real^2 = s0 % d` THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&0 <= s0` THENL
     [USE_THEN "mono" (MP_TAC o SPECL [`y1:real^2`; `s0:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `s0 % (lam:real^1) = vec 0` MP_TAC THENL
       [UNDISCH_TAC `(H:real^2->real^1) (y1 + s0 % d) = H y1 + s0 % lam` THEN
        UNDISCH_TAC `(H:real^2->real^1) y1 = H (y1 + s0 % d)` THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
      VECTOR_ARITH_TAC;
      USE_THEN "mono" (MP_TAC o SPECL [`y1 + s0 % d:real^2`; `--s0`]) THEN
      REWRITE_TAC[VECTOR_ARITH `(y + s % d) + --s % d:real^2 = y`] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(&0 <= s0)` THEN REAL_ARITH_TAC;
        DISCH_TAC] THEN
      SUBGOAL_THEN `--s0 % (lam:real^1) = vec 0` MP_TAC THENL
       [UNDISCH_TAC `(H:real^2->real^1) y1 = H (y1 + s0 % d) + --s0 % lam` THEN
        UNDISCH_TAC `(H:real^2->real^1) y1 = H (y1 + s0 % d)` THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_NEG_EQ_0] THEN
      UNDISCH_TAC `~(&0 <= s0)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^2->real^(1,1)finite_sum) continuous_on ball(x,r1)` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS K:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_LIFT_DOT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^2->real^(1,1)finite_sum`; `ball(x:real^2,r1)`]
    INVARIANCE_OF_DOMAIN_HOMEOMORPHISM) THEN
  MP_TAC(ISPECL [`phi:real^2->real^(1,1)finite_sum`; `ball(x:real^2,r1)`]
    INVARIANCE_OF_DOMAIN_GEN) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; ARITH; OPEN_BALL] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^(1,1)finite_sum->real^2`) THEN
  MP_TAC(ISPECL [`H:real^2->real^1`; `\y:real^2. lift(n dot y)`;
                 `g:real^(1,1)finite_sum->real^2`; `ball(x:real^2,r1)`; `e:real^1`]
    MOI_S6LV_SLICE_CHART) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_LIFT_DOT]; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ball(x:real^2,r1)`; `\y:real^2. lift(n dot y)`;
                        `\t. (g:real^(1,1)finite_sum->real^2)(pastecart e t)`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL]);;

(* ========================================================================= *)
(* The bicollar coordinate.  LEVEL_COORD: for |t| <= 1 a point              *)
(* is on the level t exactly when it lies in w and its collar coordinate    *)
(* sndcart (rho' y) is t.  SURFACE_ZERO: rho' (z) = (z,0) on the surface.    *)
(* STRIP_OPEN: rho(M x (-1,1)) is open in real^3 (planar charts of M from   *)
(* SURF_CHARTS and invariance of domain).                                    *)
(* ========================================================================= *)

let MOI_S6LV_LEVEL_COORD = prove
 (`!(m:real^N->bool) w (rho:real^(N,1)finite_sum->real^N) rho' t y.
     moi_s26_bicollar m w rho rho' /\ abs t <= &1
     ==> (y IN moi_s26_level m rho t <=> y IN w /\ sndcart(rho' y) = lift t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s26_bicollar; moi_s26_level; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lift t IN interval[--vec 1:real^1,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    UNDISCH_TAC `abs t <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` (X_CHOOSE_THEN `s:real^1`
      (CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
    SUBGOAL_THEN `pastecart (z:real^N) (lift t) IN m PCROSS interval[--vec 1,vec 1]`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (rho:real^(N,1)finite_sum->real^N)
                     (m PCROSS interval[--vec 1,vec 1]) = w` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SNDCART_PASTECART]];
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(rho':real^N->real^(N,1)finite_sum) y IN m PCROSS interval[--vec 1,vec 1]`
    MP_TAC THENL
     [UNDISCH_TAC `IMAGE (rho':real^N->real^(N,1)finite_sum) w =
                   m PCROSS interval[--vec 1,vec 1]` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(rho':real^N->real^(N,1)finite_sum) y` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[];
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING]]]);;

let MOI_S6LV_SURFACE_ZERO = prove
 (`!(m:real^N->bool) w (rho:real^(N,1)finite_sum->real^N) rho' z.
     moi_s26_bicollar m w rho rho' /\ z IN m
     ==> z IN w /\ rho' z = pastecart z (vec 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (z:real^N) (vec 0:real^1) IN m PCROSS interval[--vec 1,vec 1]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho:real^(N,1)finite_sum->real^N) (pastecart z (vec 0)) = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (rho:real^(N,1)finite_sum->real^N)
                   (m PCROSS interval[--vec 1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `pastecart (z:real^N) (vec 0:real^1)` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(rho:real^(N,1)finite_sum->real^N) (pastecart z (vec 0)) = z` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S6LV_OPEN_UNIT = prove
 (`open {t:real^1 | --(&1) < drop t /\ drop t < &1}`,
  SUBGOAL_THEN `{t:real^1 | --(&1) < drop t /\ drop t < &1} = interval(--vec 1,vec 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC];
    REWRITE_TAC[OPEN_INTERVAL]]);;

let MOI_S6LV_STRIP_OPEN = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_s26_bicollar (UNIONS c) w rho rho'
     ==> open (IMAGE rho (UNIONS c PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` SURF_CHARTS) THEN
  ASM_SIMP_TAC[MOI_S8TA_CM_CMB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o CONJUNCT2)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIFF_EMPTY] THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s26_bicollar (UNIONS c) w (rho:real^(3,1)finite_sum->real^3) rho'` THEN
  REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ABBREV_TAC `J = {t:real^1 | --(&1) < drop t /\ drop t < &1}` THEN
  SUBGOAL_THEN `open (J:real^1->bool) /\ J SUBSET interval[--vec 1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[MOI_S6LV_OPEN_UNIT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `t:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s28_locally_r2")) (concl th))) THEN
  ASM_REWRITE_TAC[moi_s28_locally_r2; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `phi:real^3->real^2`
      (X_CHOOSE_TAC `phi':real^2->real^3`))))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (A:real^3->bool,(:real^2)) (phi,phi')`) (concl th))) THEN
  SUBGOAL_THEN `(A:real^3->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ABBREV_TAC
   `Fm = \q:real^(2,1)finite_sum.
          (rho:real^(3,1)finite_sum->real^3) (pastecart (phi'(fstcart q)) (sndcart q))` THEN
  EXISTS_TAC `IMAGE (Fm:real^(2,1)finite_sum->real^3) ((:real^2) PCROSS J)` THEN
  SUBGOAL_THEN
   `!q. q IN (:real^2) PCROSS J
        ==> pastecart ((phi':real^2->real^3)(fstcart q)) (sndcart q) IN
            UNIONS c PCROSS interval[--vec 1:real^1,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_UNIV] THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `(A:real^3->bool) SUBSET UNIONS c` THEN
      UNDISCH_TAC `IMAGE (phi':real^2->real^3) (:real^2) = A` THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; DIMINDEX_3; LE_REFL] THEN
    REWRITE_TAC[ARITH] THEN
    SUBGOAL_THEN `open ((:real^2) PCROSS (J:real^1->bool))` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Fm" THEN
      SUBGOAL_THEN
       `(\q:real^(2,1)finite_sum.
          (rho:real^(3,1)finite_sum->real^3) (pastecart (phi'(fstcart q)) (sndcart q))) =
        rho o (\q. pastecart ((phi':real^2->real^3)(fstcart q)) (sndcart q))`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        SUBGOAL_THEN
         `(\q:real^(2,1)finite_sum. (phi':real^2->real^3)(fstcart q)) = phi' o fstcart`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS (c:(real^3->bool)->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN FIRST_ASSUM ACCEPT_TAC];
      EXPAND_TAC "Fm" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV;
        FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`a1:real^2`; `t1:real^1`; `a2:real^2`; `t2:real^1`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `!p1 p2. p1 IN UNIONS c PCROSS interval[--vec 1:real^1,vec 1] /\
                p2 IN UNIONS c PCROSS interval[--vec 1,vec 1] /\
                (rho:real^(3,1)finite_sum->real^3) p1 = rho p2 ==> p1 = p2`
      (LABEL_TAC "rinj") THENL
       [MP_TAC(ASSUME `!x. x IN UNIONS c PCROSS interval[--vec 1:real^1,vec 1]
                           ==> (rho':real^3->real^(3,1)finite_sum)
                                 ((rho:real^(3,1)finite_sum->real^3) x) = x`) THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!a1 a2:real^2. (phi':real^2->real^3) a1 = phi' a2 ==> a1 = a2`
      (LABEL_TAC "pinj") THENL
       [MP_TAC(ASSUME `!y. y IN (:real^2)
                           ==> (phi:real^3->real^2) ((phi':real^2->real^3) y) = y`) THEN
        REWRITE_TAC[IN_UNIV] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!a:real^2 s:real^1. s IN J
            ==> pastecart ((phi':real^2->real^3) a) s IN
                UNIONS c PCROSS interval[--vec 1:real^1,vec 1]`
      (LABEL_TAC "mem") THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
        MAP_EVERY UNDISCH_TAC
         [`(s:real^1) IN J`; `(J:real^1->bool) SUBSET interval[--vec 1,vec 1]`;
          `(A:real^3->bool) SUBSET UNIONS c`; `IMAGE (phi':real^2->real^3) (:real^2) = A`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `pastecart ((phi':real^2->real^3) a1) (t1:real^1) = pastecart (phi' a2) t2`
      MP_TAC THENL
       [USE_THEN "rinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN USE_THEN "mem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[PASTECART_INJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PASTECART_INJ] THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `pastecart ((phi:real^3->real^2) z) (t:real^1)` THEN
    EXPAND_TAC "Fm" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
    ASM_SIMP_TAC[];
    EXPAND_TAC "Fm" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
      PASTECART_IN_PCROSS; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`a:real^2`; `s:real^1`] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `pastecart ((phi':real^2->real^3) a) (s:real^1)` THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    MAP_EVERY UNDISCH_TAC
     [`(s:real^1) IN J`; `{t:real^1 | --(&1) < drop t /\ drop t < &1} = J`;
      `(A:real^3->bool) SUBSET UNIONS c`; `IMAGE (phi':real^2->real^3) (:real^2) = A`] THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* The part P of the triangle mapped into the bicollar.  W is a              *)
(* PL polyhedron; the preimage of a PL polyhedron under a PL map on a       *)
(* compact set is a PL polyhedron; P carries a triangulation on whose       *)
(* simplices the collar coordinate sndcart o rho' o f is affine; a level e  *)
(* in (0,1) missed by finitely many values.                                  *)
(* ========================================================================= *)

let MOI_S6LV_W_POLYHEDRON = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_s26_bicollar (UNIONS c) w rho rho'
     ==> pl_polyhedron w /\ compact w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `interval[--vec 1:real^1,vec 1]`]
    MOI_S8CU_PCROSS_POLYHEDRON) THEN
  ASM_SIMP_TAC[MOI_FSA_CM_SC; POLYTOPE_INTERVAL] THEN STRIP_TAC THEN
  UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                 (UNIONS c PCROSS interval[--vec 1,vec 1]) = w` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_S6LV_PIECES_PREIMAGE = prove
 (`!(f:real^M->real^N) s D w.
     FINITE D /\ s SUBSET UNIONS D /\
     (!k. k IN D ==> polytope k /\ k SUBSET s /\
                     ?l y. linear l /\ !z. z IN k ==> f z = l z + y) /\
     pl_polyhedron w
     ==> pl_polyhedron {x | x IN s /\ f x IN w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_AND_EXISTS_THM; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `D:(real^M->bool)->bool`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^M->bool)->real^M->real^N`
    (X_CHOOSE_TAC `Y:(real^M->bool)->real^N`)) THEN
  UNDISCH_TAC `pl_polyhedron (w:real^N->bool)` THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `{k INTER {z | (L:(real^M->bool)->real^M->real^N) k z + Y k IN q} |
     k IN D /\ q IN E}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `q:real^N->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `L:(real^M->bool)->real^M->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON] THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYHEDRON_INTER THEN ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON] THEN
      MATCH_MP_TAC MOI_PLM_POLYHEDRON_AFFINE_PREIMAGE THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON; ETA_AX];
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_BOUNDED] THEN SET_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^M` THEN
    REWRITE_TAC[IN_ELIM_THM; UNIONS_GSPEC] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `?k. k IN D /\ (x:real^M) IN k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(s:real^M->bool) SUBSET UNIONS D` THEN
        UNDISCH_TAC `(x:real^M) IN s` THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?q. q IN E /\ (f:real^M->real^N) x IN q` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(f:real^M->real^N) x IN w` THEN
        UNDISCH_TAC `(w:real^N->bool) = UNIONS E` THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `q:real^N->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `L:(real^M->bool)->real^M->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(L:(real^M->bool)->real^M->real^N) k x + Y k = f x` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `q:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `(x:real^M) IN k INTER
                   {z | (L:(real^M->bool)->real^M->real^N) k z + Y k IN q}` THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `L:(real^M->bool)->real^M->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^M) IN k`; `(k:real^M->bool) SUBSET s`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(w:real^N->bool) = UNIONS E` THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `q:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f:real^M->real^N) x = (L:(real^M->bool)->real^M->real^N) k x + Y k` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]]);;

let MOI_S6LV_PREIMAGE_POLYHEDRON = prove
 (`!(f:real^M->real^N) s w.
     compact s /\ pl_map_on s f /\ pl_polyhedron w
     ==> pl_polyhedron {x | x IN s /\ f x IN w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^N`]
    MOI_PLT_PL_MAP_ON_COMPACT_PIECES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S6LV_PIECES_PREIMAGE THEN
  EXISTS_TAC `D:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* P, the collar coordinate, and a triangulation adapted to it. *)

let MOI_S6LV_COORD_PL = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'
    (f:real^2->real^3).
     FINITE c /\ combinatorial_manifold 2 c /\
     moi_s26_bicollar (UNIONS c) w rho rho' /\ pl_map_on std_triangle f
     ==> pl_polyhedron {x | x IN std_triangle /\ f x IN w} /\
         pl_map_on {x | x IN std_triangle /\ f x IN w} (rho' o f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                 `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`]
    MOI_S6LV_W_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron {x | x IN std_triangle /\ (f:real^2->real^3) x IN w}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6LV_PREIMAGE_POLYHEDRON THEN
    ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
  EXISTS_TAC `w:real^3->bool` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN SET_TAC[];
    UNDISCH_TAC `moi_s26_bicollar (UNIONS c) w (rho:real^(3,1)finite_sum->real^3) rho'` THEN
    SIMP_TAC[moi_s26_bicollar; pl_homeomorphism];
    SET_TAC[]]);;

let MOI_S6LV_TRIANGULATE = prove
 (`!(P:real^2->bool) (g:real^2->real^(3,1)finite_sum).
     pl_polyhedron P /\ pl_map_on P g
     ==> ?K. simplicial_complex K /\ UNIONS K = P /\
             !s. s IN K ==> ?l b. linear l /\ !z. z IN s ==> sndcart(g z) = l z + b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX]) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K0:(real^2->bool)->bool`; `g:real^2->real^(3,1)finite_sum`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^2->bool` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `linear:(real^2->real^(3,1)finite_sum)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^(3,1)finite_sum`
    (X_CHOOSE_THEN `y:real^(3,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(sndcart:real^(3,1)finite_sum->real^1) o (l:real^2->real^(3,1)finite_sum)`;
                        `sndcart(y:real^(3,1)finite_sum)`] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; LINEAR_SNDCART; o_THM; SNDCART_ADD]);;

let MOI_S6LV_GENERIC_LEVEL = prove
 (`!s:real^1->bool.
     FINITE s ==> ?e. &0 < e /\ e < &1 /\ ~(lift e IN s) /\ ~(lift(--e) IN s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE ((s:real^1->bool) UNION IMAGE (\x:real^1. --x) s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(interval(vec 0:real^1,vec 1) SUBSET s UNION IMAGE (\x:real^1. --x) s)`
  MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`interval(vec 0:real^1,vec 1)`;
                   `(s:real^1->bool) UNION IMAGE (\x:real^1. --x) s`] FINITE_SUBSET) THEN
    ASM_REWRITE_TAC[FINITE_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_UNION; DE_MORGAN_THM;
              IN_INTERVAL_1; DROP_VEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop t` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  UNDISCH_TAC `~((t:real^1) IN IMAGE (\x. --x) s)` THEN
  REWRITE_TAC[IN_IMAGE; CONTRAPOS_THM] THEN DISCH_TAC THEN
  EXISTS_TAC `lift(--drop t)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_NEG; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The level set and the main theorem.  LEVEL_SET: the set of the statement  *)
(* is the level set of the collar coordinate at +-e on P.  OFF_FRAME: it     *)
(* lies in the interior of the triangle (coordinate 0 on the frame).         *)
(* IN_STRIP: its image lies in the open strip.  NEAR_BALL: each of its       *)
(* points has a ball inside P on which the other level is not attained.      *)
(* LEVEL_CHARTS: line charts.  LEVEL_CIRCLES: the components are the         *)
(* circles.                                                                  *)
(* ========================================================================= *)

let MOI_S6LV_TRIANGLE_FACTS = prove
 (`relative_interior std_triangle = interior std_triangle /\
   open (interior std_triangle) /\ interior std_triangle SUBSET std_triangle /\
   relative_frontier std_triangle = std_triangle DIFF interior std_triangle`,
  SUBGOAL_THEN `relative_interior std_triangle = interior std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN
    MATCH_MP_TAC AFF_DIM_SIMPLEX THEN REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR; INTERIOR_SUBSET; relative_frontier] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC]);;

let MOI_S6LV_LEVEL_SET = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' (f:real^2->real^3) e.
     moi_s26_bicollar m w rho rho' /\ &0 < e /\ e < &1
     ==> {x | x IN std_triangle /\
              f x IN moi_s26_level m rho e UNION moi_s26_level m rho (--e)} =
         {x | x IN {x | x IN std_triangle /\ f x IN w} /\
              (sndcart(rho'(f x)) = lift e \/ sndcart(rho'(f x)) = lift(--e))}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs e <= &1 /\ abs(--e) <= &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < e`; `e < &1`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
  MP_TAC(ISPECL [`m:real^3->bool`; `w:real^3->bool`; `rho:real^(3,1)finite_sum->real^3`;
                 `rho':real^3->real^(3,1)finite_sum`; `e:real`; `(f:real^2->real^3) x`]
    MOI_S6LV_LEVEL_COORD) THEN
  MP_TAC(ISPECL [`m:real^3->bool`; `w:real^3->bool`; `rho:real^(3,1)finite_sum->real^3`;
                 `rho':real^3->real^(3,1)finite_sum`; `--e`; `(f:real^2->real^3) x`]
    MOI_S6LV_LEVEL_COORD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN MESON_TAC[]);;

let MOI_S6LV_OFF_FRAME = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'
    (f:real^2->real^3) x.
     moi_s26_bicollar (UNIONS c) w rho rho' /\
     IMAGE f (relative_frontier std_triangle) SUBSET UNIONS c /\
     x IN std_triangle /\ ~(sndcart(rho'(f x)) = vec 0)
     ==> x IN interior std_triangle`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^2) IN interior std_triangle` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:real^2->real^3) x IN UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^3) (relative_frontier std_triangle) SUBSET UNIONS c` THEN
    REWRITE_TAC[MOI_S6LV_TRIANGLE_FACTS; SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `w:real^3->bool`;
                 `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`;
                 `(f:real^2->real^3) x`] MOI_S6LV_SURFACE_ZERO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) x)) = vec 0)` THEN
  ASM_REWRITE_TAC[SNDCART_PASTECART]);;

let MOI_S6LV_TWO_LEVELS = prove
 (`!e a (z:real^1).
     abs a = e ==> ((z = lift e \/ z = lift(--e)) <=> (z = lift a \/ z = lift(--a)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC o
    MATCH_MP (REAL_ARITH `abs a = e ==> e = a \/ e = --a`)) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN MESON_TAC[]);;

let MOI_S6LV_IN_STRIP = prove
 (`!(m:real^N->bool) w (rho:real^(N,1)finite_sum->real^N) rho' y.
     moi_s26_bicollar m w rho rho' /\ y IN w /\ abs(drop(sndcart(rho' y))) < &1
     ==> y IN IMAGE rho (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(rho':real^N->real^(N,1)finite_sum) y IN m PCROSS interval[--vec 1,vec 1]`
  MP_TAC THENL
   [UNDISCH_TAC `IMAGE (rho':real^N->real^(N,1)finite_sum) w =
                 m PCROSS interval[--vec 1,vec 1]` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `(rho':real^N->real^(N,1)finite_sum) y` THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM] THEN
  UNDISCH_TAC `abs(drop(sndcart((rho':real^N->real^(N,1)finite_sum) y))) < &1` THEN
  REAL_ARITH_TAC);;

let MOI_S6LV_NEAR_BALL = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'
    (f:real^2->real^3) x a.
     FINITE c /\ combinatorial_manifold 2 c /\
     moi_s26_bicollar (UNIONS c) w rho rho' /\
     pl_map_on std_triangle f /\
     IMAGE f (relative_frontier std_triangle) SUBSET UNIONS c /\
     &0 < abs a /\ abs a < &1 /\
     x IN std_triangle /\ f x IN w /\ sndcart(rho'(f x)) = lift a
     ==> ?r. &0 < r /\ ball(x,r) SUBSET {x | x IN std_triangle /\ f x IN w} /\
             !y. y IN ball(x,r) ==> ~(sndcart(rho'(f y)) = lift(--a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                 `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`;
                 `f:real^2->real^3`] MOI_S6LV_COORD_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN interior std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6LV_OFF_FRAME THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                          `rho:real^(3,1)finite_sum->real^3`;
                          `rho':real^3->real^(3,1)finite_sum`; `f:real^2->real^3`] THEN
    ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
    UNDISCH_TAC `&0 < abs a` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (rho:real^(3,1)finite_sum->real^3)
                    (UNIONS c PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1})` THEN
  SUBGOAL_THEN `open (S:real^3->bool) /\ S SUBSET w /\ (f:real^2->real^3) x IN S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S6LV_STRIP_OPEN THEN
      EXISTS_TAC `w:real^3->bool` THEN EXISTS_TAC `rho':real^3->real^(3,1)finite_sum` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s26_bicollar (UNIONS c) w (rho:real^(3,1)finite_sum->real^3) rho'` THEN
      REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                     (UNIONS c PCROSS interval[--vec 1,vec 1]) = w` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_S6LV_IN_STRIP THEN EXISTS_TAC `w:real^3->bool` THEN
      EXISTS_TAC `rho':real^3->real^(3,1)finite_sum` THEN
      ASM_REWRITE_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) y))) continuous_on
    {x | x IN std_triangle /\ f x IN w}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) y))) =
      sndcart o (rho' o f)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {y | y IN interior std_triangle /\ (f:real^2->real^3) y IN S} /\
    closed {y | y IN {x | x IN std_triangle /\ (f:real^2->real^3) x IN w} /\
                (\y. sndcart((rho':real^3->real^(3,1)finite_sum)(f y))) y IN {lift(--a)}}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[MOI_S6LV_TRIANGLE_FACTS] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON; MOI_S6LV_TRIANGLE_FACTS];
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC[CLOSED_SING; COMPACT_IMP_CLOSED; PL_POLYHEDRON_IMP_COMPACT]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{y | y IN interior std_triangle /\ (f:real^2->real^3) y IN S} DIFF
                {y | y IN {x | x IN std_triangle /\ (f:real^2->real^3) x IN w} /\
                     (\y. sndcart((rho':real^3->real^(3,1)finite_sum)(f y))) y IN
                     {lift(--a)}}`
    OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_DIFF] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_SING] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
    UNDISCH_TAC `&0 < abs a` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `ball(x:real^2,r) SUBSET s`) (concl th))) THEN
  MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_S6LV_TRIANGLE_FACTS))) THEN
  UNDISCH_TAC `(S:real^3->bool) SUBSET w` THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; IN_SING] THEN MESON_TAC[]);;

let MOI_S6LV_LEVEL_CHARTS = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'
    (f:real^2->real^3) (K:(real^2->bool)->bool) e.
     FINITE c /\ combinatorial_manifold 2 c /\
     moi_s26_bicollar (UNIONS c) w rho rho' /\
     pl_map_on std_triangle f /\
     IMAGE f (relative_frontier std_triangle) SUBSET UNIONS c /\
     &0 < e /\ e < &1 /\
     simplicial_complex K /\ UNIONS K = {x | x IN std_triangle /\ f x IN w} /\
     (!s. s IN K ==> ?l b. linear l /\ !z. z IN s ==> sndcart(rho'(f z)) = l z + b) /\
     (!v. {v} IN K ==> ~(sndcart(rho'(f v)) = lift e) /\
                       ~(sndcart(rho'(f v)) = lift(--e)))
     ==> moi_s4l_line_charts
           {x | x IN {x | x IN std_triangle /\ f x IN w} /\
                (sndcart(rho'(f x)) = lift e \/ sndcart(rho'(f x)) = lift(--e))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                 `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`;
                 `f:real^2->real^3`] MOI_S6LV_COORD_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4l_line_charts] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?a. sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) x)) = lift a /\
        abs a = e`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [EXISTS_TAC `e:real`; EXISTS_TAC `--e`] THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG] THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                 `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`;
                 `f:real^2->real^3`; `x:real^2`; `a:real`] MOI_S6LV_NEAR_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < e`; `e < &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`;
                 `\y. sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) y))`;
                 `lift a`; `x:real^2`; `r:real`] MOI_S6LV_LEVEL_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`e:real`; `a:real`;
                     `sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) v))`]
        MOI_S6LV_TWO_LEVELS) THEN
      ASM_SIMP_TAC[] THEN MESON_TAC[];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      SUBGOAL_THEN
       `(\y. sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) y))) =
        (\z. sndcart z + vec 0) o (rho' o f)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF; FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
      EXISTS_TAC `IMAGE ((rho':real^3->real^(3,1)finite_sum) o (f:real^2->real^3))
                        {x | x IN std_triangle /\ f x IN w}` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      REWRITE_TAC[LINEAR_SNDCART] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2->bool` (X_CHOOSE_THEN `k:real^2->real^1`
    (X_CHOOSE_THEN `k':real^1->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`u:real^2->bool`; `k:real^2->real^1`; `k':real^1->real^2`] THEN
  SUBGOAL_THEN
   `{x | (x IN std_triangle /\ (f:real^2->real^3) x IN w) /\
         (sndcart((rho':real^3->real^(3,1)finite_sum)(f x)) = lift e \/
          sndcart(rho'(f x)) = lift(--e))} INTER u =
    {y | y IN u /\ (\y. sndcart(rho'(f y))) y = lift a}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN
    ASM_CASES_TAC `(y:real^2) IN u` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^2) IN ball(x,r)` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^2->bool) SUBSET ball(x,r)` THEN
      UNDISCH_TAC `(y:real^2) IN u` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^2) IN std_triangle /\ (f:real^2->real^3) y IN w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ball(x:real^2,r) SUBSET {x | x IN std_triangle /\ (f:real^2->real^3) x IN w}` THEN
      UNDISCH_TAC `(y:real^2) IN ball(x,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`e:real`; `a:real`;
                   `sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) y))`]
      MOI_S6LV_TWO_LEVELS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) y)) =
                    lift(--a))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The main theorem. *)

let LEVEL_CIRCLES = prove
 (MOI_S26_LEVEL_CIRCLES,
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                       `rho:real^(3,1)finite_sum->real^3`;
                       `rho':real^3->real^(3,1)finite_sum`; `f:real^2->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                 `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`;
                 `f:real^2->real^3`] MOI_S6LV_COORD_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{x | x IN std_triangle /\ (f:real^2->real^3) x IN w}`;
                 `(rho':real^3->real^(3,1)finite_sum) o (f:real^2->real^3)`]
    MOI_S6LV_TRIANGULATE) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC
   `IMAGE (\v. sndcart((rho':real^3->real^(3,1)finite_sum)((f:real^2->real^3) v)))
          {v | {v} IN (K:(real^2->bool)->bool)}`
    MOI_S6LV_GENERIC_LEVEL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ THEN
    CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `L = {x | x IN {x | x IN std_triangle /\ (f:real^2->real^3) x IN w} /\
             (sndcart((rho':real^3->real^(3,1)finite_sum)(f x)) = lift e \/
              sndcart(rho'(f x)) = lift(--e))}` THEN
  SUBGOAL_THEN `pl_polyhedron (L:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `L = {x | x IN {x | x IN std_triangle /\ (f:real^2->real^3) x IN w} /\
               (\x. sndcart((rho':real^3->real^(3,1)finite_sum)(f x))) x IN
               {lift e,lift(--e)}}`
    SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S6LV_PIECES_PREIMAGE THEN
    EXISTS_TAC `K:(real^2->bool)->bool` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      UNDISCH_TAC `UNIONS K = {x | x IN std_triangle /\ (f:real^2->real^3) x IN w}` THEN
      SET_TAC[];
      X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE];
        UNDISCH_TAC `UNIONS K = {x | x IN std_triangle /\ (f:real^2->real^3) x IN w}` THEN
        UNDISCH_TAC `(s:real^2->bool) IN K` THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[pl_polyhedron] THEN
      EXISTS_TAC `{{lift e},{lift(--e)}}:(real^1->bool)->bool` THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                  POLYTOPE_SING; UNIONS_2] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4l_line_charts (L:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC MOI_S6LV_LEVEL_CHARTS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `rho:real^(3,1)finite_sum->real^3`;
                          `K:(real^2->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `L:real^2->bool` MOI_S4L_LINE_CHART_CIRCLES) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `components (L:real^2->bool)`] THEN
  ASM_REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `L:real^2->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[MOI_S6LV_TRIANGLE_FACTS] THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S6LV_OFF_FRAME THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w:real^3->bool`;
                          `rho:real^(3,1)finite_sum->real^3`;
                          `rho':real^3->real^(3,1)finite_sum`; `f:real^2->real^3`] THEN
    ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `w:real^3->bool`;
                   `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`;
                   `f:real^2->real^3`; `e:real`] MOI_S6LV_LEVEL_SET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS]]);;

