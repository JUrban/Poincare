(* ========================================================================= *)
(* pc_moi_fnd_sgn: the side of a surface in real^3 and the sign of its       *)
(* triangles, used by pc_moi_fnd_sptrace and by the orientability file       *)
(* pc_moi_fnd_sides. Contents:                                               *)
(*   -   connected sets in one of two open sets; the two half-balls of a    *)
(*       flat piece of a surface lie in different local sides;              *)
(*   -   open sectors between two half-planes about an axis in real^3;      *)
(*   -   local structure of a combinatorial surface near relative interior  *)
(*       points of its triangles (one plane) and edges (two pages);         *)
(*   -   moi_fstr_sides (two open sides D, E of the surface in a ball),     *)
(*       moi_fstr_posn, the sign moi_fstr_sg of an ordered triangle at v:   *)
(*       values +-1 and antisymmetry (MOI_FSTR_SG_SWAP);                     *)
(*   -   opposite signs of the two triangles at an edge through v           *)
(*       (MOI_FSTR_SG_EDGE).                                                 *)
(* ========================================================================= *)

let moi_fstr_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := moi_fstr_saved_interface;;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_smo_base.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic geometry in real^3: the two open half-balls of a plane lie in    *)
(* different sides of a two-sided set, and the two open sectors between two *)
(* half-planes bounded by a common line (ccw order around the axis t).      *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_CONNECTED_IN_ONE = prove
 (`!s e1 e2:real^N->bool.
     connected s /\ open e1 /\ open e2 /\ DISJOINT e1 e2 /\ s SUBSET e1 UNION e2
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (e1:real^N->bool) e2` THEN
  UNDISCH_TAC `(s:real^N->bool) SUBSET e1 UNION e2` THEN SET_TAC[]);;

(* If a set M is a plane through y near y, the two half-balls at y lie in   *)
(* different members of an open separation D, E accumulating at y.         *)
let MOI_FSTR_HALF_BALLS = prove
 (`!(D:real^3->bool) E M y n e.
     open D /\ open E /\ DISJOINT D E /\ ball(y,e) DIFF M SUBSET D UNION E /\
     y IN closure D /\ y IN closure E /\ ~(n = vec 0) /\ &0 < e /\
     M INTER ball(y,e) SUBSET {z | n dot (z - y) = &0}
     ==> ({z | z IN ball(y,e) /\ &0 < n dot (z - y)} SUBSET D /\
          {z | z IN ball(y,e) /\ n dot (z - y) < &0} SUBSET E) \/
         ({z | z IN ball(y,e) /\ &0 < n dot (z - y)} SUBSET E /\
          {z | z IN ball(y,e) /\ n dot (z - y) < &0} SUBSET D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `hp = {z:real^3 | z IN ball(y,e) /\ &0 < n dot (z - y)}` THEN
  ABBREV_TAC `hm = {z:real^3 | z IN ball(y,e) /\ n dot (z - y) < &0}` THEN
  SUBGOAL_THEN `connected(hp:real^3->bool) /\ connected(hm:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THENL
     [EXPAND_TAC "hp"; EXPAND_TAC "hm"] THEN
    REWRITE_TAC[SET_RULE `{z:real^3 | z IN s /\ P z} = s INTER {z | P z}`] THEN
    MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL] THEN
    REWRITE_TAC[DOT_RSUB; REAL_ARITH `&0 < a - b <=> b < a`; REAL_ARITH `a - b < &0 <=> a < b`] THEN
    REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_LT; CONVEX_HALFSPACE_GT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hp:real^3->bool) SUBSET D UNION E /\ (hm:real^3->bool) SUBSET D UNION E`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,e) DIFF M` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
    UNDISCH_TAC `(M:real^3->bool) INTER ball(y,e) SUBSET {z | n dot (z - y) = &0}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  (* an open set meeting ball(y,e) and inside the plane is impossible *)
  SUBGOAL_THEN
   `!U:real^3->bool. open U /\ y IN closure U /\
                     U INTER ball(y,e) SUBSET {z | n dot (z - y) = &0} ==> F`
  ASSUME_TAC THENL
   [X_GEN_TAC `U:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?z:real^3. z IN U INTER ball(y,e)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN closure U` THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE; IN_INTER; IN_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`n:real^3`; `n dot (y:real^3)`] INTERIOR_HYPERPLANE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `!s:real^3->bool. (z:real^3) IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `interior(U INTER ball(y:real^3,e))` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[INTERIOR_OPEN; OPEN_INTER; OPEN_BALL];
      MATCH_MP_TAC SUBSET_INTERIOR THEN
      UNDISCH_TAC `(U:real^3->bool) INTER ball(y,e) SUBSET {z | n dot (z - y) = &0}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; DOT_RSUB] THEN MESON_TAC[REAL_SUB_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hp:real^3->bool`; `D:real^3->bool`; `E:real^3->bool`]
    MOI_FSTR_CONNECTED_IN_ONE) THEN
  MP_TAC(ISPECL [`hm:real^3->bool`; `D:real^3->bool`; `E:real^3->bool`]
    MOI_FSTR_CONNECTED_IN_ONE) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `U:real^3->bool`)) (concl th))) THEN
  FIRST (map (fun u ->
    EXISTS_TAC u THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 < n dot (z - y:real^3)` THENL
     [SUBGOAL_THEN `(z:real^3) IN hp` ASSUME_TAC THENL
       [EXPAND_TAC "hp" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `n dot (z - y:real^3) < &0` THENL
     [SUBGOAL_THEN `(z:real^3) IN hm` ASSUME_TAC THENL
       [EXPAND_TAC "hm" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      ASM SET_TAC[];
      ASM_REAL_ARITH_TAC]) [`E:real^3->bool`; `D:real^3->bool`]));;

(* ------------------------------------------------------------------------- *)
(* Sectors around an axis t in real^3.  With D(u,w) = (t cross u) dot w     *)
(* (the oriented area of the projections to the normal plane of t),         *)
(* moi_fstr_sec t a b w says that w lies in the open sector swept from the  *)
(* half-plane through a to the half-plane through b in the positive sense.  *)
(* ------------------------------------------------------------------------- *)

let moi_fstr_sec = new_definition
 `moi_fstr_sec (t:real^3) (a:real^3) (b:real^3) (w:real^3) <=>
    if &0 < (t cross a) dot b then &0 < (t cross a) dot w /\ &0 < (t cross w) dot b
    else if (t cross a) dot b < &0 then &0 < (t cross a) dot w \/ &0 < (t cross w) dot b
    else &0 < (t cross a) dot w`;;

let MOI_FSTR_D_ANTI = prove
 (`!t w b:real^3. (t cross w) dot b = --((t cross b) dot w)`,
  VEC3_TAC);;

let MOI_FSTR_D_LIN = prove
 (`(!(t:real^3) a s u w. (t cross (s % t + u % a)) dot w = u * ((t cross a) dot w)) /\
   (!(t:real^3) a s u w. (t cross a) dot (s % t + u % w) = u * ((t cross a) dot w)) /\
   (!(t:real^3) a b s u k.
      (t cross (s % t + u % a + k % (t cross a))) dot b =
      u * ((t cross a) dot b) + k * ((t dot a) * (t dot b) - (t dot t) * (a dot b))) /\
   (!(t:real^3) a s u k.
      (t cross a) dot (s % t + u % a + k % (t cross a)) = k * ((t cross a) dot (t cross a)))`,
  REPEAT CONJ_TAC THEN VEC3_TAC);;

(* A vector orthogonal to the normal of the plane spanned by t and a is in it. *)
let MOI_FSTR_PLANE_SPAN = prove
 (`!t a w:real^3.
     ~(t = vec 0) /\ ~(a = vec 0) /\ t dot a = &0 /\ (t cross a) dot w = &0
     ==> ?s u. w = s % t + u % a /\ (&0 <= u <=> &0 <= a dot w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (t cross a) dot (t cross a:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; NORM_CROSS] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t dot (t:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `nn = (t cross a) dot (t cross a:real^3)` THEN
  MP_TAC(VEC3_RULE
   `((t cross a) dot (t cross a)) % (w:real^3) =
    (w dot (a cross (t cross a))) % t + (w dot ((t cross a) cross t)) % a +
    (w dot (t cross a)) % (t cross a)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `w dot (t cross a:real^3) = &0` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `w dot ((t cross a) cross t:real^3) = (t dot t) * (a dot w)` SUBST1_TAC THENL
   [REWRITE_TAC[VEC3_RULE `!t a w:real^3. w dot ((t cross a) cross t) =
                                     (t dot t) * (a dot w) - (t dot a) * (t dot w)`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`((w:real^3) dot (a cross (t cross a))) / nn`;
                        `(((t:real^3) dot t) * ((a:real^3) dot w)) / nn`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `nn:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ]]);;

(* The flat case: the second page is the opposite half-plane. *)
let MOI_FSTR_SEC_FLAT = prove
 (`!t a b:real^3.
     ~(t = vec 0) /\ ~(a = vec 0) /\ t dot a = &0 /\ t dot b = &0 /\
     ~(?s u. &0 <= u /\ b = s % t + u % a) /\ (t cross a) dot b = &0
     ==> ?k. k < &0 /\ b = k % a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3`; `a:real^3`; `b:real^3`] MOI_FSTR_PLANE_SPAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `t dot (b:real^3) = &0` THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_ENTIRE] THEN
    ASM_REWRITE_TAC[DOT_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `u:real` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(?s u. &0 <= u /\ b = s % t + u % (a:real^3))` THEN REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`&0`; `u:real`] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Rewriting with fixed instances of the antisymmetry of D. *)
let MOI_FSTR_DANTI_TAC (l:term list list) =
  MP_TAC(end_itlist CONJ (map (fun x -> ISPECL x MOI_FSTR_D_ANTI) l)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]);;

let MOI_FSTR_MUL_NEG_LT = prove
 (`!x y. x * y < &0 <=> &0 < x /\ y < &0 \/ x < &0 /\ &0 < y`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
  REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

(* The two sectors are disjoint. *)
let MOI_FSTR_SEC_DISJ = prove
 (`!t a b w:real^3.
     ~(t = vec 0) /\ ~(a = vec 0) /\ ~(b = vec 0) /\ t dot a = &0 /\ t dot b = &0 /\
     ~(?s u. &0 <= u /\ b = s % t + u % a) /\ ~(?s u. &0 <= u /\ a = s % t + u % b)
     ==> ~(moi_fstr_sec t a b w /\ moi_fstr_sec t b a w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_fstr_sec] THEN
  MOI_FSTR_DANTI_TAC [[`t:real^3`; `w:real^3`; `b:real^3`];
                      [`t:real^3`; `w:real^3`; `a:real^3`];
                      [`t:real^3`; `b:real^3`; `a:real^3`]] THEN
  ASM_CASES_TAC `(t cross a) dot (b:real^3) = &0` THENL
   [MP_TAC(ISPECL [`t:real^3`; `a:real^3`; `b:real^3`] MOI_FSTR_SEC_FLAT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_NEG_0; CROSS_RMUL; DOT_LMUL] THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Off both pages, a point is in one of the two sectors. *)
let MOI_FSTR_SEC_COVER = prove
 (`!t a b w:real^3.
     ~(t = vec 0) /\ ~(a = vec 0) /\ ~(b = vec 0) /\ t dot a = &0 /\ t dot b = &0 /\
     ~(?s u. &0 <= u /\ b = s % t + u % a) /\ ~(?s u. &0 <= u /\ a = s % t + u % b) /\
     ~(?s u. &0 <= u /\ w = s % t + u % a) /\ ~(?s u. &0 <= u /\ w = s % t + u % b)
     ==> moi_fstr_sec t a b w \/ moi_fstr_sec t b a w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* on the plane of t and a, off the page of a, the sign of D(b,w) is forced *)
  SUBGOAL_THEN
   `(t cross a) dot (w:real^3) = &0
    ==> (&0 < (t cross a) dot b ==> &0 < (t cross b) dot w) /\
        ((t cross a) dot b < &0 ==> (t cross b) dot w < &0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:real^3`; `a:real^3`; `w:real^3`] MOI_FSTR_PLANE_SPAN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `u < &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(?s u. &0 <= u /\ w = s % t + u % (a:real^3))` THEN REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`s:real`; `u:real`] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `w:real^3`)) THEN
    REWRITE_TAC[MOI_FSTR_D_LIN] THEN
    MOI_FSTR_DANTI_TAC [[`t:real^3`; `b:real^3`; `a:real^3`]] THEN
    REWRITE_TAC[REAL_MUL_POS_LT; MOI_FSTR_MUL_NEG_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(t cross b) dot (w:real^3) = &0
    ==> (&0 < (t cross a) dot b ==> (t cross a) dot w < &0) /\
        ((t cross a) dot b < &0 ==> &0 < (t cross a) dot w)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:real^3`; `b:real^3`; `w:real^3`] MOI_FSTR_PLANE_SPAN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `u < &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(?s u. &0 <= u /\ w = s % t + u % (b:real^3))` THEN REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`s:real`; `u:real`] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `w:real^3`)) THEN
    REWRITE_TAC[MOI_FSTR_D_LIN] THEN
    REWRITE_TAC[REAL_MUL_POS_LT; MOI_FSTR_MUL_NEG_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_fstr_sec] THEN
  MOI_FSTR_DANTI_TAC [[`t:real^3`; `w:real^3`; `b:real^3`];
                      [`t:real^3`; `w:real^3`; `a:real^3`];
                      [`t:real^3`; `b:real^3`; `a:real^3`]] THEN
  ASM_CASES_TAC `(t cross a) dot (b:real^3) = &0` THENL
   [(* flat: b is a negative multiple of a, and w is off the plane *)
    MP_TAC(ISPECL [`t:real^3`; `a:real^3`; `b:real^3`] MOI_FSTR_SEC_FLAT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((t cross a) dot (w:real^3) = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`t:real^3`; `a:real^3`; `w:real^3`] MOI_FSTR_PLANE_SPAN) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
      ASM_CASES_TAC `&0 <= u` THENL
       [UNDISCH_TAC `~(?s u. &0 <= u /\ w = s % t + u % (a:real^3))` THEN REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`s:real`; `u:real`] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `~(?s u. &0 <= u /\ w = s % t + u % (b:real^3))` THEN REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`s:real`; `u / k:real`] THEN CONJ_TAC THENL
         [REWRITE_TAC[real_div] THEN
          ONCE_REWRITE_TAC[REAL_ARITH `u * inv k = --u * --inv k`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[GSYM REAL_INV_NEG] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
          ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
          AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          UNDISCH_TAC `k < &0` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_NEG_0; CROSS_RMUL; DOT_LMUL] THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]);;

(* A point on either page is in neither sector (page of a; likewise b). *)
let MOI_FSTR_SEC_OFFPAGE = prove
 (`!(t:real^3) a b s u.
     &0 <= u
     ==> ~moi_fstr_sec t a b (s % t + u % a) /\ ~moi_fstr_sec t b a (s % t + u % a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[moi_fstr_sec; MOI_FSTR_D_LIN; DOT_CROSS_SELF; REAL_MUL_RZERO; REAL_LT_REFL] THEN
  MOI_FSTR_DANTI_TAC [[`t:real^3`; `b:real^3`; `a:real^3`]] THEN
  REWRITE_TAC[REAL_MUL_POS_LT] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* The part of a sector in a ball is connected. *)
let MOI_FSTR_SEC_CONN = prove
 (`!t a b (y:real^3) r.
     &0 < r ==> connected {z | z IN ball(y,r) /\ moi_fstr_sec t a b (z - y)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fstr_sec] THEN
  ASM_CASES_TAC `&0 < (t cross a) dot (b:real^3)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN
    SUBGOAL_THEN
     `{z | z IN ball(y,r) /\ &0 < (t cross a) dot (z - y) /\
           &0 < (t cross (z - y)) dot b} =
      ball(y,r) INTER {z:real^3 | (t cross a) dot z > (t cross a) dot y} INTER
      {z | (t cross b) dot z < (t cross b) dot y}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      REWRITE_TAC[ISPECL [`t:real^3`; `z - y:real^3`; `b:real^3`] MOI_FSTR_D_ANTI] THEN
      REWRITE_TAC[DOT_RSUB; real_gt; REAL_SUB_LT; REAL_ARITH `&0 < --(x - y) <=> x < y`];
      MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_HALFSPACE_GT; CONVEX_HALFSPACE_LT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(t cross a) dot (b:real^3) < &0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SET_RULE
      `{z:real^3 | P z /\ (Q z \/ R z)} = {z | P z /\ Q z} UNION {z | P z /\ R z}`] THEN
    MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `{z | z IN ball(y,r) /\ &0 < (t cross a) dot (z - y)} =
                    ball(y,r) INTER {z:real^3 | (t cross a) dot z > (t cross a) dot y}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_RSUB; real_gt; REAL_SUB_LT];
        MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_GT]];
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `{z | z IN ball(y,r) /\ &0 < (t cross (z - y)) dot b} =
                    ball(y,r) INTER {z:real^3 | (t cross b) dot z < (t cross b) dot y}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
        REWRITE_TAC[ISPECL [`t:real^3`; `z - y:real^3`; `b:real^3`] MOI_FSTR_D_ANTI] THEN
        REWRITE_TAC[DOT_RSUB; REAL_ARITH `&0 < --(x - y) <=> x < y`];
        MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_LT]];
      (* a common point: y minus a small multiple of a + b *)
      SUBGOAL_THEN `&0 < norm(a + b:real^3) + &1` ASSUME_TAC THENL
       [MP_TAC(ISPEC `a + b:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `e = r / (norm(a + b:real^3) + &1)` THEN
      SUBGOAL_THEN `&0 < e /\ e * norm(a + b:real^3) < r` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "e" THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
        MP_TAC(ISPECL [`r:real`; `norm(a + b:real^3) + &1`] REAL_DIV_RMUL) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`r:real`; `norm(a + b:real^3) + &1`] REAL_LT_DIV) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `y - e % (a + b:real^3)` THEN
      REWRITE_TAC[VECTOR_ARITH `(y - e % (a + b)) - y:real^3 = (--e) % a + (--e) % b`] THEN
      REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `y - (y - x):real^3 = x`; NORM_MUL] THEN
      REWRITE_TAC[CROSS_RADD; CROSS_RMUL; DOT_LADD; DOT_LMUL; DOT_RADD; DOT_RMUL;
                  DOT_CROSS_SELF; REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID] THEN
      REWRITE_TAC[REAL_MUL_POS_LT] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONVEX_CONNECTED THEN
  SUBGOAL_THEN `{z | z IN ball(y,r) /\ &0 < (t cross a) dot (z - y)} =
                ball(y,r) INTER {z:real^3 | (t cross a) dot z > (t cross a) dot y}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_RSUB; real_gt; REAL_SUB_LT];
    MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_GT]]);;

(* The normal t cross a at a point of the page of a points into sec t a b. *)
let MOI_FSTR_SEC_NORMAL = prove
 (`!(t:real^3) a b s u.
     ~(t = vec 0) /\ ~(a = vec 0) /\ t dot a = &0 /\ &0 < u
     ==> ?h. &0 < h /\
             !k. &0 < k /\ k < h ==> moi_fstr_sec t a b (s % t + u % a + k % (t cross a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (t cross a) dot (t cross a:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; NORM_CROSS] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fstr_sec; MOI_FSTR_D_LIN] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_LZERO] THEN
  ASM_CASES_TAC `&0 < (t cross a) dot (b:real^3)` THEN ASM_REWRITE_TAC[] THENL
   [ABBREV_TAC `xx = ((t:real^3) dot t) * ((a:real^3) dot b)` THEN
    EXISTS_TAC `(u * ((t cross a) dot (b:real^3))) / (&1 + abs xx)` THEN
    SUBGOAL_THEN `&0 < &1 + abs xx` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    X_GEN_TAC `k:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `k * (&1 + abs xx) < u * ((t cross a) dot (b:real^3))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `k * xx <= k * abs xx` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* Local structure of a surface in real^3 near relative interior points of  *)
(* its triangles (one plane) and of its edges (two pages).                  *)
(* ------------------------------------------------------------------------- *)

(* The component of w orthogonal to t. *)
let moi_fstr_perp = new_definition
 `moi_fstr_perp (t:real^3) (w:real^3) = w - ((w dot t) / (t dot t)) % t`;;

let MOI_FSTR_PERP = prove
 (`!t w:real^3.
     ~(t = vec 0)
     ==> t dot moi_fstr_perp t w = &0 /\
         t cross moi_fstr_perp t w = t cross w /\
         w = moi_fstr_perp t w + ((w dot t) / (t dot t)) % t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_fstr_perp] THEN
  REWRITE_TAC[DOT_RSUB; DOT_RMUL; CROSS_RSUB; CROSS_RMUL; CROSS_REFL; VECTOR_MUL_RZERO;
              VECTOR_SUB_RZERO] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
  SUBGOAL_THEN `~((t:real^3) dot t = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let MOI_FSTR_TRI_INDEP = prove
 (`!a b c:real^N.
     aff_dim(convex hull {a,b,c}) = &2
     ==> ~(a = b) /\ ~(a = c) /\ ~(b = c) /\ ~affine_dependent {a,b,c} /\
         ~collinear {a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~collinear {a:real^N,b,c}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COLLINEAR_AFF_DIM] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~collinear {a:real^N,b,c}` THEN
  REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN SIMP_TAC[]);;

let MOI_FSTR_TRI_NORMAL = prove
 (`!a b c:real^3.
     aff_dim(convex hull {a,b,c}) = &2 ==> ~((b - a) cross (c - a) = vec 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_FSTR_TRI_INDEP) THEN
  REWRITE_TAC[CROSS_EQ_0; GSYM COLLINEAR_3] THEN
  REWRITE_TAC[SET_RULE `{b:real^3,a,c} = {a,b,c}`] THEN SIMP_TAC[]);;

let MOI_FSTR_TRI_EQ = prove
 (`!a b c c':real^N.
     aff_dim(convex hull {a,b,c}) = &2 /\ aff_dim(convex hull {a,b,c'}) = &2 /\
     convex hull {a,b,c} = convex hull {a,b,c'}
     ==> c = c'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FSTR_TRI_INDEP) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c':real^N`] MOI_FSTR_TRI_INDEP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N,b,c} = {a,b,c'}` MP_TAC THENL
   [MP_TAC(ISPEC `{a:real^N,b,c}` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPEC `{a:real^N,b,c'}` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N`) THEN ASM_MESON_TAC[]);;

(* Points of a triangle lie in its plane. *)
let MOI_FSTR_TRI_PLANE = prove
 (`!a b c z:real^3.
     z IN convex hull {a,b,c} ==> ((b - a) cross (c - a)) dot (z - a) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `w:real`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x % a + y % b + w % c) - a:real^3 = y % (b - a) + w % (c - a)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `x = &1 - y - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_CROSS_SELF; REAL_MUL_RZERO; REAL_ADD_RID]]);;

(* Relative to a point y of the edge [a,b], a point of the triangle is on  *)
(* the page spanned by b - a and the orthogonal part of c - a.             *)
let MOI_FSTR_PAGE_OF = prove
 (`!a b c y z:real^3.
     y IN segment[a,b] /\ z IN convex hull {a,b,c}
     ==> ?s u. &0 <= u /\ z - y = s % (b - a) + u % moi_fstr_perp (b - a) (c - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT; CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `yy:real` (X_CHOOSE_THEN `w:real`
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `lam = ((c - a) dot (b - a:real^3)) / ((b - a) dot (b - a))` THEN
  MAP_EVERY EXISTS_TAC [`yy - th + w * lam`; `w:real`] THEN
  ASM_REWRITE_TAC[moi_fstr_perp] THEN
  SUBGOAL_THEN `x = &1 - yy - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  VECTOR_ARITH_TAC);;

(* Near a relative interior point of the edge, the page of the triangle is *)
(* in the triangle.                                                          *)
let MOI_FSTR_PAGE_IN = prove
 (`!a b c y:real^3.
     aff_dim(convex hull {a,b,c}) = &2 /\ y IN segment(a,b)
     ==> ?e. &0 < e /\
             !s u. &0 <= u /\
                   norm(s % (b - a) + u % moi_fstr_perp (b - a) (c - a)) < e
                   ==> y + s % (b - a) + u % moi_fstr_perp (b - a) (c - a) IN
                       convex hull {a,b,c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(y:real^3) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `t:real^3 = b - a` THEN
  SUBGOAL_THEN `~(t:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3`; `c - a:real^3`] MOI_FSTR_PERP) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `lam = ((c - a) dot (t:real^3)) / (t dot t)` THEN
  ABBREV_TAC `A:real^3 = moi_fstr_perp t (c - a)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(A:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(t cross (c - a:real^3) = vec 0)` THEN
    UNDISCH_TAC `t cross A = t cross (c - a:real^3)` THEN
    ASM_REWRITE_TAC[CROSS_RZERO] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3) dot t = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(t:real^3) /\ &0 < norm(A:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `K = inv(norm(t:real^3)) + (abs lam + &1) * inv(norm(A:real^3))` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LTE_ADD THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min th (&1 - th) / K` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `u:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `w:real^3 = s % t + u % A` THEN
  SUBGOAL_THEN `norm(w:real^3) pow 2 =
                s pow 2 * norm(t:real^3) pow 2 + u pow 2 * norm(A:real^3) pow 2`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u pow 2 * norm(A:real^3) pow 2 /\ &0 <= s pow 2 * norm(t:real^3) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `abs s * norm(t:real^3) <= norm(w:real^3) /\ u * norm(A:real^3) <= norm w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y /\ abs x <= abs y ==> x <= y`) THEN
    REWRITE_TAC[REAL_LE_SQUARE_ABS; REAL_POW_MUL; REAL_POW2_ABS] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs s <= norm(w:real^3) * inv(norm(t:real^3)) /\
                u <= norm w * inv(norm(A:real^3))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `u * (abs lam + &1) <= (norm(w:real^3) * inv(norm(A:real^3))) * (abs lam + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^3) * K < min th (&1 - th)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `abs s + u * (abs lam + &1) < min th (&1 - th)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(w:real^3) * K` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u * lam <= u * abs lam /\ --(u * abs lam) <= u * lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `--(u * x) = u * --x`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXPAND_TAC "w" THEN
  SUBGOAL_THEN `A:real^3 = (c - a) - lam % t` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `c - a:real^3`)) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "t" THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `y:real^3`)) THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - th - s + u * lam - u`; `th + s - u * lam`; `u:real`] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  VECTOR_ARITH_TAC);;

(* An explicit relative interior point of a triangle near its edge. *)
let MOI_FSTR_RELINT_PT = prove
 (`!a b c y:real^3 l.
     aff_dim(convex hull {a,b,c}) = &2 /\ y IN segment(a,b) /\ &0 < l /\ l < &1
     ==> y + l % (c - y) IN relative_interior(convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_SBA_RELINT_3] THEN
  UNDISCH_TAC `(y:real^3) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(&1 - l) * (&1 - th)`; `(&1 - l) * th`; `l:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC) THEN
  TRY REAL_ARITH_TAC THEN VECTOR_ARITH_TAC);;

(* Near a relative interior point of a triangle, the surface is the triangle. *)
let MOI_FSTR_RELINT_FLAT = prove
 (`!(m:(real^3->bool)->bool) a b c p.
     FINITE m /\ combinatorial_manifold 2 m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     p IN relative_interior(convex hull {a,b,c})
     ==> ?e. &0 < e /\ UNIONS m INTER ball(p,e) SUBSET convex hull {a,b,c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  ABBREV_TAC `tau = convex hull {a:real^3,b,c}` THEN
  SUBGOAL_THEN `(p:real^3) IN tau` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN UNIONS m` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `p:real^3`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(tau INTER s:real^3->bool) face_of tau /\ (tau INTER s) face_of s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (m:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau INTER s:real^3->bool = tau` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tau INTER s:real^3->bool`; `tau:real^3->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real^3->bool = tau` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tau:real^3->bool`; `s:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (m:(real^3->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_CM_DIM) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_FSTR_CARD2 = prove
 (`!(s:A->bool) x y z.
     FINITE s /\ CARD s = 2 /\ x IN s /\ y IN s /\ ~(x = y) /\ z IN s
     ==> z = x \/ z = y`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `z:A = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z:A = y` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `CARD {z:A,x,y} = 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `{z:A,x,y} HAS_SIZE 3` MP_TAC THENL
     [CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`z:A`; `x:A`; `y:A`] THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[HAS_SIZE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {z:A,x,y} <= CARD (s:A->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Near a relative interior point of an edge, the surface is the union of  *)
(* the two triangles at the edge.                                           *)
let MOI_FSTR_EDGE_PAGES = prove
 (`!(m:(real^3->bool)->bool) a b c c' y.
     FINITE m /\ combinatorial_manifold 2 m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     convex hull {a,b,c'} IN m /\ aff_dim(convex hull {a,b,c'}) = &2 /\
     ~(c = c') /\ y IN segment(a,b)
     ==> ?e. &0 < e /\
             UNIONS m INTER ball(y,e) SUBSET
             convex hull {a,b,c} UNION convex hull {a,b,c'}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(convex hull {a,b,c} = convex hull {a:real^3,b,c'})` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSTR_TRI_EQ]; ALL_TAC] THEN
  ABBREV_TAC `tau = convex hull {a:real^3,b,c}` THEN
  ABBREV_TAC `tau' = convex hull {a:real^3,b,c'}` THEN
  ABBREV_TAC `e0 = convex hull {a:real^3,b}` THEN
  SUBGOAL_THEN `(e0:real^3->bool) SUBSET tau /\ e0 SUBSET tau'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e0"; "tau"; "tau'"] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e0:real^3->bool) IN m` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (m:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`e0:real^3->bool`; `tau:real^3->bool`] o CONJUNCT1 o
      CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["e0"; "tau"] THEN
    SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
             ASSUME `~affine_dependent {a:real^3,b,c}`] THEN
    EXISTS_TAC `{a:real^3,b}` THEN REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(e0:real^3->bool) = &1 /\ relative_interior e0 = segment(a:real^3,b)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; AFF_DIM_SEGMENT; RELATIVE_INTERIOR_SEGMENT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN e0` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS m` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e0:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `y:real^3`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_UNION] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e0 INTER s:real^3->bool) face_of e0 /\ (e0 INTER s) face_of s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (m:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e0 INTER s:real^3->bool = e0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e0 INTER s:real^3->bool`; `e0:real^3->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real^3->bool = e0` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^3->bool) = &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e0:real^3->bool`; `s:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `lf_simplicial_complex (m:(real^3->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_CM_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{t | t IN m /\ aff_dim t = &2 /\ (e0:real^3->bool) SUBSET t}`;
                 `tau:real^3->bool`; `tau':real^3->bool`; `s:real^3->bool`]
    MOI_FSTR_CARD2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `m:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC MOI_FSA_CM_EDGE2 THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(* The page of one triangle at an edge is not on the page of the other. *)
let MOI_FSTR_SEPARATE_PAGES = prove
 (`!(m:(real^3->bool)->bool) a b c c'.
     lf_simplicial_complex m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     convex hull {a,b,c'} IN m /\ aff_dim(convex hull {a,b,c'}) = &2 /\ ~(c = c')
     ==> ~(?s u. &0 <= u /\
                 moi_fstr_perp (b - a) (c' - a) =
                 s % (b - a) + u % moi_fstr_perp (b - a) (c - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y:real^3 = inv(&2) % a + inv(&2) % b` THEN
  SUBGOAL_THEN `(y:real^3) IN segment(a,b)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `inv(&2)` THEN
    EXPAND_TAC "y" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`; `y:real^3`] MOI_FSTR_PAGE_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < e + norm(c' - y:real^3) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c' - y:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `l = e / (e + norm(c' - y:real^3) + &1)` THEN
  SUBGOAL_THEN `&0 < l /\ l < &1 /\ l * norm(c' - y:real^3) < e` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `l * (e + norm(c' - y:real^3) + &1) = e` ASSUME_TAC THENL
     [EXPAND_TAC "l" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
     [EXPAND_TAC "l" THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    SUBGOAL_THEN `l < &1` ASSUME_TAC THENL
     [EXPAND_TAC "l" THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      MP_TAC(ISPEC `c' - y:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < l * (e + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y + l % (c' - y) IN relative_interior(convex hull {a:real^3,b,c'})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSTR_RELINT_PT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the same point is on the page of the first triangle, hence in it *)
  SUBGOAL_THEN `~(b - a:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`b - a:real^3`; `c' - a:real^3`] MOI_FSTR_PERP) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `lam' = ((c' - a) dot (b - a:real^3)) / ((b - a) dot (b - a))` THEN
  ABBREV_TAC `P' = moi_fstr_perp (b - a) (c' - a:real^3)` THEN
  ABBREV_TAC `P = moi_fstr_perp (b - a) (c - a:real^3)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `l % (c' - y) = (l * (s + lam' - inv(&2))) % (b - a) + (l * u) % (P:real^3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `c' - y:real^3 = (c' - a) - inv(&2) % (b - a)` SUBST1_TAC THENL
     [EXPAND_TAC "y" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `c' - a:real^3`
                            then SUBST1_TAC th else failwith "no") THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `P':real^3`
                            then SUBST1_TAC th else failwith "no") THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y + l % (c' - y) IN convex hull {a:real^3,b,c}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `l % (c' - y:real^3)`)) THEN
      REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`]];
    ALL_TAC] THEN
  (* so the two triangles share a relative interior point of the second *)
  ABBREV_TAC `tau = convex hull {a:real^3,b,c}` THEN
  ABBREV_TAC `tau' = convex hull {a:real^3,b,c'}` THEN
  SUBGOAL_THEN `(tau INTER tau':real^3->bool) face_of tau /\ (tau INTER tau') face_of tau'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (m:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau INTER tau':real^3->bool = tau'` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tau INTER tau':real^3->bool`; `tau':real^3->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `y + l % (c' - y) IN (tau':real^3->bool)` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `y + l % (c' - y) IN relative_interior (tau':real^3->bool)` THEN
    UNDISCH_TAC `y + l % (c' - y) IN (tau:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau':real^3->bool = tau` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tau':real^3->bool`; `tau:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "tau" THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `~(c:real^3 = c')` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FSTR_TRI_EQ THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The side of a flat piece of the surface.  For the two open sides D, E of *)
(* M in ball(v,r) (moi_fstr_sides), a convex flat piece tau of M and a      *)
(* normal n, moi_fstr_posn says that near some relative interior point of   *)
(* tau in ball(v,r) the open half-ball in the direction n lies in D.  This  *)
(* holds at one point iff at all of them, and it flips with n.              *)
(* ------------------------------------------------------------------------- *)

let moi_fstr_sides = new_definition
 `moi_fstr_sides (M:real^3->bool) (v:real^3) r D E <=>
    &0 < r /\ open D /\ open E /\ DISJOINT D E /\
    ball(v,r) DIFF M = D UNION E /\
    M INTER ball(v,r) SUBSET closure D /\ M INTER ball(v,r) SUBSET closure E`;;

let moi_fstr_posn = new_definition
 `moi_fstr_posn (D:real^3->bool) (v:real^3) r (tau:real^3->bool) (n:real^3) <=>
    ?p e. p IN relative_interior tau /\ p IN ball(v,r) /\ &0 < e /\
          !z. z IN ball(p,e) /\ &0 < n dot (z - p) ==> z IN D`;;

(* Points of the two open half-balls in the directions n and --n. *)
let MOI_FSTR_NORMAL_PT = prove
 (`!(p:real^3) n e.
     ~(n = vec 0) /\ &0 < e
     ==> dist(p,p + (e / (&2 * norm n)) % n) < e /\
         &0 < n dot ((p + (e / (&2 * norm n)) % n) - p) /\
         dist(p,p - (e / (&2 * norm n)) % n) < e /\
         n dot ((p - (e / (&2 * norm n)) % n) - p) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(n:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / (&2 * norm(n:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (n:real^3) dot n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `p - (p + x):real^3 = --x`;
              VECTOR_ARITH `p - (p - x):real^3 = x`;
              VECTOR_ARITH `(p + x) - p:real^3 = x`;
              VECTOR_ARITH `(p - x) - p:real^3 = --x`;
              NORM_NEG; NORM_MUL; DOT_RMUL; DOT_RNEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  SUBGOAL_THEN `e / (&2 * norm(n:real^3)) * norm n = e / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(n:real^3)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `--x < &0 <=> &0 < x`] THEN
  ASM_REAL_ARITH_TAC);;

(* At a flat point, the two half-balls lie in different sides. *)
let MOI_FSTR_POSN_LOCAL = prove
 (`!(M:real^3->bool) v r D E n p e1.
     moi_fstr_sides M v r D E /\ ~(n = vec 0) /\
     p IN M /\ p IN ball(v,r) /\ &0 < e1 /\
     M INTER ball(p,e1) SUBSET {z | n dot (z - p) = &0}
     ==> ?e. &0 < e /\ ball(p,e) SUBSET ball(v,r) /\
             (({z | z IN ball(p,e) /\ &0 < n dot (z - p)} SUBSET D /\
               {z | z IN ball(p,e) /\ n dot (z - p) < &0} SUBSET E) \/
              ({z | z IN ball(p,e) /\ &0 < n dot (z - p)} SUBSET E /\
               {z | z IN ball(p,e) /\ n dot (z - p) < &0} SUBSET D))`,
  REWRITE_TAC[moi_fstr_sides] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `min e1 (r - dist(v:real^3,p))` THEN
  SUBGOAL_THEN `&0 < min e1 (r - dist(v:real^3,p))` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN ball(v,r)` THEN REWRITE_TAC[IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(p:real^3,min e1 (r - dist(v,p))) SUBSET ball(v,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `z:real^3` THEN
    MP_TAC(ISPECL [`v:real^3`; `p:real^3`; `z:real^3`] DIST_TRIANGLE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FSTR_HALF_BALLS THEN EXISTS_TAC `M:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `M INTER ball(p:real^3,e1)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (M:real^3->bool) INTER s SUBSET M INTER t`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC]);;

(* The side of the half-ball in direction n is the same at all relative     *)
(* interior points of tau in ball(v,r) (connectedness of that set).          *)
let MOI_FSTR_POSN_UNIFORM = prove
 (`!(M:real^3->bool) v r D E tau n.
     moi_fstr_sides M v r D E /\ ~(n = vec 0) /\ convex tau /\ tau SUBSET M /\
     (!p q. p IN tau /\ q IN tau ==> n dot (q - p) = &0) /\
     (!p. p IN relative_interior tau /\ p IN ball(v,r)
          ==> ?e. &0 < e /\ M INTER ball(p,e) SUBSET {z | n dot (z - p) = &0})
     ==> !p. p IN relative_interior tau /\ p IN ball(v,r)
             ==> ?e. &0 < e /\ ball(p,e) SUBSET ball(v,r) /\
                     (if moi_fstr_posn D v r tau n
                      then {z | z IN ball(p,e) /\ &0 < n dot (z - p)} SUBSET D /\
                           {z | z IN ball(p,e) /\ n dot (z - p) < &0} SUBSET E
                      else {z | z IN ball(p,e) /\ &0 < n dot (z - p)} SUBSET E /\
                           {z | z IN ball(p,e) /\ n dot (z - p) < &0} SUBSET D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (D:real^3->bool) E` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fstr_sides]; ALL_TAC] THEN
  (* the local alternatives *)
  SUBGOAL_THEN
   `!p. p IN relative_interior tau /\ p IN ball(v,r)
        ==> ?e. &0 < e /\ ball(p,e) SUBSET ball(v:real^3,r) /\
                (({z | z IN ball(p,e) /\ &0 < n dot (z - p)} SUBSET D /\
                  {z | z IN ball(p,e) /\ n dot (z - p) < &0} SUBSET E) \/
                 ({z | z IN ball(p,e) /\ &0 < n dot (z - p)} SUBSET E /\
                  {z | z IN ball(p,e) /\ n dot (z - p) < &0} SUBSET D))`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `relative_interior (tau:real^3->bool)`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FSTR_POSN_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`M:real^3->bool`; `e1:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  (* positivity at one point propagates to all points *)
  SUBGOAL_THEN
   `!p q:real^3.
          (p IN relative_interior (tau:real^3->bool) /\ p IN ball(v:real^3,r)) /\
          (q IN relative_interior tau /\ q IN ball(v,r)) /\
          (?e. &0 < e /\ !z. z IN ball(p,e) /\ &0 < (n:real^3) dot (z - p)
                             ==> z IN (D:real^3->bool))
          ==> (?e. &0 < e /\ !z. z IN ball(q,e) /\ &0 < n dot (z - q) ==> z IN D)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\p:real^3. ?e. &0 < e /\ !z. z IN ball(p,e) /\ &0 < n dot (z - p) ==> z IN D`;
      `relative_interior tau INTER ball(v:real^3,r)`] CONNECTED_INDUCTION_SIMPLE) THEN
    REWRITE_TAC[IN_INTER] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR; CONVEX_BALL];
      ALL_TAC] THEN
    X_GEN_TAC `a:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `E:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    EXISTS_TAC `(relative_interior tau INTER ball(v:real^3,r)) INTER ball(a,e0 / &2)` THEN
    SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_HALF] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
    (* x and y are in tau, so n is orthogonal to x - a and y - a *)
    SUBGOAL_THEN `n dot (x - a:real^3) = &0 /\ n dot (y - a:real^3) = &0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [(* alternative 1 at a: every point near a has its half-ball in D *)
      EXISTS_TAC `e0 / &2` THEN REWRITE_TAC[REAL_HALF] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `{z | z IN ball(a,e0) /\ &0 < n dot (z - a)} SUBSET (D:real^3->bool)` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN ball(a,e0 / &2)` THEN
        UNDISCH_TAC `(z:real^3) IN ball(y,e0 / &2)` THEN REWRITE_TAC[IN_BALL] THEN
        MP_TAC(ISPECL [`a:real^3`; `y:real^3`; `z:real^3`] DIST_TRIANGLE) THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `(n:real^3) dot (z - a) = n dot (z - y) + n dot (y - a)`
        SUBST1_TAC THENL [REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      (* alternative 2 at a: no point near a has its half-ball in D *)
      FIRST_X_ASSUM(X_CHOOSE_THEN `e':real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`x:real^3`; `n:real^3`; `min e' (e0 / &2)`] MOI_FSTR_NORMAL_PT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF]; ALL_TAC] THEN
      ABBREV_TAC `z = x + (min e' (e0 / &2) / (&2 * norm(n:real^3))) % n` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN D` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN E` ASSUME_TAC THENL
       [UNDISCH_TAC `{z | z IN ball(a,e0) /\ &0 < n dot (z - a)} SUBSET (E:real^3->bool)` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [UNDISCH_TAC `(x:real^3) IN ball(a,e0 / &2)` THEN REWRITE_TAC[IN_BALL] THEN
          MP_TAC(ISPECL [`a:real^3`; `x:real^3`; `z:real^3`] DIST_TRIANGLE) THEN
          ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN `(n:real^3) dot (z - a) = n dot (z - x) + n dot (x - a)`
          SUBST1_TAC THENL [REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `E:real^3->bool`)) (concl th) &&
    not (can (find_term ((=) `q:real^3`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    (* positivity at p, against alternative 2 *)
    UNDISCH_TAC `moi_fstr_posn D (v:real^3) r tau n` THEN REWRITE_TAC[moi_fstr_posn] THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:real^3` (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p1:real^3`; `p:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `q:real^3`)) (concl th))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`p:real^3`; `n:real^3`; `min e' e0`] MOI_FSTR_NORMAL_PT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
    ABBREV_TAC `z = p + (min e' e0 / (&2 * norm(n:real^3))) % n` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN D /\ z IN E` MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `{z | z IN ball(p,e0) /\ &0 < n dot (z - p)} SUBSET (E:real^3->bool)` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC];
      ASM SET_TAC[]];
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~moi_fstr_posn D (v:real^3) r tau n` THEN REWRITE_TAC[moi_fstr_posn] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`p:real^3`; `e0:real`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{z | z IN ball(p,e0) /\ &0 < n dot (z - p)} SUBSET (D:real^3->bool)` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* The side flips with the normal. *)
let MOI_FSTR_POSN_NEG = prove
 (`!(M:real^3->bool) v r D E tau n.
     moi_fstr_sides M v r D E /\ ~(n = vec 0) /\ convex tau /\ tau SUBSET M /\
     (!p q. p IN tau /\ q IN tau ==> n dot (q - p) = &0) /\
     (!p. p IN relative_interior tau /\ p IN ball(v,r)
          ==> ?e. &0 < e /\ M INTER ball(p,e) SUBSET {z | n dot (z - p) = &0}) /\
     ~(relative_interior tau INTER ball(v,r) = {})
     ==> (moi_fstr_posn D v r tau (--n) <=> ~moi_fstr_posn D v r tau n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (D:real^3->bool) E` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fstr_sides]; ALL_TAC] THEN
  UNDISCH_TAC `~(relative_interior tau INTER ball(v:real^3,r) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `moi_fstr_posn D (v:real^3) r tau n` THEN
  ASM_CASES_TAC `moi_fstr_posn D (v:real^3) r tau (--n)` THEN
  ASM_REWRITE_TAC[] THEN
  (MP_TAC(ISPECL [`M:real^3->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `tau:real^3->bool`; `n:real^3`]
    MOI_FSTR_POSN_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`M:real^3->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `tau:real^3->bool`; `--n:real^3`]
    MOI_FSTR_POSN_UNIFORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG; REAL_NEG_EQ_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^3`; `n:real^3`; `min e1 e2`] MOI_FSTR_NORMAL_PT) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ABBREV_TAC `z = p - (min e1 e2 / (&2 * norm(n:real^3))) % n` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN {w | w IN ball(p,e1) /\ n dot (w - p) < &0} /\
                z IN {w | w IN ball(p,e2) /\ &0 < --n dot (w - p)}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_BALL; DOT_LNEG] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM SET_TAC[]));;

(* The sign of an ordered triangle of the surface at v. *)
let moi_fstr_sg = new_definition
 `moi_fstr_sg (D:real^3->bool) (v:real^3) r (a:real^3) b c =
    if moi_fstr_posn D v r (convex hull {a,b,c}) ((b - a) cross (c - a))
    then &1 else -- &1`;;

let MOI_FSTR_TRI_POSN_HYPS = prove
 (`!(m:(real^3->bool)->bool) v r D E a b c.
     FINITE m /\ combinatorial_manifold 2 m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     v IN convex hull {a,b,c} /\ moi_fstr_sides (UNIONS m) v r D E
     ==> ~((b - a) cross (c - a) = vec 0) /\ convex(convex hull {a,b,c}) /\
         convex hull {a,b,c} SUBSET UNIONS m /\
         (!p q. p IN convex hull {a,b,c} /\ q IN convex hull {a,b,c}
                ==> ((b - a) cross (c - a)) dot (q - p) = &0) /\
         (!p. p IN relative_interior(convex hull {a,b,c}) /\ p IN ball(v,r)
              ==> ?e. &0 < e /\
                      UNIONS m INTER ball(p,e) SUBSET
                      {z | ((b - a) cross (c - a)) dot (z - p) = &0}) /\
         ~(relative_interior(convex hull {a,b,c}) INTER ball(v,r) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p q:real^3. p IN convex hull {a,b,c} /\ q IN convex hull {a,b,c}
                             ==> ((b - a) cross (c - a)) dot (q - p) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `q - p:real^3 = (q - a) - (p - a)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[DOT_RSUB] THEN ASM_SIMP_TAC[MOI_FSTR_TRI_PLANE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FSTR_TRI_NORMAL; CONVEX_CONVEX_HULL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
    X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                   `p:real^3`] MOI_FSTR_RELINT_FLAT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ASM SET_TAC[]];
    SUBGOAL_THEN `(v:real^3) IN closure(relative_interior(convex hull {a,b,c}))`
    MP_TAC THENL
     [SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CONVEX_CONVEX_HULL] THEN
      SUBGOAL_THEN `closure(convex hull {a,b,c}) = convex hull {a:real^3,b,c}`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[moi_fstr_sides]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
    MESON_TAC[DIST_SYM]]);;

(* (O1) for the sign: values +-1, antisymmetric in the transpositions. *)
let MOI_FSTR_SG_SWAP = prove
 (`!(m:(real^3->bool)->bool) v r D E a b c.
     FINITE m /\ combinatorial_manifold 2 m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     v IN convex hull {a,b,c} /\ moi_fstr_sides (UNIONS m) v r D E
     ==> (moi_fstr_sg D v r a b c = &1 \/ moi_fstr_sg D v r a b c = -- &1) /\
         moi_fstr_sg D v r b a c = --(moi_fstr_sg D v r a b c) /\
         moi_fstr_sg D v r a c b = --(moi_fstr_sg D v r a b c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`]
    MOI_FSTR_TRI_POSN_HYPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `convex hull {a:real^3,b,c}`;
                 `(b - a) cross (c - a:real^3)`] MOI_FSTR_POSN_NEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_fstr_sg] THEN
  MP_TAC(end_itlist CONJ
   [SET_RULE `{b:real^3,a,c} = {a,b,c}`; SET_RULE `{a:real^3,c,b} = {a,b,c}`;
    VEC3_RULE `(a - b) cross (c - b:real^3) = --((b - a) cross (c - a))`;
    VEC3_RULE `(c - a) cross (b - a:real^3) = --((b - a) cross (c - a))`]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* (O2) coherence of the sign across an edge at v: near a relative interior *)
(* point y of the edge, the complement of the two pages in a small ball is  *)
(* two sectors lying in different sides, and the normal of each triangle    *)
(* points into the sector next to its page.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_SMALL = prove
 (`!h x e. &0 < h /\ &0 <= x /\ &0 < e ==> ?k. &0 < k /\ k < h /\ k * x < e`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min h e / (&2 * (x + &1))` THEN
  SUBGOAL_THEN `&0 < &2 * (x + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `min h e / (&2 * (x + &1)) * (&2 * (x + &1)) = min h e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = min h e / (&2 * (x + &1))` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k * x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_FSTR_SEG_NEAR = prove
 (`!a b v:real^3 r.
     ~(a = b) /\ (v = a \/ v = b) /\ &0 < r
     ==> ?y. y IN segment(a,b) /\ y IN ball(v,r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`&1`; `norm(b - a:real^3)`; `r:real`] MOI_FSTR_SMALL) THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `(&1 - l) % a + l % b:real^3` THEN
    ASM_REWRITE_TAC[IN_SEGMENT; IN_BALL] THEN CONJ_TAC THENL
     [EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `a - ((&1 - l) % a + l % b):real^3 = --(l % (b - a))`] THEN
    REWRITE_TAC[NORM_NEG; NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`];
    EXISTS_TAC `l % a + (&1 - l) % b:real^3` THEN
    ASM_REWRITE_TAC[IN_SEGMENT; IN_BALL] THEN CONJ_TAC THENL
     [EXISTS_TAC `&1 - l` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `b - (l % a + (&1 - l) % b):real^3 = --(l % (a - b))`] THEN
    REWRITE_TAC[NORM_NEG; NORM_MUL] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`]]);;

(* An open set accumulating at y meets the two sectors near y. *)
let MOI_FSTR_OPEN_MEETS_SECTORS = prove
 (`!(t:real^3) A A' y rho U.
     ~(t = vec 0) /\ ~(A = vec 0) /\ ~(A' = vec 0) /\ t dot A = &0 /\ t dot A' = &0 /\
     ~(?s u. &0 <= u /\ A' = s % t + u % A) /\ ~(?s u. &0 <= u /\ A = s % t + u % A') /\
     &0 < rho /\ open U /\ y IN closure U
     ==> ?z. z IN U /\ z IN ball(y,rho) /\
             (moi_fstr_sec t A A' (z - y) \/ moi_fstr_sec t A' A (z - y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(t cross A:real^3 = vec 0) /\ ~(t cross A':real^3 = vec 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_POS_LT] THEN
    REWRITE_TAC[GSYM NORM_POW_2; NORM_CROSS] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`; REAL_SUB_RZERO] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `U INTER ball(y:real^3,rho) SUBSET
    {z | (t cross A) dot z = (t cross A) dot y} UNION
    {z | (t cross A') dot z = (t cross A') dot y}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^3`; `A:real^3`; `A':real^3`; `z - y:real^3`]
      MOI_FSTR_SEC_COVER) THEN
    ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN REWRITE_TAC[GSYM DOT_RSUB] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[MOI_FSTR_D_LIN; DOT_CROSS_SELF; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior({z | (t cross A) dot z = (t cross A) dot y} UNION
             {z:real^3 | (t cross A') dot z = (t cross A') dot y}) = {}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTERIOR_UNION_EQ_EMPTY; CLOSED_HYPERPLANE; INTERIOR_HYPERPLANE];
    ALL_TAC] THEN
  SUBGOAL_THEN `U INTER ball(y:real^3,rho) = {}` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!t:real^3->bool. s SUBSET interior t /\ interior t = {} ==> s = {}`) THEN
    EXISTS_TAC `{z | (t cross A) dot z = (t cross A) dot y} UNION
                {z:real^3 | (t cross A') dot z = (t cross A') dot y}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^3) IN closure U` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_BALL] THEN MESON_TAC[DIST_SYM]);;

(* Facts about the two pages at an edge [a,b] with triangles at c and c'. *)
let MOI_FSTR_EDGE_FACTS = prove
 (`!(m:(real^3->bool)->bool) a b c c'.
     lf_simplicial_complex m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     convex hull {a,b,c'} IN m /\ aff_dim(convex hull {a,b,c'}) = &2 /\ ~(c = c')
     ==> ~(b - a = vec 0) /\
         ~(moi_fstr_perp (b - a) (c - a) = vec 0) /\
         ~(moi_fstr_perp (b - a) (c' - a) = vec 0) /\
         (b - a) dot moi_fstr_perp (b - a) (c - a) = &0 /\
         (b - a) dot moi_fstr_perp (b - a) (c' - a) = &0 /\
         (b - a) cross moi_fstr_perp (b - a) (c - a) = (b - a) cross (c - a) /\
         (b - a) cross moi_fstr_perp (b - a) (c' - a) = (b - a) cross (c' - a) /\
         ~(?s u. &0 <= u /\
                 moi_fstr_perp (b - a) (c' - a) =
                 s % (b - a) + u % moi_fstr_perp (b - a) (c - a)) /\
         ~(?s u. &0 <= u /\
                 moi_fstr_perp (b - a) (c - a) =
                 s % (b - a) + u % moi_fstr_perp (b - a) (c' - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_NORMAL) THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c':real^3`] MOI_FSTR_TRI_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(b - a:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`b - a:real^3`; `c - a:real^3`] MOI_FSTR_PERP) THEN
  MP_TAC(ISPECL [`b - a:real^3`; `c' - a:real^3`] MOI_FSTR_PERP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(moi_fstr_perp (b - a) (c - a:real^3) = vec 0) /\
                ~(moi_fstr_perp (b - a) (c' - a:real^3) = vec 0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~((b - a) cross (c - a:real^3) = vec 0)` THEN
      UNDISCH_TAC `(b - a) cross moi_fstr_perp (b - a) (c - a:real^3) =
                   (b - a) cross (c - a)` THEN
      ASM_REWRITE_TAC[CROSS_RZERO] THEN MESON_TAC[];
      UNDISCH_TAC `~((b - a) cross (c' - a:real^3) = vec 0)` THEN
      UNDISCH_TAC `(b - a) cross moi_fstr_perp (b - a) (c' - a:real^3) =
                   (b - a) cross (c' - a)` THEN
      ASM_REWRITE_TAC[CROSS_RZERO] THEN MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSTR_SEPARATE_PAGES THEN
    EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSTR_SEPARATE_PAGES THEN
    EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* Near y in the edge, the two sectors lie in different sides. *)
let MOI_FSTR_SECTOR_SIDES = prove
 (`!(m:(real^3->bool)->bool) v r D E a b c c' y rho.
     FINITE m /\ combinatorial_manifold 2 m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     convex hull {a,b,c'} IN m /\ aff_dim(convex hull {a,b,c'}) = &2 /\ ~(c = c') /\
     moi_fstr_sides (UNIONS m) v r D E /\
     y IN segment(a,b) /\ &0 < rho /\ ball(y,rho) SUBSET ball(v,r) /\
     UNIONS m INTER ball(y,rho) SUBSET convex hull {a,b,c} UNION convex hull {a,b,c'}
     ==> ({z | z IN ball(y,rho) /\
               moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c - a))
                            (moi_fstr_perp (b - a) (c' - a)) (z - y)} SUBSET D /\
          {z | z IN ball(y,rho) /\
               moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c' - a))
                            (moi_fstr_perp (b - a) (c - a)) (z - y)} SUBSET E) \/
         ({z | z IN ball(y,rho) /\
               moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c - a))
                            (moi_fstr_perp (b - a) (c' - a)) (z - y)} SUBSET E /\
          {z | z IN ball(y,rho) /\
               moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c' - a))
                            (moi_fstr_perp (b - a) (c - a)) (z - y)} SUBSET D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `c:real^3`; `c':real^3`]
    MOI_FSTR_EDGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_fstr_sides (UNIONS m) (v:real^3) r D E` THEN
  REWRITE_TAC[moi_fstr_sides] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN segment[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; SEGMENT_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS m` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `convex hull {a:real^3,b,c}` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[a:real^3,b] SUBSET convex hull {a,b,c}` MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN ball(v,r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; CENTRE_IN_BALL]; ALL_TAC] THEN
  (* points of the sectors are off the surface *)
  SUBGOAL_THEN
   `!z:real^3. z IN ball(y,rho) /\
               (moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c - a))
                             (moi_fstr_perp (b - a) (c' - a)) (z - y) \/
                moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c' - a))
                             (moi_fstr_perp (b - a) (c - a)) (z - y))
               ==> z IN D UNION E`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `(D:real^3->bool) UNION E`)) THEN
    REWRITE_TAC[IN_DIFF] THEN (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    DISCH_TAC THEN
    (SUBGOAL_THEN `(z:real^3) IN convex hull {a,b,c} \/ z IN convex hull {a,b,c'}`
     MP_TAC THENL [ASM SET_TAC[]; DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC)]) THENL
     [MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`; `y:real^3`; `z:real^3`]
        MOI_FSTR_PAGE_OF);
      MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c':real^3`; `y:real^3`; `z:real^3`]
        MOI_FSTR_PAGE_OF)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `z - y:real^3`)) THENL
     [MP_TAC(ISPECL [`b - a:real^3`; `moi_fstr_perp (b - a) (c - a:real^3)`;
                     `moi_fstr_perp (b - a) (c' - a:real^3)`; `s:real`; `u:real`]
        MOI_FSTR_SEC_OFFPAGE);
      MP_TAC(ISPECL [`b - a:real^3`; `moi_fstr_perp (b - a) (c' - a:real^3)`;
                     `moi_fstr_perp (b - a) (c - a:real^3)`; `s:real`; `u:real`]
        MOI_FSTR_SEC_OFFPAGE)] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ABBREV_TAC `W1 = {z | z IN ball(y,rho) /\
                        moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c - a))
                                     (moi_fstr_perp (b - a) (c' - a:real^3)) (z - y)}` THEN
  ABBREV_TAC `W2 = {z | z IN ball(y,rho) /\
                        moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c' - a))
                                     (moi_fstr_perp (b - a) (c - a:real^3)) (z - y)}` THEN
  SUBGOAL_THEN `(W1 SUBSET (D:real^3->bool) \/ W1 SUBSET E) /\
                (W2 SUBSET (D:real^3->bool) \/ W2 SUBSET E)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FSTR_CONNECTED_IN_ONE THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["W1"; "W2"] THEN
    SIMP_TAC[MOI_FSTR_SEC_CONN; ASSUME `&0 < rho`] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `(?z:real^3. z IN D /\ (z IN W1 \/ z IN W2)) /\
    (?z:real^3. z IN E /\ (z IN W1 \/ z IN W2))`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W1"; "W2"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`b - a:real^3`; `moi_fstr_perp (b - a) (c - a:real^3)`;
                     `moi_fstr_perp (b - a) (c' - a:real^3)`; `y:real^3`; `rho:real`;
                     `D:real^3->bool`] MOI_FSTR_OPEN_MEETS_SECTORS);
      MP_TAC(ISPECL [`b - a:real^3`; `moi_fstr_perp (b - a) (c - a:real^3)`;
                     `moi_fstr_perp (b - a) (c' - a:real^3)`; `y:real^3`; `rho:real`;
                     `E:real^3->bool`] MOI_FSTR_OPEN_MEETS_SECTORS)] THEN
    ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN MESON_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `zd:real^3`) (X_CHOOSE_TAC `ze:real^3`))] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && is_binary "SUBSET" (lhand(concl th))))) THEN
  ASM SET_TAC[]);;

(* The normal of a triangle at an edge point points into the sector next to *)
(* its page; the sign decides the side of that sector.                      *)
let MOI_FSTR_NORMAL_WITNESS = prove
 (`!(m:(real^3->bool)->bool) v r D E a b c c' y rho.
     FINITE m /\ combinatorial_manifold 2 m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     v IN convex hull {a,b,c} /\ moi_fstr_sides (UNIONS m) v r D E /\
     y IN segment(a,b) /\ &0 < rho /\ ball(y,rho) SUBSET ball(v,r)
     ==> ?z. z IN ball(y,rho) /\
             moi_fstr_sec (b - a) (moi_fstr_perp (b - a) (c - a))
                          (moi_fstr_perp (b - a) (c' - a)) (z - y) /\
             (moi_fstr_posn D v r (convex hull {a,b,c}) ((b - a) cross (c - a))
              ==> z IN D) /\
             (~moi_fstr_posn D v r (convex hull {a,b,c}) ((b - a) cross (c - a))
              ==> z IN E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(b - a:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the sign data at relative interior points *)
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`]
    MOI_FSTR_TRI_POSN_HYPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `convex hull {a:real^3,b,c}`;
                 `(b - a) cross (c - a:real^3)`] MOI_FSTR_POSN_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the point p = y + l (c - y) of the relative interior *)
  MP_TAC(ASSUME `(y:real^3) IN segment(a,b)`) THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `y - a:real^3 = th % (b - a)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun eq -> if is_eq(concl eq) && lhs(concl eq) = `y:real^3`
                          then SUBST1_TAC eq else failwith "no") THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun eq -> is_eq(concl eq) &&
    lhs(concl eq) = `y:real^3`)) THEN
  MP_TAC(ISPECL [`&1`; `norm(c - y:real^3)`; `rho / &2`] MOI_FSTR_SMALL) THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_LT_01; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `y + l % (c - y) IN relative_interior(convex hull {a:real^3,b,c})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSTR_RELINT_PT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dist(y:real^3,y + l % (c - y)) < rho / &2` ASSUME_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `y - (y + l % x):real^3 = --(l % x)`] THEN
    ASM_SIMP_TAC[NORM_NEG; NORM_MUL; REAL_ARITH `&0 < l ==> abs l = l`];
    ALL_TAC] THEN
  SUBGOAL_THEN `y + l % (c - y) IN ball(v:real^3,r)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_binary "SUBSET" (concl th) && lhand(concl th) = `ball(y:real^3,rho)`)) THEN
    REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y + l % (c - y):real^3` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `moi_fstr_posn`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` STRIP_ASSUME_TAC) THEN
  (* page coordinates of p - y; from here on no assumption-rewriting of the goal *)
  MP_TAC(ISPECL [`b - a:real^3`; `c - a:real^3`] MOI_FSTR_PERP) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `mu = ((c - a) dot (b - a:real^3)) / ((b - a) dot (b - a))` THEN
  ABBREV_TAC `A = moi_fstr_perp (b - a) (c - a:real^3)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(A:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((b - a) cross (c - a:real^3) = vec 0)` THEN
    UNDISCH_TAC `(b - a) cross A = (b - a) cross (c - a:real^3)` THEN
    FIRST_X_ASSUM(fun eq -> if is_eq(concl eq) && lhs(concl eq) = `A:real^3`
                            then SUBST1_TAC eq else failwith "no") THEN
    REWRITE_TAC[CROSS_RZERO] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c - y:real^3 = A + (mu - th) % (b - a)` ASSUME_TAC THENL
   [SUBGOAL_THEN `c - y:real^3 = (c - a) - (y - a)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun eq -> if is_eq(concl eq) && lhs(concl eq) = `y - a:real^3`
                            then SUBST1_TAC eq else failwith "no") THEN
    FIRST_X_ASSUM(fun eq -> if is_eq(concl eq) && lhs(concl eq) = `c - a:real^3`
                            then SUBST1_TAC eq else failwith "no") THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b - a:real^3`; `A:real^3`; `moi_fstr_perp (b - a) (c' - a:real^3)`;
                 `l * (mu - th)`; `l:real`] MOI_FSTR_SEC_NORMAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:real`; `norm((b - a) cross (c - a:real^3))`; `min ep (rho / &2)`]
    MOI_FSTR_SMALL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NORM_POS_LE; REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(y + l % (c - y)) + k % ((b - a) cross (c - a:real^3))` THEN
  SUBGOAL_THEN `dist(y + l % (c - y),(y + l % (c - y)) + k % ((b - a) cross (c - a:real^3))) =
                k * norm((b - a) cross (c - a))`
  ASSUME_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `p - (p + x):real^3 = --x`; NORM_NEG; NORM_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((b - a) cross (c - a)) dot ((b - a) cross (c - a:real^3))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`y:real^3`; `y + l % (c - y):real^3`;
                   `(y + l % (c - y)) + k % ((b - a) cross (c - a:real^3))`]
      DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `((y + l % (c - y)) + k % ((b - a) cross (c - a))) - y:real^3 =
      (l * (mu - th)) % (b - a) + l % A + k % ((b - a) cross A)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun eq -> if is_eq(concl eq) && lhs(concl eq) = `c - y:real^3`
                              then SUBST1_TAC eq else failwith "no") THEN
      FIRST_X_ASSUM(fun eq -> if is_eq(concl eq) &&
                                 lhs(concl eq) = `(b - a) cross (A:real^3)`
                              then SUBST1_TAC eq else failwith "no") THEN
      VECTOR_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun eq -> is_cond(concl eq))) THEN
    REWRITE_TAC[ASSUME `moi_fstr_posn D (v:real^3) r (convex hull {a,b,c})
                          ((b - a) cross (c - a))`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1);
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun eq -> is_cond(concl eq))) THEN
    REWRITE_TAC[ASSUME `~moi_fstr_posn D (v:real^3) r (convex hull {a,b,c})
                          ((b - a) cross (c - a))`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_BALL; VECTOR_ARITH `(p + x) - p:real^3 = x`; DOT_RMUL] THEN
  (CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]));;

(* (O2): the signs of the two triangles at an edge through v are opposite. *)
let MOI_FSTR_SG_EDGE = prove
 (`!(m:(real^3->bool)->bool) v r D E a b c c'.
     FINITE m /\ combinatorial_manifold 2 m /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     convex hull {a,b,c'} IN m /\ aff_dim(convex hull {a,b,c'}) = &2 /\ ~(c = c') /\
     (v = a \/ v = b) /\ moi_fstr_sides (UNIONS m) v r D E
     ==> moi_fstr_sg D v r a b c' = --(moi_fstr_sg D v r a b c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_TRI_INDEP) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN convex hull {a,b,c} /\ v IN convex hull {a,b,c'}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ DISJOINT (D:real^3->bool) E` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fstr_sides]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `v:real^3`; `r:real`] MOI_FSTR_SEG_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                 `c':real^3`; `y:real^3`] MOI_FSTR_EDGE_PAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho = min rho1 (r - dist(v:real^3,y))` THEN
  SUBGOAL_THEN `&0 < rho /\ ball(y:real^3,rho) SUBSET ball(v,r) /\
                UNIONS m INTER ball(y,rho) SUBSET
                convex hull {a,b,c} UNION convex hull {a,b,c'}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN ball(v,r)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `z:real^3` THEN
      MP_TAC(ISPECL [`v:real^3`; `y:real^3`; `z:real^3`] DIST_TRIANGLE) THEN
      EXPAND_TAC "rho" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS m INTER ball(y:real^3,rho1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (M:real^3->bool) INTER s SUBSET M INTER t`) THEN
      MATCH_MP_TAC SUBSET_BALL THEN EXPAND_TAC "rho" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`; `c':real^3`;
                 `y:real^3`; `rho:real`] MOI_FSTR_SECTOR_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`; `c':real^3`;
                 `y:real^3`; `rho:real`] MOI_FSTR_NORMAL_WITNESS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `v:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `a:real^3`; `b:real^3`; `c':real^3`; `c:real^3`;
                 `y:real^3`; `rho:real`] MOI_FSTR_NORMAL_WITNESS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `moi_fstr_posn D (v:real^3) r (convex hull {a,b,c'}) ((b - a) cross (c' - a)) <=>
    ~moi_fstr_posn D v r (convex hull {a,b,c}) ((b - a) cross (c - a))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC
     `moi_fstr_posn D (v:real^3) r (convex hull {a,b,c}) ((b - a) cross (c - a))` THEN
    ASM_CASES_TAC
     `moi_fstr_posn D (v:real^3) r (convex hull {a,b,c'}) ((b - a) cross (c' - a))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj(concl th) && is_conj(lhand(concl th)))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fstr_sg] THEN
  ASM_CASES_TAC
   `moi_fstr_posn D (v:real^3) r (convex hull {a,b,c}) ((b - a) cross (c - a))` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

