(* ========================================================================= *)
(* pc_moi_s34_src: the Sec 34 unit s34_src.  Main theorem SRC =              *)
(* MOI_S34_SRC (pc_moi_s34_stmt.ml): from the fine subdivision lemma         *)
(* (MOI_S34_LF_FINE, antecedent), subdivisions (tt,kk) of (t,k) on which h   *)
(* varies by less than ep/4 over closed stars of simplices of kk, with kk a  *)
(* combinatorial 3-manifold and PL 2-sphere links in tt at the vertices of   *)
(* kk (Moise p.239).                                                         *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The open cover W x0 of |t|, closed stars, vertices and links.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S4R_COVER_OPEN = prove
 (`!(t:(real^N->bool)->bool) k (h:real^N->real^3) ep x0.
     lf_simplicial_complex t /\ k SUBSET t /\
     h continuous_on UNIONS t /\ (lift o ep) continuous_on UNIONS k
     ==> open_in (subtopology euclidean (UNIONS t))
           {y | y IN UNIONS t /\ dist(h y,h x0) < ep x0 / &16 /\
                (y IN UNIONS k ==> ep x0 / &2 < ep y)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS k SUBSET UNIONS (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN UNIONS t /\ dist(h y,h x0) < ep x0 / &16 /\
         (y IN UNIONS k ==> ep x0 / &2 < ep y)} =
    {y | y IN UNIONS t /\ (h:real^N->real^3) y IN ball(h x0,ep x0 / &16)} INTER
    (UNIONS t DIFF
     {y | y IN UNIONS k /\ (lift o ep) y IN {z:real^1 | z$1 <= ep x0 / &2}})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF; IN_BALL; o_THM;
                GSYM drop; LIFT_DROP] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[DIST_SYM; DE_MORGAN_THM; REAL_NOT_LE] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_IN_TRANS THEN EXISTS_TAC `UNIONS (k:(real^N->bool)->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
      ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; ETA_AX];
      MATCH_MP_TAC MOI_FDN_LF_CLOSED_IN_UNIONS THEN ASM_REWRITE_TAC[]]]);;

let MOI_S4R_CSTAR = prove
 (`!(tt:(real^N->bool)->bool) s v.
     s IN tt /\ v IN s /\ {v} IN tt
     ==> s UNION moi_s34_cstar tt s SUBSET
         UNIONS {q | q IN tt /\ ~(q INTER moi_s34_cstar tt {v} = {})}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET moi_s34_cstar tt {v}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_cstar; IN_SING] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
   [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    UNDISCH_TAC `(x:real^N) IN moi_s34_cstar tt s` THEN
    REWRITE_TAC[moi_s34_cstar; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC))
      ASSUME_TAC)) THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `u:real^N` THEN
    ASM SET_TAC[]]);;

let MOI_S4R_VERTEX = prove
 (`!(kk:(real^N->bool)->bool) s x.
     lf_simplicial_complex kk /\ s IN kk /\ x IN s
     ==> ?v. v IN s /\ {v} IN kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[simplex]] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `vv:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?v:real^N. v IN vv` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `v:real^N` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `(face_of):(real^N->bool)->(real^N->bool)->bool`))
        (concl th))) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]]);;

let MOI_S4R_CARRIER_IN_SUB = prove
 (`!(t:(real^N->bool)->bool) k s w.
     lf_simplicial_complex t /\ simplicial_subcomplex k t /\
     s IN t /\ w IN relative_interior s /\ w IN UNIONS k
     ==> s IN k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  UNDISCH_TAC `(w:real^N) IN UNIONS k` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^N->bool) IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER u face_of s /\ s INTER u face_of u`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER u = s` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(s:real^N->bool) INTER u`; `s:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    length(fst(strip_forall(concl th))) = 2 &&
    can (find_term (fun t -> t = `(face_of):(real^N->bool)->(real^N->bool)->bool`))
      (concl th) && can (find_term (fun t -> t = `k:(real^N->bool)->bool`)) (concl th))) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(s:real^N->bool) INTER u face_of u` THEN ASM_REWRITE_TAC[]);;

let MOI_S4R_LINK = prove
 (`!(t:(real^N->bool)->bool) k tt w.
     lf_simplicial_complex t /\ simplicial_subcomplex k t /\
     (!v. {v} IN k ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     lf_simplicial_complex tt /\ UNIONS tt = UNIONS t /\
     {w} IN tt /\ w IN UNIONS k
     ==> pl_sphere 2 (UNIONS (simplicial_link tt w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `w:real^N`] MOI_FM3_CARRIER_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^N) IN UNIONS k` THEN
    UNDISCH_TAC `simplicial_subcomplex (k:(real^N->bool)->bool) t` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `v:real^N`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC INTERIOR_LINK_RETRIANGULATION THEN
  MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `v:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4R_CARRIER_IN_SUB THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `w:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (k:(real^N->bool)->bool) t` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING] THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[simplex] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `vv:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `{v:real^N} face_of s` MP_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
      SUBGOAL_THEN `{v:real^N} INTER s face_of s` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `{v:real^N} INTER s = {v}` (fun th -> REWRITE_TAC[th]) THEN
      ASM SET_TAC[];
      REWRITE_TAC[FACE_OF_SING]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    UNDISCH_TAC `~((w:real^N) IN UNIONS (simplicial_link t v))` THEN
    REWRITE_TAC[IN_UNIONS]]);;

(* ------------------------------------------------------------------------- *)
(* Skeleta, the tube structure, the cover, fineness and the theorem SRC.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4R_SKELETON_SUB = prove
 (`!(kk:(real^N->bool)->bool) tt n.
     simplicial_subcomplex kk tt ==> simplicial_subcomplex (skeleton n kk) tt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_subcomplex; skeleton; IN_ELIM_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      TRANS_TAC INT_LE_TRANS `aff_dim(s:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]]);;

let MOI_S4R_TUBE = prove
 (`!(t:(real^N->bool)->bool) k tt kk.
     lf_simplicial_complex t /\ simplicial_subcomplex k t /\
     combinatorial_manifold_with_boundary 3 k /\
     (!v. {v} IN k ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     lf_simplicial_complex tt /\ subdivides tt t /\
     simplicial_subcomplex kk tt /\ subdivides kk k
     ==> moi_s34_tube tt kk`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (tt:(real^N->bool)->bool) = UNIONS t /\
                UNIONS (kk:(real^N->bool)->bool) = UNIONS k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `subdivides (tt:(real^N->bool)->bool) t` THEN
    UNDISCH_TAC `subdivides (kk:(real^N->bool)->bool) k` THEN
    REWRITE_TAC[subdivides] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (k:(real^N->bool)->bool) /\
                lf_simplicial_complex (kk:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THENL
     [EXISTS_TAC `t:(real^N->bool)->bool` THEN
      UNDISCH_TAC `simplicial_subcomplex (k:(real^N->bool)->bool) t`;
      EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      UNDISCH_TAC `simplicial_subcomplex (kk:(real^N->bool)->bool) tt`] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[REWRITE_RULE[simplicial_subcomplex] th]);
    ALL_TAC] THEN
  REWRITE_TAC[moi_s34_tube; graph_in_complex] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `\x:real^N. x`; `\x:real^N. x`] MOI_FMB_PL_INVARIANT_LF) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                    GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX];
    MATCH_MP_TAC MOI_S4R_SKELETON_SUB THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[skeleton; IN_ELIM_THM] THEN MESON_TAC[];
    X_GEN_TAC `w:real^N` THEN REWRITE_TAC[skeleton; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4R_LINK THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (kk:(real^N->bool)->bool) tt` THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `{w:real^N}` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(w:real^N) IN UNIONS kk` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING];
        ASM_REWRITE_TAC[]]]]);;

let MOI_S4R_COVER = prove
 (`!(t:(real^N->bool)->bool) k (h:real^N->real^3) ep.
     lf_simplicial_complex t /\ simplicial_subcomplex k t /\
     h continuous_on UNIONS t /\ (lift o ep) continuous_on UNIONS k /\
     (!x. x IN UNIONS k ==> &0 < ep x)
     ==> (!w. w IN (UNIONS t DIFF UNIONS k) INSERT
                   IMAGE (\x0. {y | y IN UNIONS t /\
                                    dist(h y,h x0) < ep x0 / &16 /\
                                    (y IN UNIONS k ==> ep x0 / &2 < ep y)})
                         (UNIONS k)
              ==> open_in (subtopology euclidean (UNIONS t)) w) /\
         UNIONS t SUBSET
         UNIONS ((UNIONS t DIFF UNIONS k) INSERT
                 IMAGE (\x0. {y | y IN UNIONS t /\
                                  dist(h y,h x0) < ep x0 / &16 /\
                                  (y IN UNIONS k ==> ep x0 / &2 < ep y)})
                       (UNIONS k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:(real^N->bool)->bool) SUBSET t` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (k:(real^N->bool)->bool) t` THEN
    SIMP_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC MOI_FDN_LF_CLOSED_IN_UNIONS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x0:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S4R_COVER_OPEN THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; UNIONS_INSERT; IN_UNION; IN_DIFF; UNIONS_IMAGE;
                IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN UNIONS k` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[DIST_REFL] THEN
    SUBGOAL_THEN `&0 < ep (y:real^N)` MP_TAC THENL
     [ASM_MESON_TAC[]; REAL_ARITH_TAC]]);;

let MOI_S4R_FINE = prove
 (`!(t:(real^N->bool)->bool) k (h:real^N->real^3) ep tt kk.
     lf_simplicial_complex tt /\ simplicial_subcomplex kk tt /\
     UNIONS kk = UNIONS k /\
     (!v. {v} IN tt
          ==> ?w. w IN (UNIONS t DIFF UNIONS k) INSERT
                       IMAGE (\x0. {y | y IN UNIONS t /\
                                        dist(h y,h x0) < ep x0 / &16 /\
                                        (y IN UNIONS k ==> ep x0 / &2 < ep y)})
                             (UNIONS k) /\
                  UNIONS {q | q IN tt /\ ~(q INTER moi_s34_cstar tt {v} = {})}
                  SUBSET w)
     ==> moi_s34_fine tt kk h ep`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fn")))) THEN
  REWRITE_TAC[moi_s34_fine] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `x:real^N`; `y:real^N`; `z:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL
   [MP_TAC(ASSUME `simplicial_subcomplex (kk:(real^N->bool)->bool) tt`) THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS kk` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`; `x:real^N`]
    MOI_S4R_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`; `v:real^N`]
    MOI_S4R_CSTAR) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "fn" (MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(s:real^N->bool) UNION moi_s34_cstar tt s SUBSET w` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {q:real^N->bool | q IN tt /\
                                          ~(q INTER moi_s34_cstar tt {v} = {})}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[SUBSET; IN_UNION]) THEN
  SUBGOAL_THEN `(x:real^N) IN w /\ (y:real^N) IN w /\ (z:real^N) IN w`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC)) THENL
   [UNDISCH_TAC `(x:real^N) IN w` THEN ASM_REWRITE_TAC[IN_DIFF];
    UNDISCH_TAC `(x:real^N) IN w` THEN UNDISCH_TAC `(y:real^N) IN w` THEN
    UNDISCH_TAC `(z:real^N) IN w` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(h:real^N->real^3) y`; `(h:real^N->real^3) x0`;
                   `(h:real^N->real^3) z`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`(h:real^N->real^3) x0`; `(h:real^N->real^3) z`] DIST_SYM) THEN
    UNDISCH_TAC `dist((h:real^N->real^3) y,h x0) < ep (x0:real^N) / &16` THEN
    UNDISCH_TAC `dist((h:real^N->real^3) z,h x0) < ep (x0:real^N) / &16` THEN
    UNDISCH_TAC `ep (x0:real^N) / &2 < ep (x:real^N)` THEN
    REAL_ARITH_TAC]);;

let SRC = prove
 (MOI_S34_SRC,
  DISCH_THEN(LABEL_TAC "lff") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`] MOI_S4R_COVER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "lff" (MP_TAC o SPECL
   [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
    `(UNIONS t DIFF UNIONS k) INSERT
     IMAGE (\x0. {y | y IN UNIONS t /\
                      dist((h:real^N->real^3) y,h x0) < ep x0 / &16 /\
                      (y IN UNIONS k ==> ep x0 / &2 < ep y)})
           (UNIONS (k:(real^N->bool)->bool))`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:(real^N->bool)->bool` (X_CHOOSE_THEN
    `kk:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
  ASM_REWRITE_TAC[moi_s34_src] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4R_TUBE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4R_FINE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `subdivides (kk:(real^N->bool)->bool) k` THEN
    SIMP_TAC[subdivides]]);;

