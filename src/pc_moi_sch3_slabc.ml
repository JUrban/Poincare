(* ========================================================================= *)
(* pc_moi_sch3_slabc: MOI_SSC_STAR : |- MOI_SSL_STAR_STMT (Moise GTM 47,    *)
(* Sec 17, Lemma 6, p.124: the section of the closed star of the vertex     *)
(* at its level is a polyhedral 2-cell, and the frontier of the star part   *)
(* of the slab is simply imbedded).                                         *)
(* The first section is the radial transfer.  A finite union S of polytopes *)
(* met at most once by each ray from a point is PL homeomorphic to the part *)
(* of the relative frontier of a surrounding polytope that it subtends,     *)
(* each polytope corresponding to its own sector (the partial form of the   *)
(* fan construction of MOI_CMB_STAR_SHAPED_PL_SPHERE_0 in pc_moi_comb.ml).  *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_slabb.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_sch3_fib.ml";;

prioritize_real();;
type_invention_error := true;;

(* The radial point of s on the ray through u, when it is unique.          *)

let MOI_SSC_RADIAL_AT = prove
 (`!(s:real^N->bool) u r.
     &0 < r /\ r % u IN s /\ (!r'. &0 < r' /\ r' % u IN s ==> r' = r)
     ==> moi_cmb_radial s u = r % u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_cmb_radial] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:real` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* On the cone over one member f of a radially unique family, the radial   *)
(* map is the central projection onto f.                                    *)

let MOI_SSC_RADIAL_CONE = prove
 (`!(ff:(real^N->bool)->bool) f y.
     ~(vec 0 IN UNIONS ff) /\
     (!x y r. x IN UNIONS ff /\ y IN UNIONS ff /\ &0 < r /\ y = r % x ==> y = x) /\
     f IN ff /\ y IN conic hull f /\ ~(y = vec 0)
     ==> ?x c. x IN f /\ &0 < c /\ y = c % x /\ moi_cmb_radial (UNIONS ff) y = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ru") MP_TAC)) THEN
  REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [ASM_CASES_TAC `c = &0` THENL
     [UNDISCH_TAC `~(y:real^N = vec 0)` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS ff /\ ~(x = vec 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(vec 0:real^N IN UNIONS ff)` THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `f:real^N->bool` THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `c:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv c % (c % x) = x:real^N` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_cmb_radial (UNIONS ff) (c % x:real^N) = inv c % (c % x)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_SSC_RADIAL_AT THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    X_GEN_TAC `r':real` THEN STRIP_TAC THEN
    USE_THEN "ru" (MP_TAC o SPECL [`x:real^N`; `r' % c % x:real^N`; `r' * c:real`]) THEN
    REWRITE_TAC[ASSUME `(x:real^N) IN UNIONS ff`;
                ASSUME `r' % c % x:real^N IN UNIONS ff`;
                MATCH_MP REAL_LT_MUL
                  (CONJ (ASSUME `&0 < r'`) (ASSUME `&0 < c`))] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM VECTOR_MUL_LID] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN DISCH_TAC THEN
    UNDISCH_TAC `r' * c = &1` THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]]);;

(* The fan polytopes: the sectors over the members of ff cut by the proper *)
(* faces of q cover the part of rf q subtended by UNIONS ff.                *)

let MOI_SSC_FAN_UNION = prove
 (`!(ff:(real^N->bool)->bool) q.
     polyhedron q
     ==> UNIONS {conic hull f INTER e | f IN ff /\ e IN {e | e face_of q /\ ~(e = q)}} =
         relative_frontier q INTER conic hull (UNIONS ff)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON_ALT] THEN
  REWRITE_TAC[UNIONS_GSPEC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNIONS; CONIC_HULL_EXPLICIT] THEN
  MESON_TAC[]);;

let MOI_SSC_FAN_POLYTOPES = prove
 (`!(ff:(real^N->bool)->bool) q.
     FINITE ff /\ (!f. f IN ff ==> polytope f) /\ polytope q
     ==> FINITE {conic hull f INTER e | f IN ff /\ e IN {e | e face_of q /\ ~(e = q)}} /\
         (!k. k IN {conic hull f INTER e | f IN ff /\ e IN {e | e face_of q /\ ~(e = q)}}
              ==> polytope k)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`\f e:real^N->bool. conic hull f INTER e`;
                   `ff:(real^N->bool)->bool`;
                   `\f:real^N->bool. {e:real^N->bool | e face_of q /\ ~(e = q)}`]
      FINITE_PRODUCT_DEPENDENT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e:real^N->bool | e face_of q}` THEN
    ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[];
    UNDISCH_TAC `k IN {conic hull f INTER e | f IN ff /\
                       e IN {e:real^N->bool | e face_of q /\ ~(e = q)}}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE];
      MATCH_MP_TAC POLYHEDRON_CONIC_HULL_POLYTOPE THEN ASM_MESON_TAC[]]]);;

(* A simplex of a refinement of a cover lies in one member of the cover.    *)

let MOI_SSC_SIMPLEX_IN_COVER = prove
 (`!t s (u:(real^N->bool)->bool).
     simplicial_complex t /\ s IN t /\ ~(s = {}) /\ UNIONS t = UNIONS u /\
     (!k. k IN u ==> ?f. f SUBSET t /\ k = UNIONS f)
     ==> ?k. k IN u /\ s SUBSET k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PLT_SIMPLEX_IN_COVER THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS u` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS t:real^N->bool`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The sector and projection properties of a refinement of the fan cover   *)
(* (the cover kept as a variable pf).                                       *)

let MOI_SSC_FAN_TRIANG_GEN = prove
 (`!(ff:(real^N->bool)->bool) q pf L.
     (!f. f IN ff ==> ~(vec 0 IN affine hull f)) /\ ~(vec 0 IN UNIONS ff) /\
     (!x y r. x IN UNIONS ff /\ y IN UNIONS ff /\ &0 < r /\ y = r % x ==> y = x) /\
     polytope q /\ vec 0 IN relative_interior q /\
     simplicial_complex L /\ UNIONS L = UNIONS pf /\
     (!k. k IN pf ==> ?c. c SUBSET L /\ k = UNIONS c) /\
     (!k. k IN pf <=> ?f e. f IN ff /\ e face_of q /\ ~(e = q) /\
                            k = conic hull f INTER e) /\
     UNIONS pf = relative_frontier q INTER conic hull (UNIONS ff)
     ==> (!f. f IN ff
              ==> relative_frontier q INTER conic hull f =
                  UNIONS {d | d IN L /\ d SUBSET conic hull f}) /\
         (!d. d IN L /\ ~(d = {})
              ==> ?a m. !y. y IN d
                            ==> &0 < a dot y /\
                                moi_cmb_radial (UNIONS ff) y = inv(a dot y) % y /\
                                m dot y = &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ru") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ref")
       (CONJUNCTS_THEN2 (LABEL_TAC "mem") ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `convex (q:real^N->bool) /\ polyhedron q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_POLYHEDRON]; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the sector of each member is a union of simplices *)
    X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPEC `q:real^N->bool` RELATIVE_FRONTIER_OF_POLYHEDRON_ALT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
        UNDISCH_TAC `(y:real^N) IN relative_frontier q` THEN REWRITE_TAC[th]) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(conic hull f INTER e:real^N->bool) IN pf` ASSUME_TAC THENL
       [USE_THEN "mem" (fun th -> REWRITE_TAC[th]) THEN
        MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `e:real^N->bool`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "ref" (MP_TAC o C MATCH_MP
        (ASSUME `(conic hull f INTER e:real^N->bool) IN pf`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^N) IN UNIONS c` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          is_eq(concl th) && rand(concl th) = `UNIONS c:real^N->bool`)) THEN
        ASM_REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `conic hull f INTER e:real^N->bool = UNIONS c`) THEN
      MP_TAC(ASSUME `(c:(real^N->bool)->bool) SUBSET L`) THEN
      MP_TAC(ASSUME `(d:real^N->bool) IN c`) THEN SET_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `d:real^N->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_INTER] THEN
      MP_TAC(ASSUME `UNIONS L = UNIONS (pf:(real^N->bool)->bool)`) THEN
      MP_TAC(ASSUME `UNIONS pf = relative_frontier q INTER
                     conic hull (UNIONS ff:real^N->bool)`) THEN
      MP_TAC(ASSUME `(d:real^N->bool) IN L`) THEN SET_TAC[]];
    (* the central projection on each simplex *)
    X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `d:real^N->bool`; `pf:(real^N->bool)->bool`]
      MOI_SSC_SIMPLEX_IN_COVER) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ref" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    USE_THEN "mem" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `e:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `k:real^N->bool`)) THEN
    MP_TAC(ISPEC `f:real^N->bool` MOI_CMB_HYPERPLANE_FUNCTIONAL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(X_CHOOSE_TAC `a:real^N`)] THEN
    MP_TAC(ISPECL [`q:real^N->bool`; `e:real^N->bool`] MOI_CMB_FACE_FUNCTIONAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:real^N`) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `m:real^N`] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN conic hull f /\ y IN e` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `(d:real^N->bool) SUBSET conic hull f INTER e`) THEN
      MP_TAC(ASSUME `(y:real^N) IN d`) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m:real^N) dot y = &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^N = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(m:real^N) dot y = &1` THEN
      ASM_REWRITE_TAC[DOT_RZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `f:real^N->bool`; `y:real^N`]
      MOI_SSC_RADIAL_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ru" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `c:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `y:real^N`)) THEN
    SUBGOAL_THEN `(a:real^N) dot x = &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `a:real^N`)) (concl th) && is_forall(concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_RMUL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_SSC_FAN_TRIANG = prove
 (`!(ff:(real^N->bool)->bool) q.
     FINITE ff /\ (!f. f IN ff ==> polytope f /\ ~(vec 0 IN affine hull f)) /\
     (!x y r. x IN UNIONS ff /\ y IN UNIONS ff /\ &0 < r /\ y = r % x ==> y = x) /\
     polytope q /\ vec 0 IN relative_interior q
     ==> ?L. simplicial_complex L /\
             UNIONS L = relative_frontier q INTER conic hull (UNIONS ff) /\
             (!f. f IN ff
                  ==> relative_frontier q INTER conic hull f =
                      UNIONS {d | d IN L /\ d SUBSET conic hull f}) /\
             (!d. d IN L /\ ~(d = {})
                  ==> ?a m. !y. y IN d
                                ==> &0 < a dot y /\
                                    moi_cmb_radial (UNIONS ff) y = inv(a dot y) % y /\
                                    m dot y = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(vec 0:real^N IN UNIONS ff)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN STRIP_TAC THEN ASM_MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `q:real^N->bool`] MOI_SSC_FAN_POLYTOPES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `{conic hull f INTER e | f IN ff /\
                  e IN {e:real^N->bool | e face_of q /\ ~(e = q)}}`
    POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN
  MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `q:real^N->bool`] MOI_SSC_FAN_UNION) THEN
  REWRITE_TAC[MATCH_MP POLYTOPE_IMP_POLYHEDRON
    (ASSUME `polytope (q:real^N->bool)`)] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `q:real^N->bool`;
                 `{conic hull f INTER e | f IN ff /\
                   e IN {e:real^N->bool | e face_of q /\ ~(e = q)}}`;
                 `L:(real^N->bool)->bool`] MOI_SSC_FAN_TRIANG_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_SSC_CONIC_HULL_UNIONS = prove
 (`!ff:(real^N->bool)->bool.
     conic hull (UNIONS ff) = UNIONS {conic hull f | f IN ff}`,
  GEN_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
  REWRITE_TAC[EXTENSION; CONIC_HULL_EXPLICIT; IN_ELIM_THM; IN_UNIONS] THEN
  MESON_TAC[]);;

(* Radial transfer with apex the origin.                                    *)

let MOI_SSC_RADIAL_TRANSFER_0 = prove
 (`!(ff:(real^N->bool)->bool) q.
     FINITE ff /\ (!f. f IN ff ==> polytope f /\ ~(vec 0 IN affine hull f)) /\
     (!x y r. x IN UNIONS ff /\ y IN UNIONS ff /\ &0 < r /\ y = r % x ==> y = x) /\
     polytope q /\ vec 0 IN relative_interior q /\ UNIONS ff SUBSET affine hull q
     ==> ?h h'. pl_homeomorphism
                  (relative_frontier q INTER conic hull (UNIONS ff),UNIONS ff) (h,h') /\
                !f. f IN ff ==> IMAGE h (relative_frontier q INTER conic hull f) = f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ru") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(vec 0:real^N IN UNIONS ff)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN STRIP_TAC THEN ASM_MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (q:real^N->bool) /\ bounded q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(vec 0:real^N IN relative_frontier q)` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the radial image of each sector is its member *)
  SUBGOAL_THEN
   `!f. f IN ff
        ==> IMAGE (moi_cmb_radial (UNIONS ff))
                  (relative_frontier q INTER conic hull f) = f:real^N->bool`
  (LABEL_TAC "imf") THENL
   [X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(y:real^N = vec 0)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `f:real^N->bool`; `y:real^N`]
        MOI_SSC_RADIAL_CONE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ru" ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':real^N` (X_CHOOSE_THEN `c:real`
        STRIP_ASSUME_TAC)) THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS ff /\ ~(x = vec 0)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[IN_UNIONS]]; ALL_TAC] THEN
      MP_TAC(ISPECL [`q:real^N->bool`; `vec 0:real^N`; `x:real^N`]
        RAY_TO_RELATIVE_FRONTIER) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN ANTS_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d % x:real^N` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(d % x:real^N) IN conic hull f` ASSUME_TAC THENL
       [REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`d:real`; `x:real^N`] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `f:real^N->bool`; `d % x:real^N`]
        MOI_SSC_RADIAL_CONE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':real^N` (X_CHOOSE_THEN `c:real`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "ru" MATCH_MP_TAC THEN EXISTS_TAC `d / c` THEN
      ASM_REWRITE_TAC[MATCH_MP REAL_LT_DIV
        (CONJ (ASSUME `&0 < d`) (ASSUME `&0 < c`))] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `d % x:real^N = c % x'` THEN
      DISCH_THEN(MP_TAC o AP_TERM `(%) (inv c):real^N->real^N`) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_LID; MATCH_MP REAL_MUL_LINV
        (MATCH_MP REAL_LT_IMP_NZ (ASSUME `&0 < c`))] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[real_div; REAL_MUL_SYM]];
    ALL_TAC] THEN
  (* the fan triangulation *)
  MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `q:real^N->bool`] MOI_SSC_FAN_TRIANG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ru" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "sect") (LABEL_TAC "form"))))) THEN
  (* the radial map is injective on the subtended part *)
  SUBGOAL_THEN
   `!z1 z2. z1 IN UNIONS L /\ z2 IN UNIONS L /\
            moi_cmb_radial (UNIONS ff) z1 = moi_cmb_radial (UNIONS ff) z2
            ==> z1 = (z2:real^N)` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z1:real^N`; `z2:real^N`] THEN
    ASM_REWRITE_TAC[IN_INTER; MOI_SSC_CONIC_HULL_UNIONS] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f1:real^N->bool` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f2:real^N->bool` STRIP_ASSUME_TAC))
        ASSUME_TAC)) THEN
    SUBGOAL_THEN `~(z1:real^N = vec 0) /\ ~(z2:real^N = vec 0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `f1:real^N->bool`; `z1:real^N`]
      MOI_SSC_RADIAL_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `f2:real^N->bool`; `z2:real^N`]
      MOI_SSC_RADIAL_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:real^N` (X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `x1:real^N = x2` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`q:real^N->bool`; `z1:real^N`; `z2:real^N`; `c1 / c2`]
      MOI_CMB_RAY_FRONTIER_UNIQUE) THEN
    ASM_REWRITE_TAC[MATCH_MP REAL_LT_DIV
      (CONJ (ASSUME `&0 < c1`) (ASSUME `&0 < c2`))] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < c2` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `c1:real = c2` ASSUME_TAC THENL
     [UNDISCH_TAC `c1 / c2 = &1` THEN UNDISCH_TAC `&0 < c2` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the abstract realization by the radial map *)
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `moi_cmb_radial (UNIONS ff:real^N->bool)`]
    MOI_CMB_RADIAL_REALIZES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "form" ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (moi_cmb_radial (UNIONS ff))
          (relative_frontier q INTER conic hull (UNIONS ff)) = UNIONS ff:real^N->bool`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
      REWRITE_TAC[IN_INTER; MOI_SSC_CONIC_HULL_UNIONS; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "imf" (fun th -> GEN_REWRITE_TAC RAND_CONV
        [GSYM(MATCH_MP th (ASSUME `(f:real^N->bool) IN ff`))]) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^N) IN f` THEN
      USE_THEN "imf" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [GSYM(MATCH_MP th (ASSUME `(f:real^N->bool) IN ff`))]) THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:B) IN IMAGE (g:A->B) s ==> x IN IMAGE g t`) THEN
      MATCH_MP_TAC(SET_RULE `t SUBSET u ==> (s:A->bool) INTER t SUBSET s INTER u`) THEN
      MATCH_MP_TAC HULL_MONO THEN UNDISCH_TAC `(f:real^N->bool) IN ff` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `moi_cmb_radial (UNIONS ff:real^N->bool)`;
                 `moi_real_vertex_sets (L:(real^N->bool)->bool)`]
    ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_REAL_VERTEX_SETS_FINITE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_REAL_VERTEX_SETS_REALIZES THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IMAGE_ID; MATCH_MP MOI_REAL_VERTEX_SETS_UNIONS
      (ASSUME `simplicial_complex (L:(real^N->bool)->bool)`)] THEN
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `h':real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "hs"))))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `h':real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN
  USE_THEN "imf" (fun th -> GEN_REWRITE_TAC RAND_CONV
    [GSYM(MATCH_MP th (ASSUME `(f:real^N->bool) IN ff`))]) THEN
  USE_THEN "sect" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(f:real^N->bool) IN ff`)]) THEN
  REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x:A. x IN s ==> (f:A->B) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `d:real^N->bool = {}` THENL [ASM_REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `d:real^N->bool`] MOI_REAL_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "form" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(d:real^N->bool) IN L`)
    (ASSUME `~(d:real^N->bool = {})`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_TAC `m:real^N`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `d:real^N->bool`)) THEN
  USE_THEN "hs" (MP_TAC o C MATCH_MP (ASSUME
    `(t:real^N->bool) IN moi_real_vertex_sets L`)) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_CMB_LOCAL_PROJ_HULL THEN
  EXISTS_TAC `a:real^N` THEN EXISTS_TAC `t:real^N->bool` THEN
  REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[]);;

(* The cone from a point v over a set, and the transfer with apex v.        *)

let moi_ssc_cone = new_definition
 `moi_ssc_cone (v:real^N) s =
    IMAGE (\x. v + x) (conic hull (IMAGE (\x. --v + x) s))`;;

let MOI_SSC_CONE_EXPLICIT = prove
 (`!(v:real^N) s y.
     y IN moi_ssc_cone v s <=> ?c x. &0 <= c /\ x IN s /\ y = v + c % (x - v)`,
  REWRITE_TAC[moi_ssc_cone; CONIC_HULL_EXPLICIT; IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `--v + x:real^N = x - v`] THEN MESON_TAC[]);;

let MOI_SSC_CONE_TRANSLATE = prove
 (`!(v:real^N) q s.
     IMAGE (\x. --v + x) (relative_frontier q INTER moi_ssc_cone v s) =
     relative_frontier (IMAGE (\x. --v + x) q) INTER
     conic hull (IMAGE (\x. --v + x) s)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[IMAGE_INTER_INJ; VECTOR_ARITH `--v + x:real^N = --v + y <=> x = y`] THEN
  REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION; moi_ssc_cone; GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[VECTOR_ARITH `--v + v + x:real^N = x`; IMAGE_ID]);;

let MOI_SSC_ZERO_IN_TRANSLATE = prove
 (`!(v:real^N) s. vec 0 IN IMAGE (\x. --v + x) s <=> v IN s`,
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `vec 0:real^N = --v + x <=> x = v`] THEN
  MESON_TAC[]);;

let MOI_SSC_RADIAL_TRANSLATE = prove
 (`!(s:real^N->bool) v.
     (!x y. x IN s /\ y IN s /\ y IN segment[v,x] ==> y = x)
     ==> !x y r. x IN IMAGE (\x. --v + x) s /\ y IN IMAGE (\x. --v + x) s /\
                 &0 < r /\ y = r % x ==> y = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ru") THEN REWRITE_TAC[IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `v + r % (x1 - v:real^N) = y1` (LABEL_TAC "eq") THENL
   [UNDISCH_TAC `y:real^N = r % x` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `--v + a:real^N = --v + b <=> a = b`] THEN
  ASM_CASES_TAC `r <= &1` THENL
   [USE_THEN "ru" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `r:real` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      REMOVE_THEN "eq" (SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC];
    CONV_TAC SYM_CONV THEN USE_THEN "ru" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `inv r` THEN
    SUBGOAL_THEN `~(r = &0) /\ &0 < inv r /\ inv r <= &1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      REMOVE_THEN "eq" (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_LINV; ASSUME `~(r = &0)`] THEN VECTOR_ARITH_TAC]]);;

let MOI_SSC_SUBTENDED_POLYHEDRON = prove
 (`!(ff:(real^N->bool)->bool) q.
     FINITE ff /\ (!f. f IN ff ==> polytope f) /\ polytope q
     ==> pl_polyhedron (relative_frontier q INTER conic hull (UNIONS ff))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{conic hull f INTER e | f IN ff /\
                e IN {e:real^N->bool | e face_of q /\ ~(e = q)}}` THEN
  MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `q:real^N->bool`] MOI_SSC_FAN_POLYTOPES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SSC_FAN_UNION THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON]);;

(* Radial transfer with apex v: a finite union of polytopes met at most     *)
(* once by each ray from v is PL homeomorphic to the part of rf q in its    *)
(* cone from v, each member corresponding to its own sector.                *)

let MOI_SSC_RADIAL_TRANSFER = prove
 (`!(ff:(real^N->bool)->bool) q (v:real^N).
     FINITE ff /\ (!f. f IN ff ==> polytope f /\ ~(v IN affine hull f)) /\
     (!x y. x IN UNIONS ff /\ y IN UNIONS ff /\ y IN segment[v,x] ==> y = x) /\
     polytope q /\ v IN relative_interior q /\ UNIONS ff SUBSET affine hull q
     ==> ?h h'. pl_homeomorphism
                  (relative_frontier q INTER moi_ssc_cone v (UNIONS ff),UNIONS ff)
                  (h,h') /\
                !f. f IN ff
                    ==> IMAGE h (relative_frontier q INTER moi_ssc_cone v f) = f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ru") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (\x:real^N. --v + x)) ff`;
                 `IMAGE (\x:real^N. --v + x) q`] MOI_SSC_RADIAL_TRANSFER_0) THEN
  REWRITE_TAC[GSYM IMAGE_UNIONS; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE];
      ASM_SIMP_TAC[POLYTOPE_TRANSLATION_EQ; AFFINE_HULL_TRANSLATION;
                   MOI_SSC_ZERO_IN_TRANSLATE];
      MATCH_MP_TAC MOI_SSC_RADIAL_TRANSLATE THEN USE_THEN "ru" ACCEPT_TAC;
      ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ];
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_TRANSLATION; MOI_SSC_ZERO_IN_TRANSLATE];
      ASM_SIMP_TAC[AFFINE_HULL_TRANSLATION; IMAGE_SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:real^N->real^N` (X_CHOOSE_THEN `h0':real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h0f")))) THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS ff:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `ff:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (relative_frontier (IMAGE (\x:real^N. --v + x) q) INTER
                   conic hull (IMAGE (\x:real^N. --v + x) (UNIONS ff)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNIONS] THEN MATCH_MP_TAC MOI_SSC_SUBTENDED_POLYHEDRON THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; POLYTOPE_TRANSLATION_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier (IMAGE (\x:real^N. --v + x) q) INTER
                  conic hull (IMAGE (\x:real^N. --v + x) (UNIONS ff))`; `--v:real^N`]
    MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^N. v + x)
      (relative_frontier (IMAGE (\x:real^N. --v + x) q) INTER
       conic hull (IMAGE (\x:real^N. --v + x) (UNIONS ff))) =
    relative_frontier q INTER moi_ssc_cone v (UNIONS ff)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN GEN_REWRITE_TAC I [TRANSLATION_GALOIS] THEN
    REWRITE_TAC[MOI_SSC_CONE_TRANSLATE];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`UNIONS ff:real^N->bool`; `v:real^N`]
    MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(\x:real^N. v + x) o h0 o (\x:real^N. --v + x)`;
    `((\x:real^N. v + x) o h0') o (\x:real^N. --v + x)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (\x:real^N. --v + x) (UNIONS ff)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier (IMAGE (\x:real^N. --v + x) q) INTER
                conic hull (IMAGE (\x:real^N. --v + x) (UNIONS ff))` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[IMAGE_o; MOI_SSC_CONE_TRANSLATE] THEN
    USE_THEN "h0f" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(f:real^N->bool) IN ff`)]) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `v + --v + x:real^N = x`; IMAGE_ID]]);;

(* ------------------------------------------------------------------------- *)
(* The star of the vertex in the slab.  The 3-simplices at v, their pieces  *)
(* in the slab, and the far part of the star region (the facets opposite v  *)
(* cut by the slab, and the sections at the two slab planes): the region is *)
(* the cone from v over the far part, which each ray from v meets at most   *)
(* once.                                                                    *)
(* ------------------------------------------------------------------------- *)

let moi_ssc_stars = new_definition
 `moi_ssc_stars (k:(real^3->bool)->bool) (v:real^3) =
    {t | t IN k /\ aff_dim t = &3 /\ v IN t}`;;

let moi_ssc_reg = new_definition
 `moi_ssc_reg (k:(real^3->bool)->bool) (a:real^3) (v:real^3) t1 t2 =
    UNIONS {t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} | t |
            t IN moi_ssc_stars k v}`;;

let moi_ssc_opp = new_definition
 `moi_ssc_opp (k:(real^3->bool)->bool) (v:real^3) t =
    convex hull ({w | {w} IN k /\ w IN t} DELETE v)`;;

let moi_ssc_far = new_definition
 `moi_ssc_far (k:(real^3->bool)->bool) (a:real^3) (v:real^3) t1 t2 =
    {moi_ssc_opp k v t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} | t |
     t IN moi_ssc_stars k v} UNION
    {t INTER {x:real^3 | a dot x = t1} | t | t IN moi_ssc_stars k v} UNION
    {t INTER {x:real^3 | a dot x = t2} | t | t IN moi_ssc_stars k v}`;;

(* The vertices of a 3-simplex at v.                                        *)

let MOI_SSC_STAR_VERTS = prove
 (`!s (a:real^3) lo hi k v t1 t2 t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssc_stars k v
     ==> ?c. FINITE c /\ ~affine_dependent c /\ CARD c = 4 /\ t = convex hull c /\
             v IN c /\ {w | {w} IN k /\ w IN t} = c /\
             (!w. w IN c ==> {w} IN k) /\
             (!w. w IN c /\ ~(w = v) ==> a dot w < t1 \/ t2 < a dot w) /\
             moi_ssc_opp k v t = convex hull (c DELETE v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SIMPLEX_HULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^3->bool` THEN
  SUBGOAL_THEN `CARD (c:real^3->bool) = 4` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim (t:real^3->bool) = &3` THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[INT_ARITH `x - &1:int = &3 <=> x = &4`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN k /\ w IN t ==> w IN c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SSL_VERTEX_IN_HULL THEN
    MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `t:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^3 | {w} IN k /\ w IN t} = c` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
     [ASM_MESON_TAC[];
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        UNDISCH_TAC `t:real^3->bool = convex hull c` THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_ssc_opp] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t1:real`)) (concl th) &&
      can (find_term ((=) `v:real^3`)) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

(* The far family: finitely many polytopes, none with v in its affine hull. *)

let MOI_SSC_FAR_FACTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> FINITE (moi_ssc_far k a v t1 t2) /\
         !f. f IN moi_ssc_far k a v t1 t2 ==> polytope f /\ ~(v IN affine hull f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  SUBGOAL_THEN `FINITE (moi_ssc_stars k (v:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[moi_ssc_stars; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_ssc_far; FINITE_UNION] THEN REPEAT CONJ_TAC THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_ssc_far; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `f:real^3->bool` THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
    (DISJ_CASES_THEN (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN ASM_SIMP_TAC[FINITE_DELETE];
      DISCH_TAC THEN
      UNDISCH_TAC `~affine_dependent (c:real^3->bool)` THEN
      REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v:real^3` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `affine hull (convex hull (c DELETE v:real^3) INTER
                               {x | t1 <= a dot x /\ a dot x <= t2})` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `affine hull (convex hull (c DELETE v:real^3))` THEN
      SIMP_TAC[HULL_MONO; INTER_SUBSET; AFFINE_HULL_CONVEX_HULL; SUBSET_REFL]];
    CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      ASM_SIMP_TAC[POLYTOPE_CONVEX_HULL; POLYHEDRON_HYPERPLANE];
      DISCH_TAC THEN
      SUBGOAL_THEN `affine hull (convex hull c INTER {x:real^3 | a dot x = t1}) SUBSET
                    {x | a dot x = t1}` MP_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[INTER_SUBSET; AFFINE_HYPERPLANE];
        ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      ASM_SIMP_TAC[POLYTOPE_CONVEX_HULL; POLYHEDRON_HYPERPLANE];
      DISCH_TAC THEN
      SUBGOAL_THEN `affine hull (convex hull c INTER {x:real^3 | a dot x = t2}) SUBSET
                    {x | a dot x = t2}` MP_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[INTER_SUBSET; AFFINE_HYPERPLANE];
        ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]]]);;

(* Beyond the facet opposite a vertex v the ray from v leaves the simplex. *)

let MOI_SSC_OPP_EXIT = prove
 (`!c (v:real^N) y l.
     FINITE c /\ ~affine_dependent c /\ v IN c /\ y IN convex hull (c DELETE v) /\
     &1 < l
     ==> ~(v + l % (y - v) IN convex hull c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c DELETE (v:real^N) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(y:real^N) IN convex hull (c DELETE v)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `v + l % (y - v) IN convex hull (c:real^N->bool)` THEN
  SUBGOAL_THEN `c = (v:real^N) INSERT (c DELETE v)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:real`
    (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `~affine_dependent (c:real^N->bool)` THEN
  REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^N) IN affine hull (c DELETE v) /\ b IN affine hull (c DELETE v)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < l - w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v:real^N = (l / (l - w)) % y + (&1 - l / (l - w)) % b`
  (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [SUBGOAL_THEN `(l - w) % v:real^N = l % y - w % b` MP_TAC THENL
     [UNDISCH_TAC `v + l % (y - v):real^N = u % v + w % b` THEN
      SUBGOAL_THEN `u = &1 - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (inv(l - w)):real^N->real^N`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[VECTOR_ARITH `a % y - b % w:real^N = c % y + d % w <=>
                              (a - c) % y = (b + d) % w`] THEN
    SUBGOAL_THEN `inv(l - w) * l - l / (l - w) = &0 /\ inv(l - w) * w + &1 - l / (l - w) = &0`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
    UNDISCH_TAC `&0 < l - w` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* A point of the facet opposite v in one simplex at v that lies in another *)
(* simplex at v lies in the facet opposite v there too.                     *)

let MOI_SSC_OPP_SHARED = prove
 (`!s (a:real^3) lo hi k v t1 t2 t t' y.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\
     t IN moi_ssc_stars k v /\ t' IN moi_ssc_stars k v /\
     y IN moi_ssc_opp k v t /\ y IN t'
     ==> y IN moi_ssc_opp k v t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t':real^3->bool = t` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t':real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(t:real^3->bool) IN moi_ssc_stars k v` THEN
  UNDISCH_TAC `(t':real^3->bool) IN moi_ssc_stars k v` THEN
  REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`;
                 `c:real^3->bool`] MOI_SSB_SIMPLEX_MEET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^3->bool) SUBSET c'` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `{w:real^3 | {w} IN k /\ w IN t'} = c'` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      SUBGOAL_THEN `(z:real^3) IN t INTER t'` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN convex hull w INTER convex hull (c DELETE v)` MP_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `t INTER t' = convex hull (w:real^3->bool)`)) THEN
      REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN moi_ssc_opp k v t` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> x IN s ==> x IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN moi_ssc_opp k v t` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull w INTER convex hull (c DELETE (v:real^3)) =
                convex hull (w INTER (c DELETE v))` SUBST1_TAC THENL
   [MATCH_MP_TAC CONVEX_HULL_INTER THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> x IN s ==> x IN t`) THEN
  MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

(* Ratios of heights.                                                       *)

let MOI_SSC_RATIO = prove
 (`!p q h. (p < h /\ h < q \/ q < h /\ h < p)
           ==> &0 < (h - p) / (q - p) /\ (h - p) / (q - p) < &1 /\
               !w. (p < h ==> p + w * (q - p) <= h) /\ (h < p ==> h <= p + w * (q - p))
                   ==> w <= (h - p) / (q - p)`,
  REPEAT GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `&0 < q - p /\ &0 < h - p` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN ASM_SIMP_TAC[REAL_ARITH `p < h ==> ~(h < p)`] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(h - p) / (q - p) = (p - h) / (p - q)` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `~(q - p = &0) ==> (h - p) / (q - p) = (p - h) / (p - q)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < p - q /\ &0 < p - h` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN ASM_SIMP_TAC[REAL_ARITH `q < h /\ h < p ==> ~(p < h)`] THEN
    REAL_ARITH_TAC]);;

(* A point of a segment from v on the near side of a level lies before the *)
(* crossing point of the segment with the level.                            *)

let MOI_SSC_SEG_CUT = prove
 (`!(a:real^3) v b w h.
     (a dot v < h /\ h < a dot b \/ a dot b < h /\ h < a dot v) /\
     &0 <= w /\ w <= &1 /\
     (a dot v < h ==> a dot (v + w % (b - v)) <= h) /\
     (h < a dot v ==> h <= a dot (v + w % (b - v)))
     ==> ?x. x IN segment[v,b] /\ a dot x = h /\ v + w % (b - v) IN segment[v,x]`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a dot (v:real^3)`; `a dot (b:real^3)`; `h:real`] MOI_SSC_RATIO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `w:real`))) THEN
  ANTS_TAC THENL
   [MP_TAC(ASSUME `(a dot (v:real^3) < h ==> a dot (v + w % (b - v:real^3)) <= h)`) THEN
    MP_TAC(ASSUME `(h < a dot v ==> h <= a dot (v + w % (b - v:real^3)))`) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN CONV_TAC TAUT;
    DISCH_TAC] THEN
  EXISTS_TAC `v + ((h - a dot v) / (a dot b - a dot v)) % (b - v):real^3` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `(h - a dot v) / (a dot b - a dot (v:real^3))` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
    MATCH_MP_TAC(REAL_FIELD
     `~(q - p = &0) ==> p + (h - p) / (q - p) * (q - p) = h`) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `w / ((h - a dot v) / (a dot b - a dot (v:real^3)))` THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH
     `v + w % (b - v):real^3 = (&1 - c) % v + c % (v + m % (b - v)) <=>
      (w - c * m) % (b - v) = vec 0`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_SUB_REFL; VECTOR_MUL_LZERO]]);;

(* The region is star-shaped from v and contains the far part; each of its *)
(* points lies on a segment from v to a far point.                         *)

let MOI_SSC_REG_STAR = prove
 (`!(k:(real^3->bool)->bool) (a:real^3) v t1 t2 x.
     simplicial_complex k /\ t1 <= a dot v /\ a dot v <= t2 /\
     x IN moi_ssc_reg k a v t1 t2
     ==> segment[v,x] SUBSET moi_ssc_reg k a v t1 t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssc_reg; moi_ssc_stars; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `convex (t:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2})` MP_TAC THENL
   [MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | p x /\ q x} = {x | p x} INTER {x | q x}`] THEN
    MATCH_MP_TAC CONVEX_INTER THEN
    REWRITE_TAC[REWRITE_RULE[real_ge] CONVEX_HALFSPACE_GE; CONVEX_HALFSPACE_LE];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `x:real^3`]) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `t:real^3->bool` THEN ASM_SIMP_TAC[]);;

let MOI_SSC_FAR_SUB = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> UNIONS (moi_ssc_far k a v t1 t2) SUBSET moi_ssc_reg k a v t1 t2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  REWRITE_TAC[moi_ssc_far; UNIONS_UNION; UNION_SUBSET; moi_ssc_reg] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN REPEAT CONJ_TAC THEN
  X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE `!a b:(real^3->bool)->bool. s SUBSET a /\ a IN b ==> s SUBSET UNIONS b`) THEN
  EXISTS_TAC `t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}` THEN
  (CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real^3->bool` THEN
                   ASM_REWRITE_TAC[]]) THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET b ==> a INTER c SUBSET b INTER c`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
    SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]]);;

(* Every point of the region lies on a segment from v to a far point.     *)

let MOI_SSC_STAR_CONE = prove
 (`!s (a:real^3) lo hi k v t1 t2 t y.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssc_stars k v /\ y IN t /\
     t1 <= a dot y /\ a dot y <= t2
     ==> ?x. x IN t /\ x IN UNIONS (moi_ssc_far k a v t1 t2) /\ y IN segment[v,x]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c DELETE (v:real^3) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `c = {v:real^3}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `CARD {v:real^3} = 4` THEN REWRITE_TAC[CARD_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN convex hull (v INSERT (c DELETE v))` MP_TAC THENL
   [ASM_SIMP_TAC[INSERT_DELETE] THEN UNDISCH_TAC `(y:real^3) IN t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:real`
    (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `w <= &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `y:real^3`)) THEN
  SUBGOAL_THEN `u = &1 - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[VECTOR_ARITH
    `(&1 - w) % v + w % b:real^3 = v + w % (b - v)`]) THEN
  SUBGOAL_THEN `(b:real^3) IN t /\ v IN t` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `convex hull (c DELETE (v:real^3))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v,b] SUBSET (t:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(b:real^3) IN t` THEN UNDISCH_TAC `(v:real^3) IN t` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CONVEX_CONVEX_HULL; CONVEX_CONTAINS_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ssc_far; UNIONS_UNION; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  ASM_CASES_TAC `t1 <= a dot (b:real^3) /\ a dot b <= t2` THENL
   [EXISTS_TAC `b:real^3` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `t = convex hull (c:real^3->bool)`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
      ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `w:real` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM; REAL_NOT_LE]) THENL
   [MP_TAC(ISPECL [`a:real^3`; `v:real^3`; `b:real^3`; `w:real`; `t1:real`]
      MOI_SSC_SEG_CUT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y = v + w % (b - v:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^3` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `t = convex hull (c:real^3->bool)`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `segment[v,b] SUBSET (t:real^3->bool)` THEN
      UNDISCH_TAC `(x:real^3) IN segment[v,b]` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`a:real^3`; `v:real^3`; `b:real^3`; `w:real`; `t2:real`]
      MOI_SSC_SEG_CUT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y = v + w % (b - v:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^3` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `t = convex hull (c:real^3->bool)`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `segment[v,b] SUBSET (t:real^3->bool)` THEN
      UNDISCH_TAC `(x:real^3) IN segment[v,b]` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[]]);;


let MOI_SSC_REG_CONE = prove
 (`!s (a:real^3) lo hi k v t1 t2 y.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ y IN moi_ssc_reg k a v t1 t2
     ==> ?x. x IN UNIONS (moi_ssc_far k a v t1 t2) /\ y IN segment[v,x]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^3) IN moi_ssc_reg k a v t1 t2` THEN
  REWRITE_TAC[moi_ssc_reg; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`; `y:real^3`] MOI_SSC_STAR_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]);;

(* Each ray from v meets the far part at most once.                        *)

let MOI_SSC_FAR_RADIAL = prove
 (`!s (a:real^3) lo hi k v t1 t2 x y.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\
     x IN UNIONS (moi_ssc_far k a v t1 t2) /\ y IN UNIONS (moi_ssc_far k a v t1 t2) /\
     y IN segment[v,x]
     ==> y = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
    MOI_SSC_FAR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ff")) THEN
  SUBGOAL_THEN `~((v:real^3) IN UNIONS (moi_ssc_far k a v t1 t2))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "ff" (MP_TAC o SPEC `f:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < m /\ m < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_CASES_TAC `m = &0` THENL
       [UNDISCH_TAC `~((v:real^3) IN UNIONS (moi_ssc_far k a v t1 t2))` THEN
        UNDISCH_TAC `(y:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN
        ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                        VECTOR_ADD_RID] THEN MESON_TAC[];
        ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `m = &1` THENL
       [UNDISCH_TAC `~(y:real^3 = x)` THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `y:real^3`)) THEN
  (* x lies in a piece of the region *)
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
    MOI_SSC_FAR_SUB) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_ssc_reg; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `a dot (y:real^3) = (&1 - m) * (a dot v) + m * (a dot x)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 - m) % v + m % x:real^3 = y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `m * (a dot (x:real^3)) <= m * t2 /\ m * t1 <= m * (a dot x) /\
                (&1 - m) * (a dot (v:real^3)) < (&1 - m) * t2 /\
                (&1 - m) * t1 < (&1 - m) * (a dot v)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN
  REWRITE_TAC[moi_ssc_far; UNIONS_UNION; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC)
    (DISJ_CASES_THEN (X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC))) THENL
   [(* y on the facet opposite v of a simplex at v *)
    SUBGOAL_THEN `(t:real^3->bool) IN k` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) IN moi_ssc_stars k v` THEN
      SIMP_TAC[moi_ssc_stars; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN t` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[convex] THEN
      DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `x:real^3`; `&1 - m`; `m:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(t:real^3->bool) IN moi_ssc_stars k v` THEN
          SIMP_TAC[moi_ssc_stars; IN_ELIM_THM];
          ASM_REAL_ARITH_TAC];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t':real^3->bool`; `t:real^3->bool`; `y:real^3`] MOI_SSC_OPP_SHARED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`; `y:real^3`; `inv m`] MOI_SSC_OPP_EXIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN moi_ssc_opp k v t` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `v + inv m % (y - v):real^3 = x` SUBST1_TAC THENL
     [UNDISCH_TAC `(&1 - m) % v + m % x:real^3 = y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[VECTOR_ARITH `((&1 - m) % v + m % x) - v:real^3 = m % (x - v)`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `a dot (y:real^3) = t1` THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `a dot (y:real^3) = t2` THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Planar facts for the section at the level of v.  A PL loop for a PL      *)
(* 1-sphere, a closed connected proper part of a PL loop with two points is *)
(* a PL arc, and a PL 2-cell has no point at which a punctured              *)
(* neighbourhood splits.                                                    *)
(* ------------------------------------------------------------------------- *)

(* A PL 1-sphere is the image of a PL simple loop.                          *)

let MOI_SSC_PL_LOOP = prove
 (`!p:real^N->bool.
     pl_sphere 1 p
     ==> ?g. simple_path g /\ pathfinish g = pathstart g /\
             pl_map_on (interval[vec 0,vec 1]) g /\ path_image g = p`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`; MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `f':real^N->real^N` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `z:real^N`
        STRIP_ASSUME_TAC))) ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `z:real^N`] MOI_PL2_TRIANGLE_POLYGON) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_OF_TRIANGLE] THEN DISCH_TAC THEN
  EXISTS_TAC `(f:real^N->real^N) o polygonal_path[x:real^N;y;z;x]` THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier k,p) (f:real^N->real^N,f')` THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `w:real^N`] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f':real^N->real^N) (f u) = u /\ f' (f w) = w` MP_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `path_image(polygonal_path[x:real^N;y;z;x])` THEN
    ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH] THEN
    REWRITE_TAC[GSYM path_image] THEN ASM_REWRITE_TAC[SUBSET_REFL];
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM_REWRITE_TAC[]]);;

(* A closed connected part of a PL loop that misses a point of the loop and *)
(* has two points is a PL arc.                                             *)

let MOI_SSC_LOOP_ARC = prove
 (`!(g:real^1->real^N) x z p q.
     simple_path g /\ pathfinish g = pathstart g /\
     pl_map_on (interval[vec 0,vec 1]) g /\
     x SUBSET path_image g /\ closed x /\ connected x /\
     z IN path_image g /\ ~(z IN x) /\ p IN x /\ q IN x /\ ~(p = q)
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\ path_image h = x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[path_image; IN_IMAGE] o check (fun th ->
    concl th = `(z:real^N) IN path_image g`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `simple_path (shiftpath t0 g:real^1->real^N) /\
    pl_map_on (interval[vec 0,vec 1]) (shiftpath t0 g) /\
    path_image (shiftpath t0 g) = path_image g /\
    shiftpath t0 g (vec 0) = z /\ shiftpath t0 g (vec 1) = z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t0:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; MOI_PL2_PL_SHIFTPATH; PATH_IMAGE_SHIFTPATH;
                 IN_INTERVAL_1; DROP_VEC] THEN
    MP_TAC(ISPECL [`t0:real^1`; `g:real^1->real^N`] PATHSTART_SHIFTPATH) THEN
    MP_TAC(ISPECL [`t0:real^1`; `g:real^1->real^N`] PATHFINISH_SHIFTPATH) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h0 = shiftpath t0 (g:real^1->real^N)` THEN
  SUBGOAL_THEN `(h0:real^1->real^N) continuous_on interval[vec 0,vec 1]` ASSUME_TAC THENL
   [ASM_MESON_TAC[simple_path; path]; ALL_TAC] THEN
  ABBREV_TAC `aa = {t | t IN interval[vec 0,vec 1] /\ (h0:real^1->real^N) t IN x}` THEN
  SUBGOAL_THEN `compact (aa:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h0:real^1->real^N) aa = x` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN path_image h0` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[path_image; IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. s IN aa /\ t IN aa /\ (h0:real^1->real^N) s = h0 t ==> s = t`
  ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `simple_path (h0:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `t:real^1`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (aa:real^1->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`aa:real^1->bool`; `h0:real^1->real^N`; `x:real^N->bool`]
      HOMEOMORPHISM_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "aa" THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `h1:real^N->real^1`) THEN
    SUBGOAL_THEN `(aa:real^1->bool) homeomorphic (x:real^N->bool)` MP_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_CONNECTEDNESS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `aa:real^1->bool` CONNECTED_COMPACT_INTERVAL_1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real^1` (X_CHOOSE_THEN `be:real^1` ASSUME_TAC)) THEN
  SUBGOAL_THEN `?sp sq. sp IN aa /\ sq IN aa /\ (h0:real^1->real^N) sp = p /\ h0 sq = q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h0:real^1->real^N) aa = x` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:real^1->bool) SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sp:real^1 = sq)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(p:real^N = q)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop al < drop be /\ al IN interval[vec 0,vec 1] /\
                be IN interval[vec 0,vec 1]` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `drop al < drop be` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(sp:real^1 = sq)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `(sp:real^1) IN aa` THEN UNDISCH_TAC `(sq:real^1) IN aa` THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(al:real^1) IN interval[al,be] /\ be IN interval[al,be]` MP_TAC THENL
     [REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(aa:real^1->bool) SUBSET interval[vec 0,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `subpath al be (h0:real^1->real^N)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `al:real^1 = be` (fun th -> UNDISCH_TAC `drop al < drop be` THEN
      REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
    REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_PL2_PL_SUBPATH THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PATH_IMAGE_SUBPATH; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `aa:real^1->bool`)) THEN ASM_REWRITE_TAC[]]);;

(* A point of a PL 2-cell has arbitrarily small neighbourhoods in the cell  *)
(* that stay connected when the point is removed.                           *)

let MOI_SSC_NO_BOWTIE = prove
 (`!(d:real^N->bool) j v u.
     pl_cell_with_boundary 2 d j /\ v IN d /\ open u /\ v IN u
     ==> ?n. v IN n /\ open_in (subtopology euclidean d) n /\ n SUBSET u /\
             connected (n DELETE v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN
    `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `pl_homeomorphism (k,d) (f:real^N->real^N,g)` THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    concl th = `homeomorphism (k,d) (f:real^N->real^N,g)`)) THEN
  SUBGOAL_THEN `(g:real^N->real^N) v IN k /\ f (g v) = v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `k:real^N->bool`; `u:real^N->bool`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^N->real^N) v` o CONJUNCT2 o
    REWRITE_RULE[OPEN_IN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (f:real^N->real^N) (k INTER ball((g:real^N->real^N) v,e))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^N->real^N) v` THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `k:real^N->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL];
    UNDISCH_TAC `ball((g:real^N->real^N) v,e) INTER k SUBSET
                 {x | x IN k /\ (f:real^N->real^N) x IN u}` THEN SET_TAC[];
    SUBGOAL_THEN `IMAGE (f:real^N->real^N) (k INTER ball((g:real^N->real^N) v,e)) DELETE v =
                  IMAGE f ((k INTER ball(g v,e)) DELETE (g v))` SUBST1_TAC THENL
     [MP_TAC(ASSUME `!x:real^N. x IN k ==> (g:real^N->real^N) (f x) = x`) THEN
      MP_TAC(ASSUME `(f:real^N->real^N) (g (v:real^N)) = v`) THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CONNECTED_PUNCTURED_CONVEX THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL] THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
        SUBGOAL_THEN `aff_dim (k INTER ball((g:real^N->real^N) v,e)) = aff_dim k`
        SUBST1_TAC THENL
         [MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
          EXISTS_TAC `(g:real^N->real^N) v` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
          ASM_MESON_TAC[AFF_DIM_SIMPLEX; INT_ARITH `~(&2:int = &1)`]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Near the vertex.  Points of the ball close to v lie in 3-simplices at v; *)
(* the wedge sections are cones from v over their far edges.                *)
(* ------------------------------------------------------------------------- *)

(* Points of the ball close to v lie in 3-simplices at v.                  *)

let MOI_SSC_NEAR_V = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> ?r. &0 < r /\
             !y. y IN s UNION inside s /\ dist(v,y) < r
                 ==> ?t. t IN moi_ssc_stars k v /\ y IN t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`UNIONS {c | c IN k /\ ~((v:real^3) IN c)}`; `v:real^3`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_SSL_SC_SIMPLEX]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?c:real^3->bool. c IN k /\ y IN c /\ v IN c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN s UNION inside s` THEN
    UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_IMP; REAL_NOT_LE] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:(real^3->bool)->bool` MOI_SSL_PURE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^3->bool` THEN
  REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN ASM SET_TAC[]);;

(* Points of a 3-simplex at v lie on segments from v to its opposite facet. *)

let MOI_SSC_STAR_DECOMP = prove
 (`!s (a:real^3) lo hi k v t1 t2 t y.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssc_stars k v /\ y IN t
     ==> ?w b. &0 <= w /\ w <= &1 /\ b IN moi_ssc_opp k v t /\ y = v + w % (b - v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c DELETE (v:real^3) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `c = {v:real^3}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `CARD {v:real^3} = 4` THEN REWRITE_TAC[CARD_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN convex hull (v INSERT (c DELETE v))` MP_TAC THENL
   [ASM_SIMP_TAC[INSERT_DELETE] THEN UNDISCH_TAC `(y:real^3) IN t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:real`
    (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`w:real`; `b:real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u = &1 - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

(* The section of a wedge (a 3-simplex at v whose interior meets the level *)
(* of v) is the cone from v over the section of its opposite facet.        *)

let MOI_SSC_WEDGE_CONE = prove
 (`!s (a:real^3) lo hi k v t1 t2 t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssc_stars k v /\
     ~(interior t INTER {x | a dot x = a dot v} = {})
     ==> ~(moi_ssc_opp k v t INTER {x | a dot x = a dot v} = {}) /\
         t INTER {x | a dot x = a dot v} =
         UNIONS {segment[v,x] | x | x IN moi_ssc_opp k v t INTER {x | a dot x = a dot v}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_ssc_opp k v t SUBSET (t:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (t:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* a point of the level in t other than v gives a point of the opposite facet *)
  SUBGOAL_THEN
   `!y. y IN t /\ a dot y = a dot v /\ ~(y = v)
        ==> ?b. b IN moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v} /\
                y IN segment[v,b]`
  (LABEL_TAC "lev") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`; `y:real^3`] MOI_SSC_STAR_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~(w = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(y:real^3 = v)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    EXISTS_TAC `b:real^3` THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `a dot (y:real^3) = a dot v` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
      REWRITE_TAC[REAL_ARITH `v + w * (b - v) = v <=> w * (b - v) = &0`; REAL_ENTIRE] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v} = {})`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC o
      REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "interior")) (concl th))) THEN
    SUBGOAL_THEN `~(z:real^3 = v)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`t:real^3->bool`; `v:real^3`] EXTREME_POINT_NOT_IN_INTERIOR) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`]
        EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "lev" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `y:real^3 = v` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC o
        REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] o
        check (fun th -> is_neg(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_ssc_opp"))
            (concl th))) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `segment[v:real^3,b]` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `b:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[ENDS_IN_SEGMENT]];
      USE_THEN "lev" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN t`)
        (CONJ (ASSUME `a dot (y:real^3) = a dot v`) (ASSUME `~(y:real^3 = v)`)))) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `segment[v:real^3,b]` THEN CONJ_TAC THENL
       [EXISTS_TAC `b:real^3` THEN ASM_REWRITE_TAC[]; FIRST_ASSUM ACCEPT_TAC]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; SUBSET];
      MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_HYPERPLANE) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]]]);;

(* The far boundary of the wedge sections: the opposite facets cut by the  *)
(* vertex level, over the 3-simplices at v whose interior meets the level. *)

let moi_ssc_lamf = new_definition
 `moi_ssc_lamf (k:(real^3->bool)->bool) (a:real^3) (v:real^3) =
    {moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v} | t |
     t IN moi_ssc_stars k v /\
     ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})}`;;

let moi_ssc_lam = new_definition
 `moi_ssc_lam (k:(real^3->bool)->bool) (a:real^3) (v:real^3) =
    UNIONS (moi_ssc_lamf k a v)`;;

let MOI_SSC_W_CONE = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> UNIONS {t INTER {x:real^3 | a dot x = a dot v} | t |
                 t IN k /\ aff_dim t = &3 /\ v IN t /\
                 ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})} =
         UNIONS {segment[v,x] | x | x IN moi_ssc_lam k a v}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t y. t IN k /\ aff_dim t = &3 /\ v IN t /\
          ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})
          ==> (y IN t INTER {x:real^3 | a dot x = a dot v} <=>
               ?b. b IN moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v} /\
                   y IN segment[v,b])`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSC_WEDGE_CONE) THEN
    ASM_REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; moi_ssc_lam; moi_ssc_lamf; moi_ssc_stars] THEN
  X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  POP_ASSUM MP_TAC THEN MESON_TAC[]);;

let MOI_SSC_LAM_FACTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> FINITE (moi_ssc_lamf k a v) /\
         (!f. f IN moi_ssc_lamf k a v ==> polytope f /\ ~(v IN affine hull f)) /\
         (!x y. x IN moi_ssc_lam k a v /\ y IN moi_ssc_lam k a v /\ y IN segment[v,x]
                ==> y = x) /\
         moi_ssc_lam k a v SUBSET {x:real^3 | a dot x = a dot v} /\
         moi_ssc_lam k a v SUBSET s UNION inside s /\
         compact (moi_ssc_lam k a v) /\ ~(v IN moi_ssc_lam k a v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  SUBGOAL_THEN `FINITE (moi_ssc_stars k (v:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[moi_ssc_stars; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (moi_ssc_lamf k (a:real^3) v)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_ssc_lamf] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `moi_ssc_stars k (v:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* each member lies in a member of the far family, inside its simplex *)
  SUBGOAL_THEN
   `!f. f IN moi_ssc_lamf k a v
        ==> polytope f /\ ~((v:real^3) IN affine hull f) /\
            f SUBSET {x:real^3 | a dot x = a dot v} /\
            f SUBSET s UNION inside s /\
            f SUBSET UNIONS (moi_ssc_far k a v t1 t2)`
  (LABEL_TAC "mem") THENL
   [REWRITE_TAC[moi_ssc_lamf; IN_ELIM_THM] THEN X_GEN_TAC `f:real^3->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_ssc_opp k v t SUBSET (t:real^3->bool)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^3->bool) SUBSET s UNION inside s` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
      UNDISCH_TAC `t IN moi_ssc_stars k (v:real^3)` THEN
      REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      REWRITE_TAC[POLYHEDRON_HYPERPLANE] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN ASM_SIMP_TAC[FINITE_DELETE];
      DISCH_TAC THEN
      UNDISCH_TAC `~affine_dependent (c:real^3->bool)` THEN
      REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v:real^3` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `affine hull (moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v})` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `affine hull (convex hull (c DELETE v:real^3))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[INTER_SUBSET];
        REWRITE_TAC[AFFINE_HULL_CONVEX_HULL; SUBSET_REFL]];
      REWRITE_TAC[INTER_SUBSET];
      ASM SET_TAC[];
      REWRITE_TAC[moi_ssc_far; UNIONS_UNION] THEN
      MATCH_MP_TAC(SET_RULE `!s t u w:real^3->bool. s SUBSET t ==> s SUBSET t UNION u UNION w`) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_ssc_opp k v t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
        GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE `!f s:real^3->bool. s IN f ==> s SUBSET UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (moi_ssc_lamf k a v) SUBSET UNIONS (moi_ssc_far k a v t1 t2) /\
    UNIONS (moi_ssc_lamf k a v) SUBSET {x:real^3 | a dot x = a dot v} /\
    UNIONS (moi_ssc_lamf k a v) SUBSET (s:real^3->bool) UNION inside s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `f:real^3->bool` THEN USE_THEN "mem" (MP_TAC o SPEC `f:real^3->bool`) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ssc_lam] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `f:real^3->bool` THEN USE_THEN "mem" (MP_TAC o SPEC `f:real^3->bool`) THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                         `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
                        MOI_SSC_FAR_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS (moi_ssc_lamf k a v) SUBSET UNIONS (moi_ssc_far k a v t1 t2)` THEN
    UNDISCH_TAC `(x:real^3) IN UNIONS (moi_ssc_lamf k a v)` THEN
    UNDISCH_TAC `(y:real^3) IN UNIONS (moi_ssc_lamf k a v)` THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `f:real^3->bool` THEN USE_THEN "mem" (MP_TAC o SPEC `f:real^3->bool`) THEN
    MESON_TAC[POLYTOPE_IMP_COMPACT];
    REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN X_GEN_TAC `f:real^3->bool` THEN
    USE_THEN "mem" (MP_TAC o SPEC `f:real^3->bool`) THEN
    MESON_TAC[HULL_INC]]);;

(* A ray from a relative interior point meets the relative frontier of a  *)
(* convex set at most once.                                               *)

let MOI_SSC_RAY_RF_UNIQUE = prove
 (`!q (v:real^N) x m.
     convex q /\ v IN relative_interior q /\ x IN relative_frontier q /\
     &0 < m /\ v + m % (x - v) IN relative_frontier q
     ==> m = &1`,
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `m < &1` THENL
   [MP_TAC(ISPECL [`q:real^N->bool`; `&1 - m`; `x:real^N`; `v:real^N`]
      IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (&1 - m) % (x - v) = v + m % (x - v:real^N)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = &1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv m /\ inv m < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV];
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^N->bool`; `&1 - inv m`; `v + m % (x - v):real^N`; `v:real^N`]
      IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(v + m % (x - v)) - (&1 - i) % ((v + m % (x - v)) - v) =
    v + (i * m) % (x - v:real^N)`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `v + &1 % (x - v):real^N = x`] THEN
  ASM_REWRITE_TAC[]);;

(* Small boxes and small planar polygons around a point.                  *)

let MOI_SSC_SMALL_BOX = prove
 (`!(v:real^3) r.
     &0 < r
     ==> ?sx. polytope sx /\ v IN interior sx /\ sx SUBSET ball(v,r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `ball(v:real^3,r)` OPEN_CONTAINS_INTERVAL) THEN
  REWRITE_TAC[OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `interval[p:real^3,q]` THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_CLOSED_INTERVAL]);;

let MOI_SSC_SMALL_Q = prove
 (`!(a:real^3) (v:real^3) r.
     ~(a = vec 0) /\ &0 < r
     ==> ?q. polytope q /\ aff_dim q = &2 /\
             affine hull q = {x | a dot x = a dot v} /\
             v IN relative_interior q /\ q SUBSET ball(v,r) /\
             q SUBSET {x | a dot x = a dot v}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^3`; `r:real`] MOI_SSC_SMALL_BOX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sx:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sx INTER {x:real^3 | a dot x = a dot v}` THEN
  MP_TAC(ISPECL [`sx:real^3->bool`; `a:real^3`; `a dot (v:real^3)`] MOI_SSL_LEVEL_SECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; INTER_SUBSET] THEN
    ASM SET_TAC[]]);;

(* Points of the vertex level of M near v, other than v, lie on segments   *)
(* from v to the far boundary Lambda.                                     *)

let MOI_SSC_NEAR_LAM = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> ?r. &0 < r /\
             !y. y IN s UNION inside s /\ a dot y = a dot v /\ dist(v,y) < r /\
                 ~(y = v)
                 ==> ?b. b IN moi_ssc_lam k a v /\ y IN segment[v,b]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
                MOI_SSC_NEAR_V) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t IN k /\ aff_dim (t:real^3->bool) = &3 /\ v IN t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t IN moi_ssc_stars k (v:real^3)` THEN
    REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSL_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSC_WEDGE_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION] o CONJUNCT2) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_UNIONS] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `b:real^3` THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_ssc_lam; moi_ssc_lamf; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v}` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
      UNDISCH_TAC `(y:real^3) IN u` THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(y:real^3) IN t INTER {x:real^3 | a dot x = a dot v}` MP_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_SING]]]);;

(* Elementary facts on the cone from v.                                   *)

let MOI_SSC_CONE_SCALE = prove
 (`!(v:real^N) s y d.
     y IN moi_ssc_cone v s /\ &0 <= d ==> v + d % (y - v) IN moi_ssc_cone v s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SSC_CONE_EXPLICIT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d * c:real`; `x:real^N`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL] THEN VECTOR_ARITH_TAC);;

let MOI_SSC_SEG_IN_CONE = prove
 (`!(v:real^N) s b y. b IN s /\ y IN segment[v,b] ==> y IN moi_ssc_cone v s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SSC_CONE_EXPLICIT; IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real`; `b:real^N`] THEN ASM_REWRITE_TAC[] THEN
  VECTOR_ARITH_TAC);;

let MOI_SSC_CONE_NEAR = prove
 (`!(v:real^N) s y r.
     y IN moi_ssc_cone v s /\ (!x. x IN s ==> r <= dist(v,x)) /\ dist(v,y) < r
     ==> ?x. x IN s /\ y IN segment[v,x]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SSC_CONE_EXPLICIT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `dist(v:real^N,y) = c * dist(v,x)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[dist; NORM_MUL;
                    VECTOR_ARITH `v - (v + c % (x - v)) = c % (v - x):real^N`] THEN
    ASM_REWRITE_TAC[real_abs];
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&1`; `c:real`; `dist(v:real^N,x)`] REAL_LE_RMUL) THEN
    ANTS_TAC THENL [REWRITE_TAC[DIST_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* The small polygon q around v in the vertex level used for N1.          *)

let MOI_SSC_N1_SETUP = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> ?q. polytope q /\ aff_dim q = &2 /\
             affine hull q = {x | a dot x = a dot v} /\
             v IN relative_interior q /\ q SUBSET {x | a dot x = a dot v} /\
             (v IN inside s ==> q SUBSET inside s) /\
             (!y. y IN q /\ y IN moi_ssc_cone v (moi_ssc_lam k a v)
                  ==> ?x. x IN moi_ssc_lam k a v /\ y IN segment[v,x]) /\
             (!y. y IN q /\ y IN s UNION inside s /\ ~(y = v)
                  ==> ?b. b IN moi_ssc_lam k a v /\ y IN segment[v,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_LAM_FACTS) THEN
  MP_TAC(SPEC_ALL MOI_SSC_NEAR_LAM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  MP_TAC(ISPECL [`moi_ssc_lam k (a:real^3) v`; `v:real^3`] SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  SUBGOAL_THEN `?r3. &0 < r3 /\ (v IN inside s ==> ball(v:real^3,r3) SUBSET inside s)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(v:real^3) IN inside s` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `inside s:real^3->bool` OPEN_CONTAINS_BALL) THEN
      ASM_SIMP_TAC[OPEN_INSIDE] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `&1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `v:real^3`; `min r1 (min r2 r3)`] MOI_SSC_SMALL_Q) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN q ==> dist(v:real^3,y) < r1 /\ dist(v,y) < r2 /\ dist(v,y) < r3 /\
                   a dot y = a dot v`
  (LABEL_TAC "inq") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `q SUBSET ball(v:real^3,min r1 (min r2 r3))` THEN
    UNDISCH_TAC `q SUBSET {x:real^3 | a dot x = a dot v}` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; REAL_LT_MIN] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(v:real^3) IN inside s ==> ball(v,r3) SUBSET inside s` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "inq" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN q`)) THEN SIMP_TAC[];
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_SSC_CONE_NEAR THEN
    EXISTS_TAC `r2:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inq" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN q`)) THEN SIMP_TAC[];
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inq" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN q`)) THEN SIMP_TAC[]]);;

(* N1 when v is an interior point of M: Lambda is a PL circle.           *)

let MOI_SSC_N1_INSIDE = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN inside s
     ==> pl_sphere 1 (moi_ssc_lam k a v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_LAM_FACTS) THEN
  MP_TAC(SPEC_ALL MOI_SSC_N1_SETUP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inm"))))))))) THEN
  SUBGOAL_THEN
   `relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v) =
    relative_frontier (q:real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `!s t:real^3->bool. s INTER t = s <=> s SUBSET t`; SUBSET] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN q /\ ~(y = v)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN relative_frontier q` THEN
      ASM_SIMP_TAC[relative_frontier; IN_DIFF; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "inm" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SSC_SEG_IN_CONE THEN EXISTS_TAC `b:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_ssc_lamf k (a:real^3) v`; `q:real^3->bool`; `v:real^3`]
    MOI_SSC_RADIAL_TRANSFER) THEN
  REWRITE_TAC[GSYM moi_ssc_lam] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (ASSUME_TAC o CONJUNCT1))) THEN
  MP_TAC(ISPECL [`1`; `relative_frontier q:real^3->bool`; `moi_ssc_lam k (a:real^3) v`;
                 `h:real^3->real^3`; `h':real^3->real^3`] MOI_CMB_PL_SPHERE_TRANSFER) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC MOI_SCX_CELL_SPHERE THEN EXISTS_TAC `q:real^3->bool` THEN
  MATCH_MP_TAC MOI_SSL_POLYGON3_CELL THEN ASM_REWRITE_TAC[]);;

let MOI_SSC_CELL_BALL = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> pl_ball n d`,
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

let MOI_SSC_LAM_SEG = prove
 (`!s (a:real^3) lo hi k v t1 t2 x.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ x IN moi_ssc_lam k a v
     ==> segment[v,x] SUBSET (s UNION inside s) INTER {y:real^3 | a dot y = a dot v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SSC_W_CONE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE `!a b:real^3->bool. a = b ==> b SUBSET a`)) THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. b SUBSET c ==> a SUBSET b ==> a SUBSET c`) THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!t m e:real^3->bool. t SUBSET m ==> t INTER e SUBSET m INTER e`) THEN
  UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
  UNDISCH_TAC `(t:real^3->bool) IN k` THEN SET_TAC[]);;

(* Some 3-simplex at v has interior meeting the vertex level.              *)

let MOI_SSC_WEDGE_EXISTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> ?t. t IN moi_ssc_stars k v /\
             ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `a dot (v:real^3)` (last (CONJUNCTS (MATCH_MP MOI_SSL_SLAB_FACTS
    (ASSUME `moi_ssl_slab_hyp s (a:real^3) lo hi k v t1 t2`))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`;
                 `(s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`;
                 `s INTER {x:real^3 | a dot x = a dot v}`] MOI_SSL_PLANE_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; STRIP_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) limit_point_of
                ((s UNION inside s) INTER {x:real^3 | a dot x = a dot v})`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SSL_PL_BALL_CONNECTED THEN EXISTS_TAC `2` THEN
      MATCH_MP_TAC MOI_SSC_CELL_BALL THEN
      EXISTS_TAC `s INTER {x:real^3 | a dot x = a dot v}` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `b:real^3`) THEN
      UNDISCH_TAC `affine hull ((s UNION inside s) INTER {x:real^3 | a dot x = a dot v}) =
                   {x | a dot x = a dot v}` THEN
      ASM_REWRITE_TAC[AFFINE_HULL_SING] THEN
      DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
      ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; AFF_DIM_SING; DIMINDEX_3] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL MOI_SSC_NEAR_V) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nv"))) THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "nv" (MP_TAC o SPEC `y:real^3`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t IN k /\ aff_dim (t:real^3->bool) = &3 /\ v IN t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t IN moi_ssc_stars k (v:real^3)` THEN
    REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSL_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN t INTER {x:real^3 | a dot x = a dot v}` MP_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_SING]]);;

(* Lambda has two distinct points.                                         *)

let MOI_SSC_LAM_TWO = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> ?b1 b2. b1 IN moi_ssc_lam k a v /\ b2 IN moi_ssc_lam k a v /\ ~(b1 = b2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SSC_WEDGE_EXISTS) THEN
  SUBGOAL_THEN `polytope (t:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSC_WEDGE_CONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `b1:real^3` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) ASSUME_TAC) THEN
  SUBGOAL_THEN
   `moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v} SUBSET moi_ssc_lam k a v`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ssc_lam; moi_ssc_lamf] THEN
    MATCH_MP_TAC(SET_RULE `!f s:real^3->bool. s IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?b2. b2 IN moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v} /\ ~(b2 = b1)`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `b2:real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`b1:real^3`; `b2:real^3`] THEN
    UNDISCH_TAC `moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v} SUBSET
                 moi_ssc_lam k a v` THEN
    UNDISCH_TAC `(b1:real^3) IN moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v}` THEN
    UNDISCH_TAC `(b2:real^3) IN moi_ssc_opp k v t INTER {x:real^3 | a dot x = a dot v}` THEN
    UNDISCH_TAC `~(b2:real^3 = b1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `F` CONTR_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `t INTER {x:real^3 | a dot x = a dot v} SUBSET segment[v,b1]` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x:real^3 = b1` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `a:real^3`; `a dot (v:real^3)`]
    MOI_SSL_LEVEL_SECTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  COND_CASES_TAC THEN INT_ARITH_TAC);;

(* The small polygon properties, packaged.                                 *)

let moi_ssc_qok = new_definition
 `moi_ssc_qok (s:real^3->bool) (a:real^3) (k:(real^3->bool)->bool) (v:real^3) q <=>
    polytope q /\ aff_dim q = &2 /\
    affine hull q = {x | a dot x = a dot v} /\
    v IN relative_interior q /\ q SUBSET {x | a dot x = a dot v} /\
    (v IN inside s ==> q SUBSET inside s) /\
    (!y. y IN q /\ y IN moi_ssc_cone v (moi_ssc_lam k a v)
         ==> ?x. x IN moi_ssc_lam k a v /\ y IN segment[v,x]) /\
    (!y. y IN q /\ y IN s UNION inside s /\ ~(y = v)
         ==> ?b. b IN moi_ssc_lam k a v /\ y IN segment[v,b])`;;

let MOI_SSC_QOK_EXISTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 ==> ?q. moi_ssc_qok s a k v q`,
  REWRITE_TAC[moi_ssc_qok] THEN MATCH_ACCEPT_TAC MOI_SSC_N1_SETUP);;

let MOI_SSC_RF_FACTS = prove
 (`!q (v:real^N) y.
     polytope q /\ v IN relative_interior q /\ y IN relative_frontier q
     ==> y IN q /\ ~(y = v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN relative_frontier q` THEN
  ASM_SIMP_TAC[relative_frontier; IN_DIFF; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_MESON_TAC[]);;

(* The radial retraction of the punctured affine hull onto the relative   *)
(* frontier (library-style form of the deformation retract lemma).        *)

let MOI_SSC_RADIAL_RETRACT = prove
 (`!q (v:real^N).
     polytope q /\ v IN relative_interior q
     ==> ?r. r continuous_on (affine hull q DELETE v) /\
             !y. y IN affine hull q DELETE v
                 ==> r y IN relative_frontier q /\
                     ?c. &0 < c /\ r y = v + c % (y - v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^N->bool`; `affine hull q:real^N->bool`; `v:real^N`]
    RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED; AFFINE_IMP_CONVEX;
                 AFFINE_AFFINE_HULL; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `q:real^N->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED; SUBSET_DIFF];
    ALL_TAC] THEN
  REWRITE_TAC[retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (r:real^N->real^N) (affine hull q DELETE v) SUBSET
                 relative_frontier q` THEN
    UNDISCH_TAC `(y:real^N) IN affine hull q DELETE v` THEN SET_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC o SPEC `y:real^N`) THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(r:real^N->real^N) y - v = c % (y - v)` THEN VECTOR_ARITH_TAC]);;

let MOI_SSC_QOK_BASIC = prove
 (`!s (a:real^3) k v q.
     moi_ssc_qok s a k v q
     ==> polytope q /\ aff_dim q = &2 /\
         affine hull q = {x | a dot x = a dot v} /\
         v IN relative_interior q /\ q SUBSET {x | a dot x = a dot v} /\
         (v IN inside s ==> q SUBSET inside s)`,
  SIMP_TAC[moi_ssc_qok]);;

let MOI_SSC_QOK_CONE = prove
 (`!s (a:real^3) k v q y.
     moi_ssc_qok s a k v q /\ y IN q /\ y IN moi_ssc_cone v (moi_ssc_lam k a v)
     ==> ?x. x IN moi_ssc_lam k a v /\ y IN segment[v,x]`,
  REWRITE_TAC[moi_ssc_qok] THEN MESON_TAC[]);;

let MOI_SSC_QOK_M = prove
 (`!s (a:real^3) k v q y.
     moi_ssc_qok s a k v q /\ y IN q /\ y IN s UNION inside s /\ ~(y = v)
     ==> ?b. b IN moi_ssc_lam k a v /\ y IN segment[v,b]`,
  REWRITE_TAC[moi_ssc_qok] THEN MESON_TAC[]);;

(* E1 = rf q INTER cone is the part of rf q in the level section D of M.  *)

let MOI_SSC_E1_EQ = prove
 (`!s (a:real^3) lo hi k v t1 t2 q.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ moi_ssc_qok s a k v q
     ==> relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v) =
         relative_frontier q INTER
         ((s UNION inside s) INTER {x:real^3 | a dot x = a dot v})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_QOK_BASIC) THEN
  REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
  ASM_CASES_TAC `(y:real^3) IN relative_frontier q` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `v:real^3`; `y:real^3`] MOI_SSC_RF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `k:(real^3->bool)->bool`; `v:real^3`;
                   `q:real^3->bool`; `y:real^3`] MOI_SSC_QOK_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `x:real^3`] MOI_SSC_LAM_SEG) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN MESON_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `k:(real^3->bool)->bool`; `v:real^3`;
                   `q:real^3->bool`; `y:real^3`] MOI_SSC_QOK_M) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SSC_SEG_IN_CONE THEN EXISTS_TAC `b:real^3` THEN
    ASM_REWRITE_TAC[]]);;

(* E1 is connected: it is the radial image of a connected punctured       *)
(* neighbourhood of v in D (no-bowtie lemma).                             *)

let MOI_SSC_E1_CONN = prove
 (`!s (a:real^3) lo hi k v t1 t2 q.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ moi_ssc_qok s a k v q
     ==> connected (relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `a dot (v:real^3)` (last (CONJUNCTS (MATCH_MP MOI_SSL_SLAB_FACTS
    (ASSUME `moi_ssl_slab_hyp s (a:real^3) lo hi k v t1 t2`))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_QOK_BASIC) THEN
  SUBGOAL_THEN `(v:real^3) IN q` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL MOI_SSC_NEAR_LAM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  MP_TAC(ISPECL [`(s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`;
                 `s INTER {x:real^3 | a dot x = a dot v}`; `v:real^3`;
                 `ball(v:real^3,r1)`] MOI_SSC_NO_BOWTIE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `n SUBSET (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP OPEN_IN_IMP_SUBSET); ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `v:real^3`] MOI_SSC_RADIAL_RETRACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ret"))) THEN
  SUBGOAL_THEN
   `relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v) =
    IMAGE (r:real^3->real^3) (n DELETE v)`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `affine hull q DELETE (v:real^3)` THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `n SUBSET (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
        UNDISCH_TAC `affine hull q = {x:real^3 | a dot x = a dot v}` THEN SET_TAC[]];
      FIRST_ASSUM ACCEPT_TAC]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [(* each point of E1 is the image of a point of n near v *)
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_DELETE] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`q:real^3->bool`; `v:real^3`; `x:real^3`] MOI_SSC_RF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `open_in (subtopology euclidean
                   ((s UNION inside s) INTER {x:real^3 | a dot x = a dot v})) n` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(v:real^3) IN u` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:real^3) IN n` THEN
      UNDISCH_TAC `n = ((s UNION inside s) INTER {x:real^3 | a dot x = a dot v}) INTER u` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `u:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < norm(x - v:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `?d. &0 < d /\ d <= &1 /\ d * norm(x - v:real^3) < e`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `min (&1) (e / (&2 * norm(x - v:real^3)))` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `e / (&2 * norm(x - v:real^3)) * norm(x - v)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> e / (&2 * n) * n = e / &2`] THEN
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `v + d % (x - v) IN segment[v:real^3,x]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `d:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `v + d % (x - v) IN (q:real^3->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `q:real^3->bool` CONVEX_CONTAINS_SEGMENT) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
      DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `x:real^3`]) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `v + d % (x - v) IN segment[v:real^3,x]` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `v + d % (x - v) IN moi_ssc_cone v (moi_ssc_lam k (a:real^3) v)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SSC_CONE_SCALE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `v + d % (x - v) IN
                  (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `k:(real^3->bool)->bool`; `v:real^3`;
                     `q:real^3->bool`; `v + d % (x - v):real^3`] MOI_SSC_QOK_CONE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `x':real^3`] MOI_SSC_LAM_SEG) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `v + d % (x - v) IN segment[v:real^3,x']` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(v + d % (x - v):real^3 = v)` ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `v + d % (x - v):real^3 = v <=> d % (x - v) = vec 0`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_SUB_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `v + d % (x - v) IN (n:real^3->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `v + d % (x - v) IN (u:real^3->bool)` MP_TAC THENL
       [UNDISCH_TAC `ball(v:real^3,e) SUBSET u` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[dist; VECTOR_ARITH `v - (v + d % (x - v)):real^3 = --(d % (x - v))`;
                    NORM_NEG; NORM_MUL] THEN
        ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE];
        UNDISCH_TAC `v + d % (x - v) IN
                     (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
        UNDISCH_TAC `n = ((s UNION inside s) INTER {x:real^3 | a dot x = a dot v}) INTER u` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    USE_THEN "ret" (MP_TAC o SPEC `v + d % (x - v):real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `q:real^3->bool` THEN REWRITE_TAC[HULL_SUBSET] THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `c * d = &1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`q:real^3->bool`; `v:real^3`; `x:real^3`; `c * d:real`]
        MOI_SSC_RAY_RF_UNIQUE) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; REAL_LT_MUL] THEN
      UNDISCH_TAC `(r:real^3->real^3) (v + d % (x - v)) IN relative_frontier q` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH
        `v + c % ((v + d % (x - v)) - v):real^3 = v + (c * d) % (x - v)`] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `v + d % (x - v):real^3` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ARITH
        `v + c % ((v + d % (x - v)) - v):real^3 = v + (c * d) % (x - v)`] THEN
      VECTOR_ARITH_TAC;
      UNDISCH_TAC `v + d % (x - v) IN (n:real^3->bool)` THEN
      UNDISCH_TAC `n = ((s UNION inside s) INTER {x:real^3 | a dot x = a dot v}) INTER u` THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    (* the image of the punctured neighbourhood lies in E1 *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_INTER] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN (s UNION inside s) INTER {x:real^3 | a dot x = a dot v} /\
                  dist(v,y) < r1`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `n SUBSET (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
      UNDISCH_TAC `n SUBSET ball(v:real^3,r1)` THEN UNDISCH_TAC `(y:real^3) IN n` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "ret" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
        UNDISCH_TAC `affine hull q = {x:real^3 | a dot x = a dot v}` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SSC_CONE_SCALE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    USE_THEN "near" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SSC_SEG_IN_CONE THEN EXISTS_TAC `b:real^3` THEN
    ASM_REWRITE_TAC[]]);;

(* For a boundary vertex E1 is not all of rf q: otherwise q lies in D and  *)
(* v would be a relative interior point of the 2-cell D.                   *)

let MOI_SSC_E1_PROPER = prove
 (`!s (a:real^3) lo hi k v t1 t2 q.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ moi_ssc_qok s a k v q /\ v IN s
     ==> ?z. z IN relative_frontier q /\
             ~(z IN relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `a dot (v:real^3)` (last (CONJUNCTS (MATCH_MP MOI_SSL_SLAB_FACTS
    (ASSUME `moi_ssl_slab_hyp s (a:real^3) lo hi k v t1 t2`))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_QOK_BASIC) THEN
  MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`;
                 `(s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`;
                 `s INTER {x:real^3 | a dot x = a dot v}`] MOI_SSL_PLANE_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; STRIP_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN
  ASM_CASES_TAC `!z:real^3. z IN relative_frontier q
                            ==> z IN moi_ssc_cone v (moi_ssc_lam k a v)` THENL
   [FIRST_X_ASSUM(LABEL_TAC "all") THEN SUBGOAL_THEN `F` CONTR_TAC;
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN MESON_TAC[]] THEN
  SUBGOAL_THEN `q SUBSET (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`q:real^3->bool`; `v:real^3`] MOI_SSC_RADIAL_RETRACT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ret"))) THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:real^3 = v` THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    USE_THEN "ret" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `q:real^3->bool` THEN REWRITE_TAC[HULL_SUBSET] THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN moi_ssc_cone v (moi_ssc_lam k a v)` ASSUME_TAC THENL
     [SUBGOAL_THEN `v + inv c % ((r:real^3->real^3) y - v) = y`
        (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
       [ASM_REWRITE_TAC[VECTOR_ADD_SUB; VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_SSC_CONE_SCALE THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      USE_THEN "all" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `k:(real^3->bool)->bool`; `v:real^3`;
                   `q:real^3->bool`; `y:real^3`] MOI_SSC_QOK_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `x':real^3`] MOI_SSC_LAM_SEG) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN segment[v,x']` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3->bool`;
                 `(s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`]
    SUBSET_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INTER; IN_ELIM_THM]);;

(* N1 for a boundary vertex: Lambda is a PL arc.                           *)

let MOI_SSC_N1_BOUNDARY = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN s
     ==> ?bb. arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\
              path_image bb = moi_ssc_lam k a v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_LAM_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `q:real^3->bool` o MATCH_MP MOI_SSC_QOK_EXISTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_QOK_BASIC) THEN
  MP_TAC(ISPECL [`moi_ssc_lamf k (a:real^3) v`; `q:real^3->bool`; `v:real^3`]
    MOI_SSC_RADIAL_TRANSFER) THEN
  REWRITE_TAC[GSYM moi_ssc_lam] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (MP_TAC o CONJUNCT1))) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "hh") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hh'")
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `closed (relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k (a:real^3) v))`
  ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL MOI_SSC_E1_EQ) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_RELATIVE_FRONTIER] THEN
    MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[CLOSED_HYPERPLANE];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL MOI_SSC_E1_CONN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL MOI_SSC_E1_PROPER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b1:real^3` (X_CHOOSE_THEN `b2:real^3` STRIP_ASSUME_TAC) o
    MATCH_MP MOI_SSC_LAM_TWO) THEN
  SUBGOAL_THEN
   `!b. b IN moi_ssc_lam k a v
        ==> (h':real^3->real^3) b IN
            relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (h':real^3->real^3) (moi_ssc_lam k a v) =
                 relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v)` THEN
    UNDISCH_TAC `(b:real^3) IN moi_ssc_lam k a v` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h':real^3->real^3) b1 = h' b2)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `h:real^3->real^3`) THEN
    USE_THEN "hh'" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(b1:real^3) IN moi_ssc_lam k a v`);
                                         MATCH_MP th (ASSUME `(b2:real^3) IN moi_ssc_lam k a v`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `relative_frontier q:real^3->bool` MOI_SSC_PL_LOOP) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_SCX_CELL_SPHERE THEN EXISTS_TAC `q:real^3->bool` THEN
    MATCH_MP_TAC MOI_SSL_POLYGON3_CELL THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`g:real^1->real^3`;
                 `relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k (a:real^3) v)`;
                 `z:real^3`; `(h':real^3->real^3) b1`; `(h':real^3->real^3) b2`]
    MOI_SSC_LOOP_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `h0:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `(h:real^3->real^3) o (h0:real^1->real^3)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "hh" (fun th -> MP_TAC(CONJ
      (MATCH_MP th (ASSUME `(x:real^3) IN
         relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v)`))
      (MATCH_MP th (ASSUME `(y:real^3) IN
         relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k a v)`)))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `relative_frontier q INTER moi_ssc_cone v (moi_ssc_lam k (a:real^3) v)` THEN
    ASM_REWRITE_TAC[GSYM path_image; SUBSET_REFL];
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE]]);;

let MOI_SSC_BALL_CELL = prove
 (`!n (d:real^N->bool). pl_ball n d ==> ?j. pl_cell_with_boundary n d j`,
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

(* N1: the wedge sections at the vertex level form a PL 2-cell.           *)

let MOI_SSC_N1 = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> ?j0:real^3->bool.
            pl_cell_with_boundary 2
              (UNIONS {t INTER {x:real^3 | a dot x = a dot v} | t |
                       t IN k /\ aff_dim t = &3 /\ v IN t /\
                       ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})})
              j0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_SSC_W_CONE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_LAM_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  UNDISCH_TAC `(v:real^3) IN s UNION inside s` THEN REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THENL
   [MP_TAC(SPEC_ALL MOI_SSC_N1_BOUNDARY) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `bb:real^1->real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`bb:real^1->real^3`; `v:real^3`] MOI_SGL_CONE_ARC) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MP_TAC(SPEC_ALL MOI_SSC_N1_INSIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`1`; `moi_ssc_lam k (a:real^3) v`; `v:real^3`] PL_BALL_CONE) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_SSC_BALL_CELL) THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The frontier of the star region; the interior-vertex case.               *)
(* ------------------------------------------------------------------------- *)

let MOI_SSC_REG_EQ = prove
 (`!(k:(real^3->bool)->bool) (a:real^3) v t1 t2.
     UNIONS {t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} | t |
             t IN k /\ aff_dim t = &3 /\ v IN t} =
     moi_ssc_reg k a v t1 t2`,
  REWRITE_TAC[moi_ssc_reg; moi_ssc_stars; IN_ELIM_THM]);;

(* A face of a star simplex missing v lies in the opposite facet.          *)

let MOI_SSC_FACE_OPP = prove
 (`!s (a:real^3) lo hi k v t1 t2 t f.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssc_stars k v /\
     f face_of t /\ ~(v IN f)
     ==> f SUBSET moi_ssc_opp k v t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(f:real^3->bool) face_of t` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~((v:real^3) IN f)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HULL_MONO THEN
  UNDISCH_TAC `~((v:real^3) IN convex hull c')` THEN
  UNDISCH_TAC `c' SUBSET (c:real^3->bool)` THEN
  MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `c':real^3->bool`] HULL_SUBSET) THEN
  SET_TAC[]);;

let MOI_SSC_REG_FACTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> compact (moi_ssc_reg k a v t1 t2) /\
         moi_ssc_reg k a v t1 t2 SUBSET s UNION inside s /\
         v IN moi_ssc_reg k a v t1 t2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  SUBGOAL_THEN `FINITE (moi_ssc_stars k (v:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[moi_ssc_stars; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_ssc_reg] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^3->bool` THEN
    REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SET_RULE `{x:real^3 | p x /\ q x} = {x | p x} INTER {x | q x}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN
      REWRITE_TAC[REWRITE_RULE[real_ge] CLOSED_HALFSPACE_GE; CLOSED_HALFSPACE_LE]];
    REWRITE_TAC[moi_ssc_reg; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `t:real^3->bool` THEN REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN
    STRIP_TAC THEN UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
    UNDISCH_TAC `(t:real^3->bool) IN k` THEN SET_TAC[];
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
      MOI_SSC_WEDGE_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[moi_ssc_reg; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `t IN moi_ssc_stars k (v:real^3)` THEN
      REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC]]);;

(* A point of an opposite facet inside M lies in a 3-simplex without v.   *)

let MOI_SSC_OPP_OTHER = prove
 (`!s (a:real^3) lo hi k v t1 t2 t x.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssc_stars k v /\
     x IN moi_ssc_opp k v t /\ x IN inside s
     ==> ?t'. t' IN k /\ aff_dim t' = &3 /\ x IN t' /\ ~(v IN t')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  SUBGOAL_THEN `~(x:real^3 = v)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(v:real^3) IN moi_ssc_opp k v t` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~affine_dependent (c:real^3->bool)` THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `convex hull (c DELETE (v:real^3))` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `x:real^3`] MOI_SSL_LOCAL_TETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN inside s` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lt"))) THEN
  MP_TAC(ISPEC `inside s:real^3->bool` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INSIDE] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(x - v:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ d * norm(x - v:real^3) < r0 /\ d * norm(x - v) < r1`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min r0 r1 / (&2 * norm(x - v:real^3))` THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> m / (&2 * n) * n = m / &2`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(x:real^3,v + (&1 + d) % (x - v)) = d * norm(x - v)` ASSUME_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH
      `x - (v + (&1 + d) % (x - v)):real^3 = --(d % (x - v))`; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `v + (&1 + d) % (x - v) IN inside (s:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(x:real^3,r1) SUBSET inside s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "lt" (MP_TAC o SPEC `v + (&1 + d) % (x - v):real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t':real^3->bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t' IN moi_ssc_stars k (v:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`; `t':real^3->bool`; `x:real^3`] MOI_SSC_OPP_SHARED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t':real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^3) IN moi_ssc_opp k v t'` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`; `x:real^3`; `&1 + d`] MOI_SSC_OPP_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `v + (&1 + d) % (x - v) IN (t':real^3->bool)` THEN
  ASM_REWRITE_TAC[]);;

(* The far part lies in the frontier of the star region.                   *)

let MOI_SSC_FAR_FRONTIER = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> UNIONS (moi_ssc_far k a v t1 t2) SUBSET frontier (moi_ssc_reg k a v t1 t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_REG_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SSC_FAR_SUB) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN moi_ssc_reg k a v t1 t2` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS (moi_ssc_far k a v t1 t2) SUBSET moi_ssc_reg k (a:real^3) v t1 t2` THEN
    UNDISCH_TAC `(x:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `a:real^3`; `t1:real`;
                 `t2:real`; `moi_ssc_stars k (v:real^3)`; `x:real^3`] MOI_SSL_FR_CRIT) THEN
  REWRITE_TAC[GSYM moi_ssc_reg] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_ssc_stars; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^3) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:real^3) dot x = t1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:real^3) dot x = t2` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN
  REWRITE_TAC[moi_ssc_far; UNIONS_UNION] THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`; `x:real^3`] MOI_SSC_OPP_OTHER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_ssc_reg k a v t1 t2 SUBSET (s:real^3->bool) UNION inside s` THEN
    UNDISCH_TAC `(x:real^3) IN moi_ssc_reg k a v t1 t2` THEN
    UNDISCH_TAC `~((x:real^3) IN s)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t':real^3->bool` THEN ASM_REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM]);;

(* Off the far part, frontier points of the star region lie on s.          *)

let MOI_SSC_FRONTIER_FAR = prove
 (`!s (a:real^3) lo hi k v t1 t2 x.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\
     x IN frontier (moi_ssc_reg k a v t1 t2) /\
     ~(x IN UNIONS (moi_ssc_far k a v t1 t2))
     ==> x IN s /\ x IN moi_ssc_reg k a v t1 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_REG_FACTS) THEN
  SUBGOAL_THEN `(x:real^3) IN moi_ssc_reg k a v t1 t2` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN frontier (moi_ssc_reg k a v t1 t2)` THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `(x:real^3) IN frontier (moi_ssc_reg k a v t1 t2)` THEN
  REWRITE_TAC[frontier; IN_DIFF] THEN
  MATCH_MP_TAC(TAUT `q ==> ~(p /\ ~q)`) THEN
  MP_TAC(ASSUME `(x:real^3) IN moi_ssc_reg k a v t1 t2`) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [moi_ssc_reg] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t1 < (a:real^3) dot x /\ a dot x < t2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^3) IN UNIONS (moi_ssc_far k a v t1 t2))` THEN
    REWRITE_TAC[] THEN
    REWRITE_TAC[moi_ssc_far; UNIONS_UNION] THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
    DISJ2_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `a:real^3`; `t1:real`;
                 `t2:real`; `moi_ssc_stars k (v:real^3)`; `x:real^3`] MOI_SSL_INT_CRIT) THEN
  REWRITE_TAC[GSYM moi_ssc_reg] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_ssc_stars; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    UNDISCH_TAC `moi_ssc_reg k a v t1 t2 SUBSET (s:real^3->bool) UNION inside s` THEN
    UNDISCH_TAC `(x:real^3) IN moi_ssc_reg k a v t1 t2` THEN
    UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t':real^3->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^3->bool) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `t IN moi_ssc_stars k (v:real^3)` THEN
    SIMP_TAC[moi_ssc_stars; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`]
    MOI_SSL_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`; `t INTER t':real^3->bool`] MOI_SSC_FACE_OPP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_TAC] THEN
  UNDISCH_TAC `~((x:real^3) IN UNIONS (moi_ssc_far k a v t1 t2))` THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[moi_ssc_far; UNIONS_UNION] THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
  DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t INTER t' SUBSET moi_ssc_opp k (v:real^3) t` THEN
  UNDISCH_TAC `(x:real^3) IN t'` THEN UNDISCH_TAC `(x:real^3) IN t` THEN SET_TAC[]);;

(* Rays from an interior point v of the star region meet the far part     *)
(* exactly once.                                                          *)

let MOI_SSC_RAY_HITS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN interior (moi_ssc_reg k a v t1 t2)
     ==> !u. ~(u = vec 0)
             ==> ?!r. &0 < r /\ v + r % u IN UNIONS (moi_ssc_far k a v t1 t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(v:real^3) IN interior (moi_ssc_reg k a v t1 t2)` THEN
    REWRITE_TAC[IN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < norm(u:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `?c. &0 < c /\ c * norm(u:real^3) < e` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `e / (&2 * norm(u:real^3))` THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> e / (&2 * n) * n = e / &2`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `v + c % u IN moi_ssc_reg k (a:real^3) v t1 t2` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(v:real^3,e) SUBSET moi_ssc_reg k a v t1 t2` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[dist; VECTOR_ARITH `v - (v + c % u):real^3 = --(c % u)`;
                  NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `v + c % u:real^3`] MOI_SSC_REG_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(m = &0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `v + c % u = (&1 - &0) % v + &0 % (x:real^3)` THEN
      REWRITE_TAC[VECTOR_ARITH `v + c % u = (&1 - &0) % v + &0 % x:real^3 <=>
                                c % u = vec 0`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    EXISTS_TAC `c / m` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `v + (c / m) % u:real^3 = x` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `m % (x - v) = c % (u:real^3)` MP_TAC THENL
     [UNDISCH_TAC `v + c % u = (&1 - m) % v + m % (x:real^3)` THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (inv m):real^3->real^3`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV] THEN
    REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`r1:real`; `r2:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!p q. &0 < p /\ p <= q /\
            v + p % u IN UNIONS (moi_ssc_far k a v t1 t2) /\
            v + q % u IN UNIONS (moi_ssc_far k (a:real^3) v t1 t2)
            ==> p = q`
    (fun th -> ASM_MESON_TAC[th; REAL_LE_TOTAL; REAL_LT_IMP_LE; REAL_LTE_TRANS]) THEN
    MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `v + q % u:real^3`; `v + p % u:real^3`] MOI_SSC_FAR_RADIAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `p / q` THEN
      SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      REWRITE_TAC[VECTOR_ARITH
       `v + p % u:real^3 = (&1 - r) % v + r % (v + q % u) <=> p % u = (r * q) % u`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      REWRITE_TAC[VECTOR_ARITH `v + p % u:real^3 = v + q % u <=> (p - q) % u = vec 0`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN REAL_ARITH_TAC]]);;

(* Interior vertex: the frontier of the star region is the far part.        *)

let MOI_SSC_INT_FRONTIER = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN inside s
     ==> frontier (moi_ssc_reg k a v t1 t2) = UNIONS (moi_ssc_far k a v t1 t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_SSC_FAR_FRONTIER)] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `x:real^3`] MOI_SSC_FRONTIER_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ASSUME `(x:real^3) IN moi_ssc_reg k a v t1 t2`) THEN
  REWRITE_TAC[moi_ssc_reg; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^3->bool) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `t IN moi_ssc_stars k (v:real^3)` THEN
    SIMP_TAC[moi_ssc_stars; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `x:real^3`] MOI_SSL_CARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "car")))) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `c:real^3->bool`;
                 `x:real^3`] MOI_SSL_SPHERE_SIMPLICES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "car" (MP_TAC o SPEC `t:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~((v:real^3) IN c)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `inside s INTER (s:real^3->bool) = {}` THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET s` THEN
    UNDISCH_TAC `(v:real^3) IN c` THEN UNDISCH_TAC `(v:real^3) IN inside s` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`; `c:real^3->bool`] MOI_SSC_FACE_OPP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `~((x:real^3) IN UNIONS (moi_ssc_far k a v t1 t2))` THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[moi_ssc_far; UNIONS_UNION] THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
  DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `c:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `(x:real^3) IN relative_interior c` THEN
  UNDISCH_TAC `c SUBSET moi_ssc_opp k (v:real^3) t` THEN SET_TAC[]);;

(* The interior-vertex case of the star statement.                          *)

let MOI_SSC_INT_CASE = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN inside s
     ==> moi_sch3_simple (frontier (moi_ssc_reg k a v t1 t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SSC_FAR_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ff")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_REG_FACTS) THEN
  SUBGOAL_THEN `(v:real^3) IN interior (moi_ssc_reg k a v t1 t2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `a:real^3`; `t1:real`;
                   `t2:real`; `moi_ssc_stars k (v:real^3)`; `v:real^3`] MOI_SSL_INT_CRIT) THEN
    REWRITE_TAC[GSYM moi_ssc_reg] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `~((v:real^3) IN s)` ASSUME_TAC THENL
     [UNDISCH_TAC `inside s INTER (s:real^3->bool) = {}` THEN
      UNDISCH_TAC `(v:real^3) IN inside s` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_ssc_stars; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL MOI_SSC_INT_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC STAR_SIMPLE THEN EXISTS_TAC `v:real^3` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC STAR_SHAPED_PL_SPHERE THEN EXISTS_TAC `v:real^3` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `moi_ssc_far k (a:real^3) v t1 t2` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN X_GEN_TAC `f:real^3->bool` THEN
      STRIP_TAC THEN USE_THEN "ff" (MP_TAC o C MATCH_MP
        (ASSUME `(f:real^3->bool) IN moi_ssc_far k a v t1 t2`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SSC_RAY_HITS THEN
      MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`] THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPEC `moi_ssc_reg k (a:real^3) v t1 t2` INTERIOR_INSIDE_FRONTIER) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    MP_TAC(SPEC_ALL MOI_SSC_INT_FRONTIER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `(v:real^3) IN interior (moi_ssc_reg k a v t1 t2)` THEN SET_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                         `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
                        MOI_SSC_FAR_RADIAL) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The link polygon of a vertex of a triangulated 2-sphere.                 *)
(* ------------------------------------------------------------------------- *)

let moi_ssc_cyc = new_definition
 `moi_ssc_cyc (c:(real^3->bool)->bool) (v:real^3) n (m:num->real^3) <=>
    3 <= n /\ (!i. m(i + n) = m i) /\
    (!i. ~(m i = v) /\ {m i} IN c /\ segment[v,m i] IN c /\
         ~(m i = m(SUC i)) /\ segment[m i,m(SUC i)] IN c /\
         segment[m i,m(SUC i)] IN simplicial_link c v) /\
    (!i j. i < j /\ j < i + n
           ==> ~(segment[m i,m(SUC i)] = segment[m j,m(SUC j)])) /\
    (!y. segment[v,y] IN c /\ ~(y = v) ==> ?i. i < n /\ y = m i)`;;

let MOI_SSC_CYC_EXISTS = prove
 (`!c (v:real^3).
     simplicial_complex c /\ UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\ {v} IN c
     ==> ?n m. moi_ssc_cyc c v n m`,
  REWRITE_TAC[moi_ssc_cyc] THEN MATCH_ACCEPT_TAC MOI_SFB_CYCLE);;

(* The triangle at v over the i-th link edge.                               *)

let MOI_SSC_CYC_TRI = prove
 (`!c (v:real^3) n m i.
     simplicial_complex c /\ {v} IN c /\ moi_ssc_cyc c v n m
     ==> convex hull (v INSERT segment[m i,m(SUC i)]) IN c /\
         aff_dim (convex hull (v INSERT segment[m i,m(SUC i)])) = &2 /\
         segment[v,m i] SUBSET convex hull (v INSERT segment[m i,m(SUC i)]) /\
         segment[v,m(SUC i)] SUBSET convex hull (v INSERT segment[m i,m(SUC i)]) /\
         segment[m i,m(SUC i)] SUBSET convex hull (v INSERT segment[m i,m(SUC i)]) /\
         aff_dim (segment[m i,m(SUC i)]) = &1 /\
         ~(v IN affine hull (segment[m i,m(SUC i)]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssc_cyc] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `i:num`) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`;
                 `segment[(m:num->real^3) i,m(SUC i)]`] MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim (segment[(m:num->real^3) i,m(SUC i)]) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SUBGOAL_THEN
   `!x. x IN convex hull (v INSERT segment[(m:num->real^3) i,m(SUC i)])
        ==> segment[v,x] SUBSET convex hull (v INSERT segment[m i,m(SUC i)])`
  (LABEL_TAC "seg") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "seg" MATCH_MP_TAC THEN
    UNDISCH_TAC `segment[(m:num->real^3) i,m(SUC i)] SUBSET
                 convex hull (v INSERT segment[m i,m(SUC i)])` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    USE_THEN "seg" MATCH_MP_TAC THEN
    UNDISCH_TAC `segment[(m:num->real^3) i,m(SUC i)] SUBSET
                 convex hull (v INSERT segment[m i,m(SUC i)])` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (convex hull (v INSERT segment[(m:num->real^3) i,m(SUC i)])) =
                 aff_dim (segment[m i,m(SUC i)]) + &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_INSERT] THEN INT_ARITH_TAC]);;

(* No vertex lies on three link edges of a window (each edge at v lies in    *)
(* exactly two triangles).                                                  *)

let MOI_SSC_CYC_NOT3 = prove
 (`!c (v:real^3) n m y a b d.
     simplicial_complex c /\ UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\
     {v} IN c /\ moi_ssc_cyc c v n m /\ segment[v,y] IN c /\ ~(y = v) /\
     y IN segment[m a,m(SUC a)] /\ y IN segment[m b,m(SUC b)] /\
     y IN segment[m d,m(SUC d)] /\ a < b /\ b < d /\ d < a + n
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `moi_ssc_cyc c (v:real^3) n m`) THEN REWRITE_TAC[moi_ssc_cyc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "e") (CONJUNCTS_THEN2 (LABEL_TAC "w") (LABEL_TAC "all"))))) THEN
  SUBGOAL_THEN
   `!x. y IN segment[(m:num->real^3) x,m(SUC x)]
        ==> convex hull (v INSERT segment[m x,m(SUC x)]) IN c /\
            aff_dim (convex hull (v INSERT segment[m x,m(SUC x)])) = &2 /\
            segment[v,y] SUBSET convex hull (v INSERT segment[m x,m(SUC x)])`
  (LABEL_TAC "tri") THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `n:num`; `m:num->real^3`; `x:num`]
      MOI_SSC_CYC_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_CONVEX_HULL) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      UNDISCH_TAC `segment[(m:num->real^3) x,m(SUC x)] SUBSET
                   convex hull (v INSERT segment[m x,m(SUC x)])` THEN
      UNDISCH_TAC `(y:real^3) IN segment[m(x:num),m(SUC x)]` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. ~(segment[(m:num->real^3) x,m(SUC x)] = segment[m z,m(SUC z)])
          ==> ~(convex hull (v INSERT segment[m x,m(SUC x)]) =
                convex hull (v INSERT segment[m z,m(SUC z)]))`
  (LABEL_TAC "inj") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SCF_LINK_JOIN_INJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `v:real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "e" (MP_TAC o SPEC `x:num`) THEN SIMP_TAC[];
      USE_THEN "e" (MP_TAC o SPEC `z:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "tri" (MP_TAC o C MATCH_MP
    (ASSUME `(y:real^3) IN segment[m(a:num),m(SUC a)]`)) THEN
  USE_THEN "tri" (MP_TAC o C MATCH_MP
    (ASSUME `(y:real^3) IN segment[m(b:num),m(SUC b)]`)) THEN
  USE_THEN "tri" (MP_TAC o C MATCH_MP
    (ASSUME `(y:real^3) IN segment[m(d:num),m(SUC d)]`)) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `segment[v:real^3,y]`;
                 `convex hull (v INSERT segment[(m:num->real^3) a,m(SUC a)])`;
                 `convex hull (v INSERT segment[(m:num->real^3) b,m(SUC b)])`;
                 `convex hull (v INSERT segment[(m:num->real^3) d,m(SUC d)])`]
    MOI_SCF_SURF_EDGE_NOT3) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  REPEAT CONJ_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
  USE_THEN "w" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* The link vertices are distinct.                                          *)

let MOI_SSC_CYC_INJ = prove
 (`!c (v:real^3) n m.
     simplicial_complex c /\ UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\
     {v} IN c /\ moi_ssc_cyc c v n m
     ==> !i j. i < n /\ j < n /\ m i = m j ==> i = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i j. i < j /\ j < n /\ (m:num->real^3) i = m j ==> F` ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(SPECL [`i:num`; `j:num`] LT_CASES) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(DISJ_CASES_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`]) THEN ASM_REWRITE_TAC[]]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ASSUME `moi_ssc_cyc c (v:real^3) n m`) THEN REWRITE_TAC[moi_ssc_cyc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "e") (CONJUNCTS_THEN2 (LABEL_TAC "w") (LABEL_TAC "all"))))) THEN
  ASM_CASES_TAC `j = SUC i` THENL
   [USE_THEN "e" (MP_TAC o SPEC `i:num`) THEN
    UNDISCH_TAC `(m:num->real^3) i = m j` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. SUC p = j /\ i < p` (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `j - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `n:num`; `m:num->real^3`;
                       `(m:num->real^3) i`; `i:num`; `p:num`; `j:num`] MOI_SSC_CYC_NOT3) THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THEN
  TRY ASM_ARITH_TAC THEN
  USE_THEN "e" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[]);;

(* The link polygon is a PL 1-sphere.                                        *)

let MOI_SSC_CYC_POLY = prove
 (`!c (v:real^3) n m.
     simplicial_complex c /\ UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\
     {v} IN c /\ moi_ssc_cyc c v n m
     ==> pl_sphere 1 (UNIONS {segment[m i,m(SUC i)] | i | i < n})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_SSC_CYC_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "inj")] THEN
  MP_TAC(ASSUME `moi_ssc_cyc c (v:real^3) n m`) THEN REWRITE_TAC[moi_ssc_cyc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "per")
    (CONJUNCTS_THEN2 (LABEL_TAC "e") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(m:num->real^3)(SUC(n - 1)) = m 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC(n - 1) = 0 + n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; USE_THEN "per" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:3) /\ 2 <= n - 1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_3] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i <= n - 1 /\ j <= n - 1 /\ (m:num->real^3) i = m j ==> i = j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n - 1 ==> segment[(m:num->real^3) i,m(SUC i)] IN c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "e" (MP_TAC o SPEC `i:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[(m:num->real^3)(n - 1),m 0] IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `(m:num->real^3)(SUC(n - 1)) = m 0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "e" (MP_TAC o SPEC `n - 1`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `n - 1`; `m:num->real^3`]
    MOI_SLV_POLYGON_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `{segment[(m:num->real^3) i,m(SUC i)] | i | i < n} =
    segment[m(n - 1),m 0] INSERT {segment[m i,m(SUC i)] | i | i < n - 1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN X_GEN_TAC `e:real^3->bool` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `i = n - 1` THENL
       [DISJ1_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      STRIP_TAC THENL
       [EXISTS_TAC `n - 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    REWRITE_TAC[UNIONS_INSERT]]);;

(* Every triangle at v is one of the triangles over the link edges.         *)

let MOI_SSC_CYC_ALLTRI = prove
 (`!c (v:real^3) n m t.
     simplicial_complex c /\ UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\
     {v} IN c /\ moi_ssc_cyc c v n m /\
     t IN c /\ aff_dim t = &2 /\ v IN t
     ==> ?i. i < n /\ t = convex hull (v INSERT segment[m i,m(SUC i)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `moi_ssc_cyc c (v:real^3) n m`) THEN REWRITE_TAC[moi_ssc_cyc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "per")
    (CONJUNCTS_THEN2 (LABEL_TAC "e") (CONJUNCTS_THEN2 (LABEL_TAC "w") (LABEL_TAC "all"))))) THEN
  (* a vertex of t other than v *)
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SLV_SC_SIMPLEX_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (t:real^3->bool) /\ W SUBSET t` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `W:real^3->bool` CONVEX_CONVEX_HULL) THEN
    MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `W:real^3->bool`] HULL_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN W /\ ~(y = v)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    SUBGOAL_THEN `W SUBSET {v:real^3}` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SING] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
    MP_TAC(ASSUME `aff_dim(t:real^3->bool) = &2`) THEN
    MP_TAC(ASSUME `convex hull W = (t:real^3->bool)`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN t` ASSUME_TAC THENL
   [UNDISCH_TAC `W SUBSET (t:real^3->bool)` THEN UNDISCH_TAC `(y:real^3) IN W` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^3,y] IN c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFB_EDGE_IN THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!w:real^3. w IN W ==> {w} IN c` THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. y IN segment[(m:num->real^3) x,m(SUC x)]
        ==> convex hull (v INSERT segment[m x,m(SUC x)]) IN c /\
            aff_dim (convex hull (v INSERT segment[m x,m(SUC x)])) = &2 /\
            segment[v,y] SUBSET convex hull (v INSERT segment[m x,m(SUC x)])`
  (LABEL_TAC "tri") THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `n:num`; `m:num->real^3`; `x:num`]
      MOI_SSC_CYC_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_CONVEX_HULL) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      UNDISCH_TAC `segment[(m:num->real^3) x,m(SUC x)] SUBSET
                   convex hull (v INSERT segment[m x,m(SUC x)])` THEN
      UNDISCH_TAC `(y:real^3) IN segment[m(x:num),m(SUC x)]` THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "all" (MP_TAC o C MATCH_MP (CONJ (ASSUME `segment[v:real^3,y] IN c`)
    (ASSUME `~(y:real^3 = v)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i1:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `segment[v:real^3,y] SUBSET t` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT]
      (ASSUME `convex (t:real^3->bool)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the two triangles over the link edges at y *)
  SUBGOAL_THEN `(y:real^3) IN segment[m i1,m(SUC i1)] /\
                y IN segment[m(i1 + n - 1),m(SUC(i1 + n - 1))]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      SUBGOAL_THEN `SUC(i1 + n - 1) = i1 + n` SUBST1_TAC THENL
       [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "per" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  USE_THEN "tri" (MP_TAC o C MATCH_MP
    (ASSUME `(y:real^3) IN segment[m(i1:num),m(SUC i1)]`)) THEN
  USE_THEN "tri" (MP_TAC o C MATCH_MP
    (ASSUME `(y:real^3) IN segment[m(i1 + n - 1),m(SUC(i1 + n - 1))]`)) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~(convex hull (v INSERT segment[(m:num->real^3) i1,m(SUC i1)]) =
      convex hull (v INSERT segment[m(i1 + n - 1),m(SUC(i1 + n - 1))]))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`;
                   `segment[(m:num->real^3) i1,m(SUC i1)]`;
                   `segment[(m:num->real^3)(i1 + n - 1),m(SUC(i1 + n - 1))]`]
      MOI_SCF_LINK_JOIN_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]] THEN
    USE_THEN "w" MATCH_MP_TAC THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = convex hull (v INSERT segment[(m:num->real^3) i1,m(SUC i1)])` THENL
   [EXISTS_TAC `i1:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `t = convex hull (v INSERT segment[(m:num->real^3)(i1 + n - 1),m(SUC(i1 + n - 1))])`
  THENL
   [EXISTS_TAC `(i1 + n - 1) MOD n` THEN
    SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT_EQ] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\i. segment[(m:num->real^3) i,m(SUC i)]`; `n:num`]
      MOI_SFB_PERIODIC_MOD) THEN
    REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      REWRITE_TAC[ARITH_RULE `SUC(i + n) = SUC i + n`] THEN
      USE_THEN "per" (fun th -> REWRITE_TAC[th]);
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `segment[v:real^3,y]`; `t:real^3->bool`;
                 `convex hull (v INSERT segment[(m:num->real^3) i1,m(SUC i1)])`;
                 `convex hull (v INSERT segment[(m:num->real^3)(i1 + n - 1),
                                                m(SUC(i1 + n - 1))])`]
    MOI_SCF_SURF_EDGE_NOT3) THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT]);;

(* Near v the triangulated sphere is the cone from v over the link polygon. *)

let MOI_SSC_CYC_NEAR = prove
 (`!c (v:real^3) n m.
     simplicial_complex c /\ UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\
     {v} IN c /\ moi_ssc_cyc c v n m
     ==> ?r. &0 < r /\
             !y. y IN UNIONS c /\ dist(v,y) < r
                 ==> ?x. x IN UNIONS {segment[m i,m(SUC i)] | i | i < n} /\
                         y IN segment[v,x]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS {t | t IN c /\ ~((v:real^3) IN t)}`; `v:real^3`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
          SIMP_TAC[simplicial_complex];
          SET_TAC[]];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^3) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^3) IN t0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "sep" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `t0:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SCF_SURF_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^3) IN t0` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `n:num`; `m:num->real^3`;
                 `t:real^3->bool`] MOI_SSC_CYC_ALLTRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^3) IN t0` THEN
    UNDISCH_TAC `(t0:real^3->bool) SUBSET t` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN convex hull (v INSERT segment[m(i:num),m(SUC i)])`
  MP_TAC THENL
   [UNDISCH_TAC `t = convex hull (v INSERT segment[(m:num->real^3) i,m(SUC i)])` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(t0:real^3->bool) SUBSET t` THEN UNDISCH_TAC `(y:real^3) IN t0` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[CONVEX_HULL_INSERT; SEGMENT_EQ_EMPTY; HULL_P; CONVEX_SEGMENT;
           IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:real`
    (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `b:real^3` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `segment[(m:num->real^3) i,m(SUC i)]` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `w:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `u = &1 - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The boundary-vertex case of the star statement and the final theorem.     *)
(* ------------------------------------------------------------------------- *)

let MOI_SSC_KS_FACTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN s
     ==> simplicial_complex {c | c IN k /\ c SUBSET s} /\
         UNIONS {c | c IN k /\ c SUBSET s} = s /\
         UNIONS {c | c IN k /\ c SUBSET s} homeomorphic sphere(vec 0:real^3,&1) /\
         {v} IN {c | c IN k /\ c SUBSET s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  SUBGOAL_THEN `UNIONS {c | c IN k /\ c SUBSET s} = (s:real^3->bool)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SSL_SPHERE_UNIONS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; SING_SUBSET] THEN CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (k:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
      ASM_MESON_TAC[]];
    MP_TAC(ISPEC `{c | c IN k /\ c SUBSET (s:real^3->bool)}` MOI_SFB_SPHERE_FACTS) THEN
    ASM_SIMP_TAC[]]);;

(* For a simplex c of k at v, the far point on the ray through a point of c *)
(* in the slab lies in c.                                                   *)

let MOI_SSC_FAR_IN_FACE = prove
 (`!s (a:real^3) lo hi k v t1 t2 c y.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ c IN k /\ v IN c /\ y IN c /\
     ~(y = v) /\ t1 <= a dot y /\ a dot y <= t2
     ==> ?x. x IN c /\ x IN UNIONS (moi_ssc_far k a v t1 t2) /\ y IN segment[v,x]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  MP_TAC(ISPEC `k:(real^3->bool)->bool` MOI_SSL_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^3) IN c` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t IN moi_ssc_stars k (v:real^3) /\ (y:real^3) IN t` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET t` THEN UNDISCH_TAC `(v:real^3) IN c` THEN
    UNDISCH_TAC `(y:real^3) IN c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c face_of (t:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real^3->bool`; `t:real^3->bool`]
      MOI_SSL_SC_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `c INTER t = (c:real^3->bool)` (fun th -> SIMP_TAC[th]) THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET t` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`; `y:real^3`] MOI_SSC_STAR_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `y:real^3 = x` THENL
   [UNDISCH_TAC `(y:real^3) IN c` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `c face_of (t:real^3->bool)` THEN REWRITE_TAC[face_of] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `x:real^3`; `y:real^3`] o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET t` THEN UNDISCH_TAC `(v:real^3) IN c` THEN
    SET_TAC[];
    SIMP_TAC[]]);;

(* The boundary pieces: far parts of the simplices of s at v.               *)

let moi_ssc_jfam = new_definition
 `moi_ssc_jfam (s:real^3->bool) (k:(real^3->bool)->bool) (a:real^3) (v:real^3) t1 t2 =
    {c INTER f | c IN k /\ c SUBSET s /\ v IN c /\ f IN moi_ssc_far k a v t1 t2}`;;

let MOI_SSC_JFAM_FACTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> FINITE (moi_ssc_jfam s k a v t1 t2) /\
         (!g. g IN moi_ssc_jfam s k a v t1 t2 ==> polytope g /\ ~(v IN affine hull g)) /\
         UNIONS (moi_ssc_jfam s k a v t1 t2) SUBSET UNIONS (moi_ssc_far k a v t1 t2) /\
         (!x. x IN UNIONS (moi_ssc_jfam s k a v t1 t2) ==> segment[v,x] SUBSET s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SSC_FAR_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ff")) THEN
  REWRITE_TAC[moi_ssc_jfam] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{c INTER f | c IN k /\ f IN moi_ssc_far k (a:real^3) v t1 t2}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "ff" (MP_TAC o C MATCH_MP
      (ASSUME `(f:real^3->bool) IN moi_ssc_far k a v t1 t2`)) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `~((v:real^3) IN affine hull f)` THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t ==> x IN s ==> x IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b:real^3->bool c. b SUBSET UNIONS c /\ a SUBSET b
                                                ==> a SUBSET UNIONS c`) THEN
    EXISTS_TAC `f:real^3->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!f s:real^3->bool. s IN f ==> s SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `c:real^3->bool` (X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC))
      ASSUME_TAC)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT]
      (ASSUME `convex (c:real^3->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN g` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[]]);;

(* The radial transfer respects unions of the family members.               *)

let MOI_SSC_IMAGE_CONE_UNIONS = prove
 (`!(h:real^N->real^N) q v gg.
     (!g. g IN gg ==> IMAGE h (relative_frontier q INTER moi_ssc_cone v g) = g)
     ==> IMAGE h (relative_frontier q INTER moi_ssc_cone v (UNIONS gg)) = UNIONS gg`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `relative_frontier q INTER moi_ssc_cone v (UNIONS gg) =
    UNIONS (IMAGE (\g. relative_frontier q INTER moi_ssc_cone (v:real^N) g) gg)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM; IN_INTER; MOI_SSC_CONE_EXPLICIT] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real`
        (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC))) THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS gg` THEN REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`c:real`; `x:real^N`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real`
          (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC))))) THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`c:real`; `x:real^N`] THEN
      ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `g:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE] THEN
    X_GEN_TAC `x:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N->bool` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC))) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN
      EXISTS_TAC `relative_frontier q INTER moi_ssc_cone (v:real^N) x` THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

(* A small box around a boundary vertex v and its trace on s and on M.      *)

let MOI_SSC_BOX = prove
 (`!s (a:real^3) lo hi k v t1 t2 n m.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN s /\
     moi_ssc_cyc {c | c IN k /\ c SUBSET s} v n m
     ==> ?sx. polytope sx /\ v IN interior sx /\
              (!y. y IN relative_frontier sx
                   ==> (y IN s <=>
                        y IN moi_ssc_cone v (UNIONS {segment[m i,m(SUC i)] | i | i < n})) /\
                       (y IN s <=>
                        y IN moi_ssc_cone v (UNIONS (moi_ssc_jfam s k a v t1 t2))) /\
                       (y IN s UNION inside s <=>
                        y IN moi_ssc_cone v (UNIONS (moi_ssc_far k a v t1 t2)))) /\
              (?z. z IN relative_frontier sx /\ z IN inside s) /\
              ~(relative_frontier sx SUBSET s UNION inside s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  MP_TAC(SPEC_ALL MOI_SSC_KS_FACTS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SSC_FAR_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ff")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_JFAM_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_REG_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SSC_FAR_SUB) THEN
  (* the triangles over the link edges lie in s and contain v *)
  SUBGOAL_THEN
   `!i. convex hull (v INSERT segment[(m:num->real^3) i,m(SUC i)]) IN k /\
        convex hull (v INSERT segment[m i,m(SUC i)]) SUBSET s /\
        v IN convex hull (v INSERT segment[m i,m(SUC i)]) /\
        segment[m i,m(SUC i)] SUBSET convex hull (v INSERT segment[m i,m(SUC i)]) /\
        ~(v IN segment[m i,m(SUC i)])`
  (LABEL_TAC "T") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`{c | c IN k /\ c SUBSET (s:real^3->bool)}`; `v:real^3`; `n:num`;
                   `m:num->real^3`; `i:num`] MOI_SSC_CYC_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    UNDISCH_TAC `~((v:real^3) IN affine hull segment[m(i:num),m(SUC i)])` THEN
    REWRITE_TAC[CONTRAPOS_THM; HULL_INC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}
        ==> segment[v,x] SUBSET s /\ ~(x = v) /\
            ?c. c IN k /\ c SUBSET s /\ v IN c /\ segment[v,x] SUBSET c`
  (LABEL_TAC "Lseg") THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "T" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    SUBGOAL_THEN `segment[v:real^3,x] SUBSET
                  convex hull (v INSERT segment[m(i:num),m(SUC i)])` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_CONVEX_HULL) THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `segment[(m:num->real^3) i,m(SUC i)] SUBSET
                   convex hull (v INSERT segment[m i,m(SUC i)])` THEN
      UNDISCH_TAC `(x:real^3) IN segment[m(i:num),m(SUC i)]` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `segment[v:real^3,x] SUBSET
                   convex hull (v INSERT segment[m(i:num),m(SUC i)])` THEN
      UNDISCH_TAC `convex hull (v INSERT segment[(m:num->real^3) i,m(SUC i)]) SUBSET s` THEN
      SET_TAC[];
      UNDISCH_TAC `~((v:real^3) IN segment[m(i:num),m(SUC i)])` THEN
      UNDISCH_TAC `(x:real^3) IN segment[m(i:num),m(SUC i)]` THEN SET_TAC[];
      EXISTS_TAC `convex hull (v INSERT segment[(m:num->real^3) i,m(SUC i)])` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* radii *)
  MP_TAC(ISPECL [`{c | c IN k /\ c SUBSET (s:real^3->bool)}`; `v:real^3`; `n:num`;
                 `m:num->real^3`] MOI_SSC_CYC_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nL"))) THEN
  MP_TAC(ISPECL [`UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`; `v:real^3`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; CLOSED_SEGMENT];
      DISCH_TAC THEN USE_THEN "Lseg" (MP_TAC o C MATCH_MP (ASSUME
        `(v:real^3) IN UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`)) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sL"))) THEN
  MP_TAC(ISPECL [`UNIONS (moi_ssc_far k (a:real^3) v t1 t2)`; `v:real^3`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `f:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "ff" (MP_TAC o C MATCH_MP (ASSUME
        `(f:real^3->bool) IN moi_ssc_far k a v t1 t2`)) THEN
      MESON_TAC[POLYTOPE_IMP_CLOSED];
      REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN X_GEN_TAC `f:real^3->bool` THEN
      STRIP_TAC THEN USE_THEN "ff" (MP_TAC o C MATCH_MP (ASSUME
        `(f:real^3->bool) IN moi_ssc_far k a v t1 t2`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sd"))) THEN
  MP_TAC(SPEC_ALL MOI_SSC_NEAR_V) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nV"))) THEN
  MP_TAC(ISPEC `{x:real^3 | a dot x > t1} INTER {x | a dot x < t2}` OPEN_CONTAINS_BALL) THEN
  SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_GT; OPEN_HALFSPACE_LT] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `r5:real` STRIP_ASSUME_TAC) THEN
  (* an interior point y0 of a star simplex *)
  MP_TAC(SPEC_ALL MOI_SSC_WEDGE_EXISTS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSC_STAR_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN interior t0 /\ ~(y0 = v)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(interior t0 INTER {x:real^3 | a dot x = a dot v} = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t0:real^3->bool`; `v:real^3`] EXTREME_POINT_NOT_IN_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3`; `min (min r1 r2) (min (min r3 r4) (min r5 (dist(v:real^3,y0))))`]
    MOI_SSC_SMALL_BOX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN MATCH_MP_TAC DIST_POS_LT THEN
    UNDISCH_TAC `~(y0:real^3 = v)` THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sx:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sx:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!y. y IN sx ==> dist(v:real^3,y) < r1 /\ dist(v,y) < r2 /\ dist(v,y) < r3 /\
                    dist(v,y) < r4 /\ dist(v,y) < dist(v,y0) /\
                    t1 <= a dot y /\ a dot y <= t2`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN ball(v,r5) /\
                  dist(v,y) < min (min r1 r2) (min (min r3 r4) (min r5 (dist(v,y0))))`
    MP_TAC THENL
     [UNDISCH_TAC `sx SUBSET ball(v:real^3,min (min r1 r2) (min (min r3 r4)
                                              (min r5 (dist(v,y0)))))` THEN
      UNDISCH_TAC `(y:real^3) IN sx` THEN REWRITE_TAC[SUBSET; IN_BALL; REAL_LT_MIN] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ball(v:real^3,r5) SUBSET {x | t1 < a dot x} INTER {x | a dot x < t2}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; REAL_LT_MIN] THEN
    DISCH_THEN(fun th -> DISCH_THEN(fun th' -> MP_TAC(MATCH_MP th (CONJUNCT1 th')) THEN
                                                MP_TAC(CONJUNCT2 th'))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sx /\ ~(y = v)
        ==> (y IN s <=>
             y IN moi_ssc_cone v (UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n})) /\
            (y IN s <=> y IN moi_ssc_cone v (UNIONS (moi_ssc_jfam s k a v t1 t2))) /\
            (y IN s UNION inside s <=>
             y IN moi_ssc_cone v (UNIONS (moi_ssc_far k a v t1 t2)))`
  (LABEL_TAC "eq") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "near" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN sx`)) THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [USE_THEN "nL" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN s`)
        (ASSUME `dist(v:real^3,y) < r1`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_SSC_SEG_IN_CONE THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`v:real^3`;
                     `UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`;
                     `y:real^3`; `r2:real`] MOI_SSC_CONE_NEAR) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "Lseg" (MP_TAC o C MATCH_MP (ASSUME
        `(x:real^3) IN UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`)) THEN
      UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN SET_TAC[];
      USE_THEN "nL" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN s`)
        (ASSUME `dist(v:real^3,y) < r1`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "Lseg" (MP_TAC o C MATCH_MP (ASSUME
        `(x:real^3) IN UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
      MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `c:real^3->bool`; `y:real^3`] MOI_SSC_FAR_IN_FACE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `segment[v:real^3,x] SUBSET c` THEN
        UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_SSC_SEG_IN_CONE THEN EXISTS_TAC `x0:real^3` THEN
      ASM_REWRITE_TAC[moi_ssc_jfam] THEN
      UNDISCH_TAC `(x0:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c INTER f:real^3->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      MAP_EVERY EXISTS_TAC [`c:real^3->bool`; `f:real^3->bool`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`v:real^3`; `UNIONS (moi_ssc_jfam s k (a:real^3) v t1 t2)`;
                     `y:real^3`; `r3:real`] MOI_SSC_CONE_NEAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        USE_THEN "sd" MATCH_MP_TAC THEN
        UNDISCH_TAC `UNIONS (moi_ssc_jfam s k (a:real^3) v t1 t2) SUBSET
                     UNIONS (moi_ssc_far k a v t1 t2)` THEN
        UNDISCH_TAC `(x:real^3) IN UNIONS (moi_ssc_jfam s k a v t1 t2)` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(MATCH_MP (ASSUME `!x:real^3. x IN UNIONS (moi_ssc_jfam s k a v t1 t2)
                                          ==> segment[v,x] SUBSET s`)
        (ASSUME `(x:real^3) IN UNIONS (moi_ssc_jfam s k a v t1 t2)`)) THEN
      UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN SET_TAC[];
      USE_THEN "nV" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN s UNION inside s`)
        (ASSUME `dist(v:real^3,y) < r4`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `t:real^3->bool`; `y:real^3`] MOI_SSC_STAR_CONE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_SSC_SEG_IN_CONE THEN EXISTS_TAC `x0:real^3` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`v:real^3`; `UNIONS (moi_ssc_far k (a:real^3) v t1 t2)`;
                     `y:real^3`; `r3:real`] MOI_SSC_CONE_NEAR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `a:real^3`; `v:real^3`; `t1:real`; `t2:real`;
                     `x0:real^3`] MOI_SSC_REG_STAR) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        UNDISCH_TAC `UNIONS (moi_ssc_far k a v t1 t2) SUBSET moi_ssc_reg k (a:real^3) v t1 t2` THEN
        UNDISCH_TAC `(x0:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `moi_ssc_reg k a v t1 t2 SUBSET (s:real^3->bool) UNION inside s` THEN
      UNDISCH_TAC `(y:real^3) IN segment[v,x0]` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior sx = interior (sx:real^3->bool) /\
                affine hull sx = (:real^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR;
      MATCH_MP_TAC AFFINE_HULL_NONEMPTY_INTERIOR] THEN
    UNDISCH_TAC `(v:real^3) IN interior sx` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sx:real^3->bool`; `v:real^3`] MOI_SSC_RADIAL_RETRACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "ret"))) THEN
  SUBGOAL_THEN `relative_frontier sx SUBSET (sx:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED; SUBSET_DIFF];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`sx:real^3->bool`; `v:real^3`; `y:real^3`] MOI_SSC_RF_FACTS) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "ret" (MP_TAC o C MATCH_MP (ASSUME `~(y0:real^3 = v)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(r:real^3->real^3) y0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `dist(v:real^3,(r:real^3->real^3) y0) < dist(v,y0)` MP_TAC THENL
       [USE_THEN "near" (MP_TAC o C MATCH_MP (MATCH_MP (REWRITE_RULE[SUBSET]
          (ASSUME `relative_frontier sx SUBSET (sx:real^3->bool)`))
          (ASSUME `(r:real^3->real^3) y0 IN relative_frontier sx`))) THEN SIMP_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[dist; VECTOR_ARITH `v - (v + c % (y - v)):real^3 = c % (v - y)`;
                      NORM_MUL] THEN
      ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < norm(v - y0:real^3)` ASSUME_TAC THENL
       [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN UNDISCH_TAC `~(y0:real^3 = v)` THEN
        MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`c:real`; `&1`; `norm(v - y0:real^3)`] REAL_LT_RMUL_EQ) THEN
      ASM_REWRITE_TAC[REAL_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^3->real^3) y0 IN interior t0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t0:real^3->bool`; `c:real`; `v:real^3`; `y0:real^3`]
        IN_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MP_TAC(ASSUME `t0 = convex hull (c0:real^3->bool)`) THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
          FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
          UNDISCH_TAC `t0 IN moi_ssc_stars k (v:real^3)` THEN
          SIMP_TAC[moi_ssc_stars; IN_ELIM_THM];
          FIRST_ASSUM ACCEPT_TAC;
          ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        ASM_REWRITE_TAC[VECTOR_ARITH `v - c % (v - y):real^3 = v + c % (y - v)`]];
      ALL_TAC] THEN
    UNDISCH_TAC `interior (s UNION inside s) = inside (s:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`t0:real^3->bool`; `(s:real^3->bool) UNION inside s`]
      SUBSET_INTERIOR) THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `(r:real^3->real^3) y0 IN interior t0` THEN ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `t0 IN moi_ssc_stars k (v:real^3)` THEN
    UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
    REWRITE_TAC[moi_ssc_stars; IN_ELIM_THM] THEN SET_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `sx SUBSET (s:real^3->bool) UNION inside s` MP_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `y:real^3 = v` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "ret" (MP_TAC o C MATCH_MP (ASSUME `~(y:real^3 = v)`)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `~((r:real^3->real^3) y = v)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_ARITH `v + c % (y - v):real^3 = v <=> c % (y - v) = vec 0`;
                        VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NZ];
        ALL_TAC] THEN
      USE_THEN "eq" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN sx`)
        (ASSUME `~(y:real^3 = v)`))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2) THEN
      SUBGOAL_THEN `y:real^3 = v + inv c % ((r:real^3->real^3) y - v)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_ADD_SUB; VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_SSC_CONE_SCALE THEN CONJ_TAC THENL
       [USE_THEN "eq" (MP_TAC o C MATCH_MP (CONJ
          (MATCH_MP (REWRITE_RULE[SUBSET]
             (ASSUME `relative_frontier sx SUBSET (sx:real^3->bool)`))
             (ASSUME `(r:real^3->real^3) y IN relative_frontier sx`))
          (ASSUME `~((r:real^3->real^3) y = v)`))) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
        UNDISCH_TAC `relative_frontier sx SUBSET (s:real^3->bool) UNION inside s` THEN
        UNDISCH_TAC `(r:real^3->real^3) y IN relative_frontier sx` THEN SET_TAC[];
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `inside s INTER (s:real^3->bool) = {}` THEN
    UNDISCH_TAC `(v:real^3) IN interior sx` THEN UNDISCH_TAC `(v:real^3) IN s` THEN
    SET_TAC[]]);;

let MOI_SSC_CONN_SIDE = prove
 (`!u e1 e2:real^3->bool.
     connected u /\ open e1 /\ open e2 /\ e1 INTER e2 = {} /\ u SUBSET e1 UNION e2 /\
     ~(u INTER e1 = {})
     ==> u SUBSET e1`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `connected (u:real^3->bool)` THEN
  REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^3->bool`; `e2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `e1 INTER e2 = {}:real^3->bool` THEN
  UNDISCH_TAC `~((u:real^3->bool) INTER e1 = {})` THEN
  UNDISCH_TAC `(u:real^3->bool) SUBSET e1 UNION e2` THEN SET_TAC[]);;

(* The far part of the star region at a boundary vertex is a PL 2-cell      *)
(* whose boundary is the union j of the boundary pieces.                    *)

let MOI_SSC_BDY_DISK = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN s
     ==> pl_cell_with_boundary 2 (UNIONS (moi_ssc_far k a v t1 t2))
                                 (UNIONS (moi_ssc_jfam s k a v t1 t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  MP_TAC(SPEC_ALL MOI_SSC_KS_FACTS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`{c | c IN k /\ c SUBSET (s:real^3->bool)}`; `v:real^3`]
    MOI_SSC_CYC_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `m:num->real^3`)) THEN
  MP_TAC(SPEC_ALL MOI_SSC_BOX) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sx:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bx")
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) ASSUME_TAC))))) THEN
  SUBGOAL_THEN `~(interior sx = {}:real^3->bool) /\
                relative_interior sx = interior (sx:real^3->bool) /\
                affine hull sx = (:real^3)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(interior sx = {}:real^3->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:real^3) IN interior sx` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_NONEMPTY_INTERIOR; AFFINE_HULL_NONEMPTY_INTERIOR];
    ALL_TAC] THEN
  (* J1 = rf sx INTER s is a PL circle *)
  SUBGOAL_THEN `pl_sphere 1 (relative_frontier sx INTER (s:real^3->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`; `sx:real^3->bool`;
                   `v:real^3`] MOI_SSC_RADIAL_TRANSFER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_UNIV] THEN REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
        SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
        REWRITE_TAC[FORALL_IN_GSPEC; POLYTOPE_SEGMENT] THEN X_GEN_TAC `i:num` THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL [`{c | c IN k /\ c SUBSET (s:real^3->bool)}`; `v:real^3`; `n:num`;
                       `m:num->real^3`; `i:num`] MOI_SSC_CYC_TRI) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        MP_TAC(ISPECL [`{c | c IN k /\ c SUBSET (s:real^3->bool)}`; `v:real^3`]
          MOI_STA_LINK_FACTS) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[MOI_SSL_SC_LF]; ALL_TAC] THEN
        DISCH_THEN(LABEL_TAC "lk" o CONJUNCT2) THEN
        SUBGOAL_THEN
         `UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n} SUBSET
          UNIONS (simplicial_link {c | c IN k /\ c SUBSET s} v)`
        ASSUME_TAC THENL
         [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN
          DISCH_TAC THEN
          MATCH_MP_TAC(SET_RULE `!f s:real^3->bool. s IN f ==> s SUBSET UNIONS f`) THEN
          UNDISCH_TAC `moi_ssc_cyc {c | c IN k /\ c SUBSET s} (v:real^3) n m` THEN
          REWRITE_TAC[moi_ssc_cyc] THEN SIMP_TAC[];
          ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
        USE_THEN "lk" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `(x:real^3) IN UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`;
          UNDISCH_TAC `(y:real^3) IN UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`;
          FIRST_ASSUM ACCEPT_TAC] THEN
        UNDISCH_TAC
         `UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n} SUBSET
          UNIONS (simplicial_link {c | c IN k /\ c SUBSET s} v)` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h1:real^3->real^3` (X_CHOOSE_THEN `h1':real^3->real^3`
      (MP_TAC o CONJUNCT1))) THEN
    SUBGOAL_THEN
     `relative_frontier sx INTER
      moi_ssc_cone v (UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}) =
      relative_frontier sx INTER (s:real^3->bool)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
      ASM_CASES_TAC `(y:real^3) IN relative_frontier sx` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "bx" (MP_TAC o CONJUNCT1 o C MATCH_MP
        (ASSUME `(y:real^3) IN relative_frontier sx`)) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`1`; `UNIONS {segment[(m:num->real^3) i,m(SUC i)] | i | i < n}`;
                   `relative_frontier sx INTER (s:real^3->bool)`;
                   `h1':real^3->real^3`; `h1:real^3->real^3`]
      MOI_CMB_PL_SPHERE_TRANSFER) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC MOI_SSC_CYC_POLY THEN
    MAP_EVERY EXISTS_TAC [`{c | c IN k /\ c SUBSET (s:real^3->bool)}`; `v:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the box boundary is a PL 2-sphere; split it along J1 *)
  SUBGOAL_THEN `pl_sphere 2 (relative_frontier (sx:real^3->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    MP_TAC(ISPEC `sx:real^3->bool` MOI_SSL_CELL_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier sx:real^3->bool`;
                 `relative_frontier sx INTER (s:real^3->bool)`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  (* the half containing a point of inside s is E1 = rf sx INTER M *)
  SUBGOAL_THEN
   `!da db:real^3->bool.
      pl_cell_with_boundary 2 da (relative_frontier sx INTER s) /\
      pl_cell_with_boundary 2 db (relative_frontier sx INTER s) /\
      da UNION db = relative_frontier sx /\ z IN da
      ==> relative_frontier sx INTER (s UNION inside s) = da`
  (LABEL_TAC "side") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!d:real^3->bool. pl_cell_with_boundary 2 d (relative_frontier sx INTER s)
                       ==> relative_frontier sx INTER s SUBSET d /\
                           connected (d DIFF (relative_frontier sx INTER s))`
    (LABEL_TAC "cf") THENL
     [GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "cf" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME
      `pl_cell_with_boundary 2 (da:real^3->bool) (relative_frontier sx INTER s)`)) THEN
    USE_THEN "cf" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME
      `pl_cell_with_boundary 2 (db:real^3->bool) (relative_frontier sx INTER s)`)) THEN
    SUBGOAL_THEN `open(inside s) /\ open(outside s) /\
                  inside s INTER outside s = {} /\
                  relative_frontier sx DIFF (relative_frontier sx INTER s) SUBSET
                  inside s UNION outside (s:real^3->bool) /\
                  outside s INTER (s UNION inside s) = {}`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[OPEN_INSIDE];
        ASM_SIMP_TAC[OPEN_OUTSIDE];
        REWRITE_TAC[INSIDE_INTER_OUTSIDE];
        MP_TAC(ISPEC `s:real^3->bool` INSIDE_UNION_OUTSIDE) THEN SET_TAC[];
        REWRITE_TAC[OUTSIDE_INSIDE] THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `da DIFF (relative_frontier sx INTER s) SUBSET inside (s:real^3->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SSC_CONN_SIDE THEN EXISTS_TAC `outside (s:real^3->bool)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `relative_frontier sx DIFF (relative_frontier sx INTER s) SUBSET
                     inside s UNION outside (s:real^3->bool)` THEN
        UNDISCH_TAC `da UNION db = relative_frontier (sx:real^3->bool)` THEN SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^3` THEN
        UNDISCH_TAC `inside s INTER (s:real^3->bool) = {}` THEN
        UNDISCH_TAC `(z:real^3) IN inside s` THEN UNDISCH_TAC `(z:real^3) IN da` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `db DIFF (relative_frontier sx INTER s) SUBSET outside (s:real^3->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SSC_CONN_SIDE THEN EXISTS_TAC `inside (s:real^3->bool)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `inside s INTER outside s = {}:real^3->bool` THEN SET_TAC[];
        UNDISCH_TAC `relative_frontier sx DIFF (relative_frontier sx INTER s) SUBSET
                     inside s UNION outside (s:real^3->bool)` THEN
        UNDISCH_TAC `da UNION db = relative_frontier (sx:real^3->bool)` THEN SET_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `~(relative_frontier sx SUBSET (s:real^3->bool) UNION inside s)` THEN
        REWRITE_TAC[] THEN
        UNDISCH_TAC `(db DIFF (relative_frontier sx INTER s)) INTER outside s =
                     {}:real^3->bool` THEN
        UNDISCH_TAC `relative_frontier sx DIFF (relative_frontier sx INTER s) SUBSET
                     inside s UNION outside (s:real^3->bool)` THEN
        UNDISCH_TAC `da DIFF (relative_frontier sx INTER s) SUBSET inside (s:real^3->bool)` THEN
        UNDISCH_TAC `da UNION db = relative_frontier (sx:real^3->bool)` THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `da DIFF (relative_frontier sx INTER s) SUBSET inside (s:real^3->bool)` THEN
    UNDISCH_TAC `db DIFF (relative_frontier sx INTER s) SUBSET outside (s:real^3->bool)` THEN
    UNDISCH_TAC `relative_frontier sx INTER s SUBSET (da:real^3->bool)` THEN
    UNDISCH_TAC `da UNION db = relative_frontier (sx:real^3->bool)` THEN
    UNDISCH_TAC `outside s INTER (s UNION inside s) = {}:real^3->bool` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (relative_frontier sx INTER (s UNION inside s))
                                        (relative_frontier sx INTER (s:real^3->bool))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN d1 \/ z IN d2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `d1 UNION d2 = relative_frontier (sx:real^3->bool)` THEN
      UNDISCH_TAC `(z:real^3) IN relative_frontier sx` THEN SET_TAC[];
      SUBGOAL_THEN `relative_frontier sx INTER (s UNION inside s) = d1:real^3->bool`
        SUBST1_TAC THENL
       [USE_THEN "side" MATCH_MP_TAC THEN EXISTS_TAC `d2:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `relative_frontier sx INTER (s UNION inside s) = d2:real^3->bool`
        SUBST1_TAC THENL
       [USE_THEN "side" MATCH_MP_TAC THEN EXISTS_TAC `d1:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* transfer E1 to the far part d *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_JFAM_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SSC_FAR_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ff")) THEN
  MP_TAC(ISPECL [`moi_ssc_far k (a:real^3) v t1 t2 UNION moi_ssc_jfam s k a v t1 t2`;
                 `sx:real^3->bool`; `v:real^3`] MOI_SSC_RADIAL_TRANSFER) THEN
  SUBGOAL_THEN `UNIONS (moi_ssc_far k a v t1 t2 UNION moi_ssc_jfam s k a v t1 t2) =
                UNIONS (moi_ssc_far k (a:real^3) v t1 t2)` SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_UNION] THEN
    UNDISCH_TAC `UNIONS (moi_ssc_jfam s k (a:real^3) v t1 t2) SUBSET
                 UNIONS (moi_ssc_far k a v t1 t2)` THEN SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; SUBSET_UNIV; IN_UNION] THEN CONJ_TAC THENL
     [X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THENL
       [USE_THEN "ff" (MP_TAC o C MATCH_MP (ASSUME
          `(f:real^3->bool) IN moi_ssc_far k a v t1 t2`)) THEN SIMP_TAC[];
        UNDISCH_TAC `!g. g IN moi_ssc_jfam s k a v t1 t2
                         ==> polytope g /\ ~((v:real^3) IN affine hull g)` THEN
        DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME
          `(f:real^3->bool) IN moi_ssc_jfam s k a v t1 t2`)) THEN SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                           `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
                          MOI_SSC_FAR_RADIAL) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "img")))) THEN
  SUBGOAL_THEN
   `relative_frontier sx INTER moi_ssc_cone v (UNIONS (moi_ssc_far k a v t1 t2)) =
    relative_frontier sx INTER ((s:real^3->bool) UNION inside s) /\
    relative_frontier sx INTER moi_ssc_cone v (UNIONS (moi_ssc_jfam s k a v t1 t2)) =
    relative_frontier sx INTER (s:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
    ASM_CASES_TAC `(y:real^3) IN relative_frontier sx` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "bx" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN relative_frontier sx`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^3->real^3) (relative_frontier sx INTER s) =
    UNIONS (moi_ssc_jfam s k (a:real^3) v t1 t2)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `relative_frontier sx INTER
                 moi_ssc_cone v (UNIONS (moi_ssc_jfam s k a v t1 t2)) =
                 relative_frontier sx INTER (s:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_SSC_IMAGE_CONE_UNIONS THEN X_GEN_TAC `g:real^3->bool` THEN
    DISCH_TAC THEN USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism
                (relative_frontier sx INTER moi_ssc_cone v (UNIONS (moi_ssc_far k a v t1 t2)),
                 UNIONS (moi_ssc_far k a v t1 t2)) (h:real^3->real^3,h')` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (relative_frontier sx INTER (s UNION inside s))
                                       (relative_frontier sx INTER (s:real^3->bool))` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`K:real^3->bool`; `(h:real^3->real^3) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (h':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier sx INTER ((s:real^3->bool) UNION inside s)` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (relative_frontier sx INTER s) =
                 UNIONS (moi_ssc_jfam s k (a:real^3) v t1 t2)` THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]);;

let MOI_SSC_CELL_BOUNDARY_NONEMPTY = prove
 (`!(d:real^N->bool) j. pl_cell_with_boundary 2 d j ==> ~(j = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; SIMPLEX_IMP_COMPACT] THEN
  ASM_MESON_TAC[AFF_DIM_SIMPLEX; AFF_DIM_EMPTY; AFF_DIM_SING; INT_ARITH `~(&2:int = -- &1)`;
                INT_ARITH `~(&2:int = &0)`; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]);;

(* At a boundary vertex the frontier of the star region is the far part    *)
(* with the cone from v over its boundary j.                                *)

let MOI_SSC_IN_CONE_SEGS = prove
 (`!(v:real^3) x x0 j.
     x0 IN j /\ x IN segment[v,x0] ==> x IN UNIONS {segment[v,y] | y | y IN j}`,
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_SSC_BDY_FRONTIER = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN s
     ==> frontier (moi_ssc_reg k a v t1 t2) =
         UNIONS (moi_ssc_far k a v t1 t2) UNION
         UNIONS {segment[v,x] | x | x IN UNIONS (moi_ssc_jfam s k a v t1 t2)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_JFAM_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSC_REG_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SSC_FAR_SUB) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SSC_FAR_FRONTIER) THEN
  MP_TAC(SPEC_ALL MOI_SSC_BDY_DISK) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_SSC_CELL_BOUNDARY_NONEMPTY) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `x:real^3`] MOI_SSC_FRONTIER_FAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_CASES_TAC `x:real^3 = v` THENL
     [UNDISCH_TAC `~(UNIONS (moi_ssc_jfam s k (a:real^3) v t1 t2) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `x0:real^3`) THEN
      MATCH_MP_TAC MOI_SSC_IN_CONE_SEGS THEN EXISTS_TAC `x0:real^3` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[moi_ssc_reg; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM]
      (ASSUME `(x:real^3) IN moi_ssc_reg k a v t1 t2`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:real^3->bool) IN k` ASSUME_TAC THENL
     [UNDISCH_TAC `t IN moi_ssc_stars k (v:real^3)` THEN
      SIMP_TAC[moi_ssc_stars; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `x:real^3`] MOI_SSL_CARRIER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "car")))) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `c:real^3->bool`;
                   `x:real^3`] MOI_SSL_SPHERE_SIMPLICES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "car" (MP_TAC o SPEC `t:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN c` ASSUME_TAC THENL
     [MP_TAC(ISPEC `c:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^3) IN relative_interior c` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^3) IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `t:real^3->bool`; `c:real^3->bool`] MOI_SSC_FACE_OPP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      UNDISCH_TAC `~((x:real^3) IN UNIONS (moi_ssc_far k a v t1 t2))` THEN
      REWRITE_TAC[] THEN
      REWRITE_TAC[moi_ssc_far; UNIONS_UNION] THEN
      REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM] THEN
      DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `c SUBSET moi_ssc_opp k (v:real^3) t` THEN
      UNDISCH_TAC `(x:real^3) IN c` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `c:real^3->bool`; `x:real^3`] MOI_SSC_FAR_IN_FACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SSC_IN_CONE_SEGS THEN EXISTS_TAC `x0:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x0:real^3) IN UNIONS (moi_ssc_far k a v t1 t2)` THEN
    REWRITE_TAC[moi_ssc_jfam; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c INTER f:real^3->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MAP_EVERY EXISTS_TAC [`c:real^3->bool`; `f:real^3->bool`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `a:real^3`; `t1:real`;
                   `t2:real`; `moi_ssc_stars k (v:real^3)`; `y:real^3`] MOI_SSL_FR_CRIT) THEN
    REWRITE_TAC[GSYM moi_ssc_reg] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[v:real^3,x] SUBSET s /\
                  segment[v,x] SUBSET moi_ssc_reg k a v t1 t2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(MATCH_MP (ASSUME `!x:real^3. x IN UNIONS (moi_ssc_jfam s k a v t1 t2)
                                             ==> segment[v,x] SUBSET s`)
          (ASSUME `(x:real^3) IN UNIONS (moi_ssc_jfam s k a v t1 t2)`)) THEN SIMP_TAC[];
        MATCH_MP_TAC MOI_SSC_REG_STAR THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        UNDISCH_TAC `UNIONS (moi_ssc_far k a v t1 t2) SUBSET moi_ssc_reg k (a:real^3) v t1 t2` THEN
        UNDISCH_TAC `UNIONS (moi_ssc_jfam s k (a:real^3) v t1 t2) SUBSET
                     UNIONS (moi_ssc_far k a v t1 t2)` THEN
        UNDISCH_TAC `(x:real^3) IN UNIONS (moi_ssc_jfam s k a v t1 t2)` THEN SET_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[moi_ssc_stars; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      UNDISCH_TAC `segment[v:real^3,x] SUBSET moi_ssc_reg k a v t1 t2` THEN
      UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN SET_TAC[];
      DISJ1_TAC THEN UNDISCH_TAC `segment[v:real^3,x] SUBSET s` THEN
      UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN SET_TAC[]]]);;

let MOI_SSC_BDY_CASE = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ v IN s
     ==> moi_sch3_simple (frontier (moi_ssc_reg k a v t1 t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_SSC_BDY_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC CONE_DISK_SIMPLE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SSC_BDY_DISK THEN ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SSC_FAR_FACTS) THEN
    REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN MESON_TAC[HULL_INC];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                         `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
                        MOI_SSC_FAR_RADIAL) THEN
    ASM_REWRITE_TAC[]]);;

(* The main theorem: the star statement of the slab step.                    *)

let MOI_SSC_STAR = prove
 (MOI_SSL_STAR_STMT,
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                       `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SSC_N1 THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`; `t1:real`; `t2:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[MOI_SSC_REG_EQ] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
    UNDISCH_TAC `(v:real^3) IN s UNION inside s` THEN REWRITE_TAC[IN_UNION] THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC MOI_SSC_BDY_CASE THEN
      MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SSC_INT_CASE THEN
      MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`] THEN
      ASM_REWRITE_TAC[]]]);;

