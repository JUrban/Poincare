(* ========================================================================= *)
(* pc_moi_s35_mina: Moise GTM 47, Sec 35.1, Lemma 1 (p.250) in chart form    *)
(* (main theorem LEMMA1 = MOI_S35_LEMMA1 of pc_moi_s35_stmt.ml) and the      *)
(* passage from one essential circle to moi_s35_single (main theorem         *)
(* SINGLE_FROM_ONE = MOI_S35_SINGLE_FROM_ONE).                               *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_s27.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_s35_minc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A local surface lemma.  An edge of a simplicial complex (dimensions      *)
(* at most 2) with a point p of its relative interior that has a chart of   *)
(* the polyhedron onto an open subset of R^2 lies in exactly two triangles. *)
(* Local versions of MOI_SCF_OPEN_IMAGE_R2, MOI_SCF_OPEN_SUBSET_RELINT,     *)
(* MOI_SCF_OPEN_DIM_GE, MOI_SCF_UNFOLD, MOI_SCF_SURF_EDGE_NOT1,             *)
(* MOI_SCF_SURF_EDGE_NOT3 and MOI_SCF_SURF_EDGE of pc_moi_smo_cf.ml (which  *)
(* assume the whole polyhedron homeomorphic to S^2); the proofs follow     *)
(* those, with one chart (U,V) instead of the sphere charts.               *)
(* ------------------------------------------------------------------------- *)

(* An injective continuous image of an open subset of R^2 inside the chart *)
(* domain U is open in X (invariance of domain).                           *)

let MOI_S5L_CHART_OPEN_IMAGE = prove
 (`!(X:real^N->bool) U V (phi:real^N->real^2) phi' (W:real^2->bool) f.
     open_in (subtopology euclidean X) U /\ open V /\
     homeomorphism (U,V) (phi,phi') /\
     open W /\ f continuous_on W /\ IMAGE f W SUBSET U /\
     (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y)
     ==> open_in (subtopology euclidean X) (IMAGE f W)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) W =
                IMAGE (phi':real^2->real^N) (IMAGE ((phi:real^N->real^2) o f) W)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`phi:real^N->real^2`; `V:real^2->bool`] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]]);;

(* The phi-image of an open subset of X inside U is open in R^2.           *)

let MOI_S5L_CHART_IMAGE_OPEN = prove
 (`!(X:real^N->bool) U V (phi:real^N->real^2) phi' W0.
     open_in (subtopology euclidean X) U /\ open V /\
     homeomorphism (U,V) (phi,phi') /\
     open_in (subtopology euclidean X) W0 /\ W0 SUBSET U
     ==> open (IMAGE phi W0) /\ IMAGE phi W0 SUBSET V /\
         IMAGE phi' (IMAGE phi W0) = W0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean V) (IMAGE (phi:real^N->real^2) W0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`phi':real^2->real^N`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `X:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_OPEN_TRANS];
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^N. x) W0` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
    MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[]]);;

(* An open subset of X inside U and inside a set of dimension at most 2     *)
(* lies in its relative interior.                                          *)

let MOI_S5L_CHART_SUBSET_RELINT = prove
 (`!(X:real^N->bool) U V (phi:real^N->real^2) phi' W0 s.
     open_in (subtopology euclidean X) U /\ open V /\
     homeomorphism (U,V) (phi,phi') /\
     open_in (subtopology euclidean X) W0 /\ W0 SUBSET U /\ W0 SUBSET s /\
     aff_dim s <= &2
     ==> W0 SUBSET relative_interior s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `U:real^N->bool`; `V:real^2->bool`;
    `phi:real^N->real^2`; `phi':real^2->real^N`; `W0:real^N->bool`]
    MOI_S5L_CHART_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `W0:real^N->bool`)) THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
  EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[AFFINE_UNIV; AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
              AFF_DIM_UNIV; DIMINDEX_2] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `s:real^N->bool`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* An open nonempty subset of X inside U and inside s forces aff_dim s >= 2. *)

let MOI_S5L_CHART_DIM_GE = prove
 (`!(X:real^N->bool) U V (phi:real^N->real^2) phi' W0 s.
     open_in (subtopology euclidean X) U /\ open V /\
     homeomorphism (U,V) (phi,phi') /\
     open_in (subtopology euclidean X) W0 /\ ~(W0 = {}) /\ W0 SUBSET U /\
     W0 SUBSET s
     ==> &2 <= aff_dim s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `U:real^N->bool`; `V:real^2->bool`;
    `phi:real^N->real^2`; `phi':real^2->real^N`; `W0:real^N->bool`]
    MOI_S5L_CHART_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
    concl th = `~(W0:real^N->bool = {})`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
    concl th = `open (IMAGE (phi:real^N->real^2) W0)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:real^N->real^2) y`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`phi':real^2->real^N`; `ball((phi:real^N->real^2) y,r)`;
                 `s:real^N->bool`] INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN) THEN
  ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_2; CONVEX_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_TRANS];
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `s:real^N->bool`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* The unfolding of two triangles on a common edge [a,b] near the point    *)
(* a + t0 (b - a) of the edge (MOI_SCF_UNFOLD centred at any t0 in (0,1)).  *)

let MOI_S5L_UNFOLD_AT = prove
 (`!a b c1 c2:real^N t0.
     ~affine_dependent {a,b,c1} /\ ~affine_dependent {a,b,c2} /\
     ~(a = b) /\ ~(c1 = a) /\ ~(c1 = b) /\ ~(c2 = a) /\ ~(c2 = b) /\
     convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a,b} /\
     &0 < t0 /\ t0 < &1
     ==> ?(f:real^2->real^N) W x.
           open W /\ f continuous_on W /\
           IMAGE f W SUBSET convex hull {a,b,c1} UNION convex hull {a,b,c2} /\
           (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y) /\
           x IN W /\ f x = a + t0 % (b - a)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\p:real^2. a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                         max (--(p$2)) (&0) % (c2 - a:real^N)` THEN
  EXISTS_TAC `ball(vector[t0; &0]:real^2,min t0 (&1 - t0) / &2)` THEN
  EXISTS_TAC `vector[t0; &0]:real^2` THEN
  REWRITE_TAC[OPEN_BALL; MOI_SCF_UNFOLD_CONT] THEN
  SUBGOAL_THEN
   `!p:real^2. p IN ball(vector[t0; &0],min t0 (&1 - t0) / &2)
               ==> &0 <= p$1 /\ abs(p$2) <= &1 - p$1`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^2` THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`vector[t0; &0] - p:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[t0; &0] - p:real^2`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_2; DIMINDEX_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY UNDISCH_TAC [`&0 < t0`; `t0 < &1`] THEN
    UNDISCH_TAC `norm(vector[t0; &0] - p:real^2) < min t0 (&1 - t0) / &2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN BETA_TAC THEN
    X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^2`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `&0 <= (p:real^2)$2` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_SCF_UNFOLD_IN THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN MATCH_MP_TAC MOI_SCF_UNFOLD_IN2 THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC BETA_RULE THEN
    MATCH_MP_TAC MOI_SCF_UNFOLD_INJ THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:real^2`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^2`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CENTRE_IN_BALL] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < t0`; `t0 < &1`] THEN REAL_ARITH_TAC;
    BETA_TAC THEN REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_ARITH `max (&0) (&0) = &0`; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID]]);;

(* The open star of a simplex s of L: points all of whose carriers contain s. *)

let MOI_S5L_STAR_FACTS = prove
 (`!L:(real^N->bool)->bool e p.
     simplicial_complex L /\ e IN L /\ p IN relative_interior e
     ==> open_in (subtopology euclidean (UNIONS L))
           {x | x IN UNIONS L /\ !u. u IN L /\ x IN u ==> e SUBSET u} /\
         p IN {x | x IN UNIONS L /\ !u. u IN L /\ x IN u ==> e SUBSET u}`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `e:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[MOI_SCF_RELINT_SUBSET]]]);;

(* The common hypotheses of the local edge lemmas.                          *)

let moi_s5l_edge_chart = new_definition
 `moi_s5l_edge_chart (L:(real^N->bool)->bool) e p U V (phi:real^N->real^2) phi' <=>
    simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &2) /\
    e IN L /\ aff_dim e = &1 /\ p IN relative_interior e /\
    open_in (subtopology euclidean (UNIONS L)) U /\ p IN U /\ open V /\
    homeomorphism (U,V) (phi,phi')`;;

(* A simplex of L containing a point of the open star of e and of dimension *)
(* at most 2 is e or a triangle on e.                                       *)

let MOI_S5L_STAR_CARRIER = prove
 (`!L e (u:real^N->bool).
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &2) /\
     e IN L /\ aff_dim e = &1 /\ u IN L /\ e SUBSET u
     ==> u = e \/ aff_dim u = &2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `aff_dim(u:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`e:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

(* No triangle on e is impossible.                                          *)

let MOI_S5L_EDGE_NOT0 = prove
 (`!L e (p:real^N) U V (phi:real^N->real^2) phi'.
     moi_s5l_edge_chart L e p U V phi phi' /\
     {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = {}
     ==> F`,
  REWRITE_TAC[moi_s5l_edge_chart] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `p:real^N`]
    MOI_S5L_STAR_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `st = {x:real^N | x IN UNIONS L /\ !u. u IN L /\ x IN u ==> e SUBSET u}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(st:real^N->bool) SUBSET e` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
      (MP_TAC o SPEC `u:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `u:real^N->bool`]
      MOI_S5L_STAR_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `{t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = {}:(real^N->bool)->bool` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `U:real^N->bool`; `V:real^2->bool`;
    `phi:real^N->real^2`; `phi':real^2->real^N`; `st INTER U:real^N->bool`;
    `e:real^N->bool`] MOI_S5L_CHART_DIM_GE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* Exactly one triangle on e is impossible.                                 *)

let MOI_S5L_EDGE_NOT1 = prove
 (`!L e (p:real^N) U V (phi:real^N->real^2) phi' t1.
     moi_s5l_edge_chart L e p U V phi phi' /\
     {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = {t1}
     ==> F`,
  REWRITE_TAC[moi_s5l_edge_chart] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t1 IN L /\ aff_dim t1 = &2 /\ (e:real^N->bool) SUBSET t1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = {t1:real^N->bool}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `t1:real^N->bool`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `p:real^N`]
    MOI_S5L_STAR_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `st = {x:real^N | x IN UNIONS L /\ !u. u IN L /\ x IN u ==> e SUBSET u}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(st:real^N->bool) SUBSET t1` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
      (MP_TAC o SPEC `u:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `u:real^N->bool`]
      MOI_S5L_STAR_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      UNDISCH_TAC `{t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = {t1:real^N->bool}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `U:real^N->bool`; `V:real^2->bool`;
    `phi:real^N->real^2`; `phi':real^2->real^N`; `st INTER U:real^N->bool`;
    `t1:real^N->bool`] MOI_S5L_CHART_SUBSET_RELINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      INT_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) INTER relative_interior t1 = {}` MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_DISJOINT_RELATIVE_INTERIOR THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_SUBSET_FACE];
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`st INTER U SUBSET relative_interior (t1:real^N->bool)`;
      `(p:real^N) IN st`; `(p:real^N) IN U`; `(p:real^N) IN relative_interior e`] THEN
    SET_TAC[]]);;

(* Three triangles on e are impossible: two of them unfold near p to an    *)
(* open subset of X, which the third approaches.                           *)

let MOI_S5L_EDGE_NOT3 = prove
 (`!L e (p:real^N) U V (phi:real^N->real^2) phi' t1 t2 t3.
     moi_s5l_edge_chart L e p U V phi phi' /\
     t1 IN L /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
     t2 IN L /\ aff_dim t2 = &2 /\ e SUBSET t2 /\
     t3 IN L /\ aff_dim t3 = &2 /\ e SUBSET t3 /\
     ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3)
     ==> F`,
  REWRITE_TAC[moi_s5l_edge_chart] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `t1:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `t2:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c1:real^N = c2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(t1:real^N->bool = t2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a:real^N,b}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{a:real^N,b,c1}`;
                   `{a:real^N,b,c2}`] MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t0. &0 < t0 /\ t0 < &1 /\ p = a + t0 % (b - a:real^N)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^N) IN relative_interior e` THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT] THEN
    REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN EXISTS_TAC `u:real` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`; `t0:real`]
    MOI_S5L_UNFOLD_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `W:real^2->bool`
    (X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `W' = {z:real^2 | z IN W /\ (f:real^2->real^N) z IN U}` THEN
  SUBGOAL_THEN `open (W':real^2->bool) /\ W' SUBSET W /\ x0 IN W' /\
                IMAGE (f:real^2->real^N) W' SUBSET U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `W:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "W'" THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
      EXISTS_TAC `UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET
                   convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
      UNDISCH_TAC `(t1:real^N->bool) IN L` THEN
      UNDISCH_TAC `(t2:real^N->bool) IN L` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXPAND_TAC "W'" THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `U:real^N->bool`; `V:real^2->bool`;
    `phi:real^N->real^2`; `phi':real^2->real^N`; `W':real^2->bool`;
    `f:real^2->real^N`] MOI_S5L_CHART_OPEN_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^2->real^N) x0` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^2->real^N) x0 IN closure(relative_interior t3)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`]
      MOI_CON_SC_CONVEX) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`]
      MOI_SCF_SC_CLOSED) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^N) IN t3` MP_TAC THENL
     [MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(p:real^N) IN relative_interior e` THEN
      UNDISCH_TAC `(e:real^N->bool) SUBSET t3` THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (f:real^2->real^N) W'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t3:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`;
                 `t1:real^N->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`;
                 `t2:real^N->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET
               convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
  UNDISCH_TAC `(y:real^N) IN IMAGE (f:real^2->real^N) W'` THEN
  UNDISCH_TAC `(y:real^N) IN relative_interior t3` THEN
  UNDISCH_TAC `(W':real^2->bool) SUBSET W` THEN
  SUBGOAL_THEN `~(t3:real^N->bool = t1) /\ ~(t3 = t2)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* Every edge with a chart point in its relative interior lies in exactly   *)
(* two triangles.                                                            *)

let MOI_S5L_EDGE_TWO = prove
 (`!L e (p:real^N) U V (phi:real^N->real^2) phi'.
     moi_s5l_edge_chart L e p U V phi phi'
     ==> CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s5l_edge_chart]) THEN
  ABBREV_TAC `ts = {t:real^N->bool | t IN L /\ aff_dim t = &2 /\ e SUBSET t}` THEN
  SUBGOAL_THEN `FINITE (ts:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(ts:(real^N->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5L_EDGE_NOT0 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `e:real^N->bool`; `p:real^N`;
      `U:real^N->bool`; `V:real^2->bool`; `phi:real^N->real^2`;
      `phi':real^2->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(ts:(real^N->bool)->bool) = 1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(ts:(real^N->bool)->bool) HAS_SIZE 1` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_TAC `t1:real^N->bool`) THEN
    MATCH_MP_TAC MOI_S5L_EDGE_NOT1 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `e:real^N->bool`; `p:real^N`;
      `U:real^N->bool`; `V:real^2->bool`; `phi:real^N->real^2`;
      `phi':real^2->real^N`; `t1:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(3 <= CARD(ts:(real^N->bool)->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `ts:(real^N->bool)->bool` CHOOSE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `3`) THEN
    ASM_REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
       (X_CHOOSE_THEN `t3:real^N->bool` STRIP_ASSUME_TAC)))) THEN
    MATCH_MP_TAC MOI_S5L_EDGE_NOT3 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `e:real^N->bool`; `p:real^N`;
      `U:real^N->bool`; `V:real^2->bool`; `phi:real^N->real^2`;
      `phi':real^2->real^N`; `t1:real^N->bool`; `t2:real^N->bool`;
      `t3:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:(real^N->bool)->bool) SUBSET ts` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The level complex of a complex of dimension at most 2 at a level t      *)
(* through no vertex.  Adapted from MOI_SLV_LEVEL_DIM, MOI_SLV_LEVEL_CARRIER, *)
(* MOI_SLV_TRI_CROSS, MOI_SLV_LEVEL_EDGES_AT and MOI_SLV_LEVEL_GRAPH2 of    *)
(* pc_moi_sch3_lev.ml (there for a generic height on a PL 2-sphere and the  *)
(* level of a vertex); here the edges crossing the level are assumed to lie *)
(* in exactly two triangles.                                                 *)
(* ------------------------------------------------------------------------- *)

(* A simplex of dimension at most 2 with no vertex at level t meets the     *)
(* level in a set of dimension at most 1.                                    *)

let MOI_S5L_SLICE_DIM = prove
 (`!K (a:real^3) t s.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
     (!w. {w} IN K ==> ~(a dot w = t)) /\ s IN K
     ==> aff_dim (s INTER {x | a dot x = t}) <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(s:real^3->bool) <= &2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real^3->bool = {}` THENL
   [ASM_REWRITE_TAC[INTER_EMPTY; AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `s:real^3->bool`] MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w:real^3. w IN V` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(s:real^3->bool = {})` THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^3} IN K` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLV_SC_VERTEX_SING THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(affine hull s SUBSET {x:real^3 | a dot x = t})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN affine hull s` MP_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `affine hull s SUBSET {x:real^3 | a dot x = t}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(fun th -> DISCH_THEN
        (MP_TAC o MATCH_MP th)) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `aff_dim(affine hull s INTER {x:real^3 | a dot x = t})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC AFF_DIM_SUBSET THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `s:real^3->bool`] HULL_SUBSET) THEN
    SET_TAC[];
    SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFFINE_AFFINE_HULL] THEN
    ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(s:real^3->bool) <= &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC]);;

(* The level complex.                                                        *)

let MOI_S5L_LEVEL_COMPLEX = prove
 (`!K (a:real^3) t.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
     (!w. {w} IN K ==> ~(a dot w = t))
     ==> simplicial_complex {s INTER {x | a dot x = t} | s IN K} /\
         (!s. s IN {s INTER {x | a dot x = t} | s IN K} ==> aff_dim s <= &1) /\
         UNIONS {s INTER {x | a dot x = t} | s IN K} =
         UNIONS K INTER {x | a dot x = t}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLV_SLICE_COMPLEX THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5L_SLICE_DIM THEN
    EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_S5L_SLICE_DIM THEN
    EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTER_UNIONS]]);;
(* A point of the level complex that is a whole slice is the crossing point *)
(* of an edge with one end below and one end above the level.               *)

let MOI_S5L_LEVEL_CARRIER = prove
 (`!K (a:real^3) t s p.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
     (!w. {w} IN K ==> ~(a dot w = t)) /\ s IN K /\
     s INTER {x | a dot x = t} = {p}
     ==> ?w1 w2. segment[w1,w2] IN K /\ a dot w1 < t /\ t < a dot w2 /\
                 segment[w1,w2] INTER {x | a dot x = t} = {p} /\
                 p IN segment(w1,w2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `(p:real^3) IN s /\ a dot p = t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s INTER {x:real^3 | a dot x = t} = {p}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `p:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->bool) IN K` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `e INTER {x:real^3 | a dot x = t} = {p}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `e:real^3->bool`] FACE_OF_IMP_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    UNDISCH_TAC `s INTER {x:real^3 | a dot x = t} = {p}` THEN
    UNDISCH_TAC `(p:real^3) IN e` THEN UNDISCH_TAC `a dot (p:real^3) = t` THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(e:real^3->bool) = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim(e:real^3->bool) <= &2` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = -- &1)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` SUBST_ALL_TAC) THEN
      SUBGOAL_THEN `q:real^3 = p` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `(p:real^3) IN {q}` THEN REWRITE_TAC[IN_SING] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `t:real`)) (concl th) &&
        can (find_term is_neg) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = &2)` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`e:real^3->bool`; `a:real^3`; `t:real`; `p:real^3`]
        MOI_SLV_RELINT_SLICE_TWO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[INT_LE_REFL] THEN ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `e INTER {x:real^3 | a dot x = t} = {p}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `e:real^3->bool` AFF_DIM_GE) THEN
    SPEC_TAC(`aff_dim(e:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `e:real^3->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN segment(w1,w2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN relative_interior(segment[w1,w2])` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a dot (w1:real^3) = t) /\ ~(a dot (w2:real^3) = t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?u. &0 < u /\ u < &1 /\ p = (&1 - u) % w1 + u % (w2:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN segment(w1,w2)` THEN
    REWRITE_TAC[IN_SEGMENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - u) * a dot (w1:real^3) + u * a dot w2 = t`
  ASSUME_TAC THENL
   [UNDISCH_TAC `a dot (p:real^3) = t` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL];
    ALL_TAC] THEN
  ASM_CASES_TAC `a dot (w1:real^3) < t` THENL
   [MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLV_CONVEX_SIGN THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `a dot (w1:real^3)`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`w2:real^3`; `w1:real^3`] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--c < --y ==> y < c`) THEN
      MATCH_MP_TAC MOI_SLV_CONVEX_SIGN THEN
      MAP_EVERY EXISTS_TAC [`u:real`; `--(a dot (w1:real^3))`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(&1 - u) * a dot (w1:real^3) + u * a dot w2 = t` THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;
(* A triangle on a crossing edge meets the level in a segment.              *)

let MOI_S5L_TRI_CROSS = prove
 (`!K (a:real^3) t w1 w2 tau p.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
     (!w. {w} IN K ==> ~(a dot w = t)) /\
     segment[w1,w2] IN K /\ a dot w1 < t /\ t < a dot w2 /\
     segment[w1,w2] INTER {x | a dot x = t} = {p} /\
     tau IN K /\ aff_dim tau = &2 /\ segment[w1,w2] SUBSET tau
     ==> aff_dim(tau INTER {x | a dot x = t}) = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `(p:real^3) IN segment[w1,w2] /\ a dot p = t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = t} = {p}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w1:real^3 = w2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                 `tau:real^3->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w3:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `segment[w1:real^3,w3] IN K /\ segment[w3,w2] IN K /\ {w3} IN K`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `(face_of):(real^3->bool)->(real^3->bool)->bool`))
        (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THENL
     [EXISTS_TAC `{w1:real^3,w3}`; EXISTS_TAC `{w3:real^3,w2}`;
      EXISTS_TAC `{w3:real^3}` THEN REWRITE_TAC[CONVEX_HULL_SING]] THEN
    REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a dot (w3:real^3) = t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t:real`)) (concl th) &&
      can (find_term is_neg) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?q:real^3. ~(q = p) /\ q IN tau /\ a dot q = t`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `a dot (w3:real^3) < t` THENL
     [MP_TAC(ISPECL [`a:real^3`; `t:real`; `w3:real^3`; `w2:real^3`]
        MOI_SLV_CROSS_SING) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^3` THEN
      SUBGOAL_THEN `(q:real^3) IN segment[w3,w2] /\ a dot q = t`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w3:real^3,w2] INTER {z | a dot z = t} = {q}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                       `w3:real^3`; `w2:real^3`] MOI_SLV_SEGMENTS_INTER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[SEGMENT_EQ] THEN
          REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `w1:real^3`) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(q:real^3) IN segment[w3,w2]` THEN
        SPEC_TAC(`q:real^3`,`q:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]];
      MP_TAC(ISPECL [`a:real^3`; `t:real`; `w1:real^3`; `w3:real^3`]
        MOI_SLV_CROSS_SING) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^3` THEN
      SUBGOAL_THEN `(q:real^3) IN segment[w1,w3] /\ a dot q = t`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w1:real^3,w3] INTER {z | a dot z = t} = {q}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                       `w1:real^3`; `w3:real^3`] MOI_SLV_SEGMENTS_INTER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[SEGMENT_EQ] THEN
          REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `w2:real^3`) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(q:real^3) IN segment[w1,w3]` THEN
        SPEC_TAC(`q:real^3`,`q:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a <= &1 ==> a:int = &1`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{p:real^3,q}`; `tau INTER {x:real^3 | a dot x = t}`]
      AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      ASM_REWRITE_TAC[AFF_DIM_2] THEN COND_CASES_TAC THEN
      ASM_MESON_TAC[INT_LE_REFL]];
    MATCH_MP_TAC MOI_S5L_SLICE_DIM THEN
    EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]]);;
(* With two triangles on every crossing edge, every vertex of the level     *)
(* complex lies on exactly two of its edges.                                 *)

let MOI_S5L_LEVEL_EDGES_AT = prove
 (`!K (a:real^3) t p.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
     (!w. {w} IN K ==> ~(a dot w = t)) /\
     (!w1 w2. segment[w1,w2] IN K /\ a dot w1 < t /\ t < a dot w2
              ==> {tau | tau IN K /\ aff_dim tau = &2 /\ segment[w1,w2] SUBSET tau}
                  HAS_SIZE 2) /\
     {p} IN {s INTER {x | a dot x = t} | s IN K}
     ==> {s | s IN {s INTER {x | a dot x = t} | s IN K} /\
              aff_dim s = &1 /\ p IN s} HAS_SIZE 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s0:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM)) o
    REWRITE_RULE[IN_ELIM_THM] o check (fun th -> aconv (concl th)
      `{p:real^3} IN {s INTER {x | a dot x = t} | s IN K}`)) THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `a:real^3`; `t:real`;
                 `s0:real^3->bool`; `p:real^3`] MOI_S5L_LEVEL_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(w1:real^3 = w2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{tau:real^3->bool | tau IN K /\ aff_dim tau = &2 /\
                                    segment[w1,w2] SUBSET tau} HAS_SIZE 2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN {s INTER {x | a dot x = t} | s IN K} /\
         aff_dim s = &1 /\ p IN s} =
    IMAGE (\tau:real^3->bool. tau INTER {x | a dot x = t})
      {tau:real^3->bool | tau IN K /\ aff_dim tau = &2 /\ segment[w1,w2] SUBSET tau}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `sig:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool`
        STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `sig:real^3->bool`)) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[w1:real^3,w2] SUBSET s` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `p:real^3`] THEN
        ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN ASM_MESON_TAC[IN_INTER];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim(s:real^3->bool) <= &2` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= aff_dim(s:real^3->bool)` MP_TAC THENL
       [MP_TAC(ISPECL [`segment[w1:real^3,w2]`; `s:real^3->bool`] AFF_DIM_SUBSET) THEN
        ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(aff_dim(s:real^3->bool) = &1)` MP_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `segment[w1:real^3,w2] = s` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
          EXISTS_TAC `K:(real^3->bool)->bool` THEN
          ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
          ALL_TAC] THEN
        UNDISCH_TAC `aff_dim (s INTER {x:real^3 | a dot x = t}) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      SPEC_TAC(`aff_dim(s:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `tau:real^3->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `sig:real^3->bool`)) THEN
      CONJ_TAC THENL [EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5L_TRI_CROSS THEN
        MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `w1:real^3`;
                              `w2:real^3`; `p:real^3`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = t} = {p}` THEN
        UNDISCH_TAC `segment[w1:real^3,w2] SUBSET tau` THEN SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^3->bool`; `t2:real^3->bool`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim(t1 INTER {x:real^3 | a dot x = t}) = &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5L_TRI_CROSS THEN
    MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `w1:real^3`;
                          `w2:real^3`; `p:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `t1:real^3->bool`; `t2:real^3->bool`]
    MOI_SLV_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1 INTER t2:real^3->bool = segment[w1,w2]` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `K:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET_INTER; AFF_DIM_SEGMENT] THEN
    MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a < &2 ==> &1 = a:int`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`segment[w1:real^3,w2]`; `t1 INTER t2:real^3->bool`]
        AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_INTER; AFF_DIM_SEGMENT];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `aff_dim(t1:real^3->bool) = &2`)) THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(t1:real^3->bool = t2)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t1 INTER t2:real^3->bool = t1` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `aff_dim(t1 INTER {x:real^3 | a dot x = t}) = &1` THEN
  SUBGOAL_THEN `t1 INTER {x:real^3 | a dot x = t} = {p}` SUBST1_TAC THENL
   [UNDISCH_TAC `t1 INTER {x:real^3 | a dot x = t} =
                 t2 INTER {x | a dot x = t}` THEN
    UNDISCH_TAC `t1 INTER t2:real^3->bool = segment[w1,w2]` THEN
    UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = t} = {p}` THEN
    UNDISCH_TAC `segment[w1:real^3,w2] SUBSET t1` THEN SET_TAC[];
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC]);;

(* The level complex is a degree-2 graph (with any marked point).           *)

let MOI_S5L_LEVEL_GRAPH2 = prove
 (`!K (a:real^3) t.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
     (!w. {w} IN K ==> ~(a dot w = t)) /\
     (!w1 w2. segment[w1,w2] IN K /\ a dot w1 < t /\ t < a dot w2
              ==> {tau | tau IN K /\ aff_dim tau = &2 /\ segment[w1,w2] SUBSET tau}
                  HAS_SIZE 2)
     ==> !v. moi_slv_graph2 {s INTER {x | a dot x = t} | s IN K} v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `a:real^3`; `t:real`]
    MOI_S5L_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_slv_graph2] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5L_LEVEL_EDGES_AT THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The components of a 1-dimensional complex in which every vertex lies     *)
(* on exactly two edges are its PL circles, and there are finitely many.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S5L_CIRCLE_BASIC = prove
 (`!q:real^N->bool. pl_sphere 1 q ==> compact q /\ connected q /\ ~(q = {})`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[COMPACT_PATH_IMAGE; CONNECTED_PATH_IMAGE; PATH_IMAGE_NONEMPTY;
                SIMPLE_PATH_IMP_PATH]);;

(* Every point of the graph lies on an edge.                                *)

let MOI_S5L_G2_EDGE_THROUGH = prove
 (`!G (x:real^N).
     simplicial_complex G /\ (!s. s IN G ==> aff_dim s <= &1) /\
     (!v. moi_slv_graph2 G v) /\ x IN UNIONS G
     ==> ?s. s IN G /\ aff_dim s = &1 /\ x IN s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  SUBGOAL_THEN `aff_dim(s0:real^N->bool) <= &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(s0:real^N->bool) = &1` THENL
   [EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s0 = {x:real^N}` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `aff_dim(s0:real^N->bool) <= &0` MP_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MOI_S5C_AFF_DIM_LE0] THEN STRIP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + basis 1:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `moi_slv_graph2:((real^N->bool)->bool)->real^N->bool`)) (concl th))) THEN
  REWRITE_TAC[moi_slv_graph2] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS) THEN
  ASM_SIMP_TAC[VECTOR_ARITH `x = x + b <=> b = vec 0:real^N`; BASIS_NONZERO;
               DIMINDEX_GE_1; LE_REFL] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s1:real^N->bool` THEN
  UNDISCH_TAC `{s | s IN G /\ aff_dim s = &1 /\ (x:real^N) IN s} = {s1,s2}` THEN
  SET_TAC[]);;
(* Every point of the graph lies on a PL circle in it; two such circles     *)
(* meeting are equal; each is open in the graph.                             *)

let MOI_S5L_G2_CIRCLE_THROUGH = prove
 (`!G (x:real^3).
     simplicial_complex G /\ (!s. s IN G ==> aff_dim s <= &1) /\
     (!v. moi_slv_graph2 G v) /\ x IN UNIONS G
     ==> ?q. pl_sphere 1 q /\ q SUBSET UNIONS G /\ x IN q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(real^3->bool)->bool`; `x:real^3`] MOI_S5L_G2_EDGE_THROUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:(real^3->bool)->bool`; `s:real^3->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`G:(real^3->bool)->bool`; `u:real^3`; `s:real^3->bool`]
    MOI_SLV_G2_COVER) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^3->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S5L_G2_CIRCLES_DISJOINT = prove
 (`!G (p:real^3->bool) q x.
     simplicial_complex G /\ (!v. moi_slv_graph2 G v) /\
     pl_sphere 1 p /\ pl_sphere 1 q /\ p SUBSET UNIONS G /\ q SUBSET UNIONS G /\
     x IN p /\ x IN q
     ==> p = q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_G2_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`G:(real^3->bool)->bool`; `x + basis 1:real^3`; `x:real^3`] THEN
  ASM_SIMP_TAC[VECTOR_ARITH `x = x + b <=> b = vec 0:real^3`; BASIS_NONZERO;
               DIMINDEX_3; ARITH]);;

let MOI_S5L_G2_CIRCLE_OPEN = prove
 (`!G (q:real^3->bool).
     simplicial_complex G /\ (!v. moi_slv_graph2 G v) /\
     pl_sphere 1 q /\ q SUBSET UNIONS G
     ==> open_in (subtopology euclidean (UNIONS G)) q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?v:real^3. ~(v IN UNIONS G)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `bounded (UNIONS G:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
      ASM_MESON_TAC[MOI_SCF_SC_FINITE; MOI_CON_SC_COMPACT];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> ~q) ==> q ==> p`) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `UNIONS G = (:real^3)` (fun th -> REWRITE_TAC[th; NOT_BOUNDED_UNIV]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(real^3->bool)->bool`; `v:real^3`; `q:real^3->bool`]
    MOI_SLV_G2_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `UNIONS G DELETE (v:real^3) = UNIONS G /\ q DELETE v = q`
    (fun th -> REWRITE_TAC[th] THEN SIMP_TAC[]) THEN
  ASM SET_TAC[]);;
(* The components of the graph are exactly its PL circles.                  *)

let MOI_S5L_G2_COMPONENTS = prove
 (`!G:(real^3->bool)->bool.
     simplicial_complex G /\ (!s. s IN G ==> aff_dim s <= &1) /\
     (!v. moi_slv_graph2 G v)
     ==> components (UNIONS G) = {q | pl_sphere 1 q /\ q SUBSET UNIONS G} /\
         FINITE (components (UNIONS G))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!q:real^3->bool. pl_sphere 1 q /\ q SUBSET UNIONS G ==> q IN components (UNIONS G)`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^3->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5L_CIRCLE_BASIC) THEN
    REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `d:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `d:real^3->bool` CONNECTED_CLOPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q:real^3->bool`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS G:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_S5L_G2_CIRCLE_OPEN THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `components (UNIONS G) = {q:real^3->bool | pl_sphere 1 q /\ q SUBSET UNIONS G}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?x:real^3. x IN k` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`UNIONS G:real^3->bool`; `k:real^3->bool`]
          IN_COMPONENTS_NONEMPTY) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN UNIONS G` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`UNIONS G:real^3->bool`; `k:real^3->bool`]
          IN_COMPONENTS_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`G:(real^3->bool)->bool`; `x:real^3`] MOI_S5L_G2_CIRCLE_THROUGH) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(q:real^3->bool) IN components (UNIONS G)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `k:real^3->bool = q` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MP_TAC(ISPECL [`UNIONS G:real^3->bool`; `k:real^3->bool`; `q:real^3->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN UNDISCH_TAC `(x:real^3) IN q` THEN
      SET_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SLV_CIRCLES_FINITE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The setting of an edge configuration: B = phi^-1(b), its PL              *)
(* parametrization by the square annulus, its triangulation, the flatness  *)
(* of the circles.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5L_SETUP = prove
 (`!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> ?K (FF:real^2->real^3) GG psi.
           {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} SUBSET interior moi_s35_stube /\ compact {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} /\
           pl_homeomorphism ({x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b},b) (phi,psi) /\
           pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}) (FF,GG) /\
           IMAGE phi (IMAGE FF (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0 /\ IMAGE phi (IMAGE FF (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1 /\
           FINITE K /\ simplicial_complex K /\ UNIONS K = {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} /\
           (!v. {v} IN K ==> ~(v$3 = c)) /\ (!s. s IN K ==> aff_dim s <= &2) /\
           (moi_s35_circles (phi:real^3->real^3) b c) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c} /\ (moi_s35_circles (phi:real^3->real^3) b c) = {x | x IN {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} /\ x$3 = c}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf]) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `b:real^3->bool`] MOI_S5C_B_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} /\ compact {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_polyhedron {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` ASSUME_TAC THENL
     [REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
      EXISTS_TAC `k:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`; `phi:real^3->real^3`] MOI_S5C_PL_EMBED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:real^3->real^3`) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[pl_annulus_with_ends] o check
    (MOI_S5C_HEAD "pl_annulus_with_ends")) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b})
      ((psi:real^3->real^3) o (f:real^2->real^3),(g:real^3->real^2) o (phi:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `b:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN b ==> (phi:real^3->real^3) (psi y) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) SUBSET b /\ IMAGE (f:real^2->real^3) (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) SUBSET b`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_S5C_A0_FACTS THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[homeomorphism] o
      CONJUNCT1 o REWRITE_RULE[pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),b) (f:real^2->real^3,g)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`;
    `(psi:real^3->real^3) o (f:real^2->real^3)`;
    `(g:real^3->real^2) o (phi:real^3->real^3)`; `psi:real^3->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[IMAGE_o] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `b0:real^3->bool`)) THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) SUBSET b` THEN
    UNDISCH_TAC `!y. y IN b ==> (phi:real^3->real^3) (psi y) = y` THEN SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `b1:real^3->bool`)) THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) SUBSET b` THEN
    UNDISCH_TAC `!y. y IN b ==> (phi:real^3->real^3) (psi y) = y` THEN SET_TAC[];
    MATCH_MP_TAC MOI_S5C_NO_3DIM THEN
    MAP_EVERY EXISTS_TAC [`(g:real^3->real^2) o (phi:real^3->real^3)`; `{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
    MATCH_MP_TAC MOI_S5C_CIRCLES_FLAT THEN
    MAP_EVERY EXISTS_TAC [`xa:real^3->bool`; `xb:real^3->bool`] THEN
    ASM_SIMP_TAC[MOI_S5C_PL_BALL_3_FILL; COMPACT_IMP_CLOSED] THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s35_circles; EXTENSION; IN_ELIM_THM; CONJ_ASSOC]]);;
(* The square annulus minus its two boundary squares (an open subset of R^2). *)

let MOI_S5L_A0_OPEN = prove
 (`(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) =
   interval(--vector[&2;&2]:real^2,vector[&2;&2]) DIFF
   interval[--vector[&1;&1]:real^2,vector[&1;&1]] /\
   open (interval(--vector[&2;&2]:real^2,vector[&2;&2]) DIFF
         interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; MOI_S5C_IN_SQANN; MOI_S5C_IN_RF1;
                MOI_S5C_IN_RF2; MOI_S5C_IN_SQO; MOI_S5C_IN_SQI] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERVAL; CLOSED_INTERVAL]]);;

(* With the setting of MOI_S5L_SETUP, every edge of K crossing the level c  *)
(* lies in exactly two triangles of K (the chart at its crossing point is  *)
(* FF on the open square annulus).                                          *)

let MOI_S5L_K_CROSS_TWO = prove
 (`!phi xa xb ww b b0 b1 c K (FF:real^2->real^3) GG.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}) (FF,GG) /\
     IMAGE phi (IMAGE FF (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0 /\ IMAGE phi (IMAGE FF (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1 /\
     simplicial_complex K /\ UNIONS K = {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} /\
     (!s. s IN K ==> aff_dim s <= &2) /\ (moi_s35_circles (phi:real^3->real^3) b c) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c} /\
     (moi_s35_circles (phi:real^3->real^3) b c) = {x | x IN {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} /\ x$3 = c}
     ==> !w1 w2. segment[w1,w2] IN K /\ basis 3 dot w1 < c /\ c < basis 3 dot w2
                 ==> {tau | tau IN K /\ aff_dim tau = &2 /\ segment[w1,w2] SUBSET tau}
                     HAS_SIZE 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
    (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
  MP_TAC(ISPECL [`basis 3:real^3`; `c:real`; `w1:real^3`; `w2:real^3`]
    MOI_SLV_CROSS_SING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(w1:real^3 = w2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN (moi_s35_circles (phi:real^3->real^3) b c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(p:real^3) IN UNIONS K` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[w1:real^3,w2]` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
        ASM_REWRITE_TAC[IN_ELIM_THM]];
      UNDISCH_TAC `segment[w1:real^3,w2] INTER {z | basis 3 dot z = c} = {p}` THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `V = interval(--vector[&2;&2]:real^2,vector[&2;&2]) DIFF
                  interval[--vector[&1;&1]:real^2,vector[&1;&1]]` THEN
  SUBGOAL_THEN `open (V:real^2->bool) /\ (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = V`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[MOI_S5L_A0_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}) ((FF:real^2->real^3),GG)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(V:real^2->bool) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` ASSUME_TAC THENL
   [UNDISCH_TAC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = V` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}) (IMAGE (FF:real^2->real^3) V) /\
    homeomorphism (IMAGE (FF:real^2->real^3) V,V) (GG,FF)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`GG:real^3->real^2`; `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`; `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`!x. x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) ==> (GG:real^3->real^2) ((FF:real^2->real^3) x) = x`;
        `IMAGE (FF:real^2->real^3) (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) = {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`; `(V:real^2->bool) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN IMAGE (FF:real^2->real^3) V` ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^3) IN {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN (moi_s35_circles (phi:real^3->real^3) b c)` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((phi:real^3->real^3) p IN b0 UNION b1)` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (b0 UNION b1) (IMAGE (phi:real^3->real^3) moi_s35_ttube)` THEN
      MATCH_MP_TAC(SET_RULE `!x:real^3. x IN t ==> DISJOINT s t ==> ~(x IN s)`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(p:real^3) IN (moi_s35_circles (phi:real^3->real^3) b c)` THEN UNDISCH_TAC `(moi_s35_circles (phi:real^3->real^3) b c) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}` THEN
      UNDISCH_TAC `abs c <= &1 / &512` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s35_ttube] THEN
      MESON_TAC[REAL_LT_IMP_LE; REAL_ARITH `abs c <= &1 / &512 ==> abs c <= &1 / &32`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(FF:real^2->real^3) (GG p) = p` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(GG:real^3->real^2) p` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = V` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_DIFF; IN_UNION] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` THEN
      UNDISCH_TAC `IMAGE (GG:real^3->real^2) {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} = (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((phi:real^3->real^3) p IN b0 UNION b1)` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) (IMAGE FF (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0` THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) (IMAGE FF (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MAP_EVERY UNDISCH_TAC
     [`(FF:real^2->real^3) (GG p) = p`;
      `(GG:real^3->real^2) p IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) \/ GG p IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5L_EDGE_TWO THEN
  MAP_EVERY EXISTS_TAC [`p:real^3`; `IMAGE (FF:real^2->real^3) V`; `V:real^2->bool`;
    `GG:real^3->real^2`; `FF:real^2->real^3`] THEN
  REWRITE_TAC[moi_s5l_edge_chart] THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT]);;
(* The circles of an edge configuration: finitely many components, each the *)
(* lift of a planar PL circle.                                               *)

let MOI_S5L_LEVEL_STRUCTURE = prove
 (`!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> FINITE (components (moi_s35_circles (phi:real^3->real^3) b c)) /\
         components (moi_s35_circles (phi:real^3->real^3) b c) = {q | pl_sphere 1 q /\ q SUBSET (moi_s35_circles (phi:real^3->real^3) b c)} /\
         (!k. k IN components (moi_s35_circles (phi:real^3->real^3) b c)
              ==> pl_sphere 1 (IMAGE moi_s5c_proj k) /\
                  k = IMAGE (moi_s35_lift c) (IMAGE moi_s5c_proj k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5L_SETUP) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `psi:real^3->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`; `GG:real^3->real^2`] MOI_S5L_K_CROSS_TWO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN K ==> ~(basis 3 dot w = c)` ASSUME_TAC THENL
   [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `basis 3:real^3`; `c:real`]
    MOI_S5L_LEVEL_COMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `basis 3:real^3`; `c:real`]
    MOI_S5L_LEVEL_GRAPH2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `{s INTER {x:real^3 | basis 3 dot x = c} | s IN K}`
    MOI_S5L_G2_COMPONENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s INTER {x:real^3 | basis 3 dot x = c} | s IN K} = (moi_s35_circles (phi:real^3->real^3) b c)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^3->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN k ==> x$3 = c` ASSUME_TAC THENL
   [UNDISCH_TAC `k SUBSET {x:real^3 | (x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b) /\
                                      x$3 = c}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `c:real`] MOI_S5C_LEVEL_PLH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON]; STRIP_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:real^3->bool`; `IMAGE moi_s5c_proj (k:real^3->bool)`;
                    `moi_s5c_proj`; `moi_s35_lift c`] MOI_S5C_SPHERE1_TO_PLANE) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) k` THEN
    CONJ_TAC THENL [REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[MOI_S5C_PROJ_LIFT]]);;

(* LEMMA1 parts 1 and 2.                                                     *)

let MOI_S5L_LEMMA1_STRUCT = prove
 (`!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> FINITE (components (moi_s35_circles phi b c)) /\
         (!k. k IN components (moi_s35_circles phi b c)
              ==> ?j:real^2->bool. pl_sphere 1 j /\ k = IMAGE (moi_s35_lift c) j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S5L_LEVEL_STRUCTURE) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE moi_s5c_proj (k:real^3->bool)` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Crossing arguments in the level plane.                                   *)
(* ------------------------------------------------------------------------- *)

(* The lift of the closed square n <= 5/16 at the level c lies in the open  *)
(* box moi_s5c_u and in dom.                                                 *)

let MOI_S5L_LIFT_Q5 = prove
 (`!c (y:real^2).
     abs c <= &1 / &512 /\ y IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])
     ==> moi_s35_lift c y IN moi_s5c_u /\ moi_s35_lift c y IN moi_s35_dom /\
         (moi_s35_lift c y)$3 = c /\
         moi_s35_n (moi_s35_lift c y) = max (abs(y$1)) (abs(y$2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S5C_IN_SQI] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_S5C_IN_U; moi_s35_dom; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL;
              moi_s35_lift; moi_s35_n; VECTOR_3; DIMINDEX_3; FORALL_3;
              VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

(* A connected planar set in the square n <= 5/16 whose lift at level c     *)
(* goes from xb to its complement under phi meets the circles.              *)

let MOI_S5L_CROSS = prove
 (`!phi xa xb ww b b0 b1 c (G:real^2->bool) y1 y2.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     connected G /\ G SUBSET (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) /\ y1 IN G /\ y2 IN G /\
     phi (moi_s35_lift c y1) IN xb /\ ~(phi (moi_s35_lift c y2) IN xb)
     ==> ?y. y IN G /\ moi_s35_lift c y IN moi_s35_circles phi b c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
    (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
  SUBGOAL_THEN `!y:real^2. y IN G
      ==> moi_s35_lift c y IN moi_s5c_u /\ moi_s35_lift c y IN moi_s35_dom /\
          (moi_s35_lift c y)$3 = c`
  (LABEL_TAC "lift") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:real`; `y:real^2`] MOI_S5L_LIFT_Q5) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE ((phi:real^3->real^3) o moi_s35_lift c) G)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MP_TAC(SPEC `c:real` MOI_S5C_LIFT_LINEAR) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE ((phi:real^3->real^3) o moi_s35_lift c) G`; `xb:real^3->bool`]
    CONNECTED_INTER_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF;
      IN_IMAGE; o_THM] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `(phi:real^3->real^3) (moi_s35_lift c y1)` THEN ASM_MESON_TAC[];
      EXISTS_TAC `(phi:real^3->real^3) (moi_s35_lift c y2)` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "lift" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^2) IN G`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `c:real`] MOI_S5C_XA_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S5C_PL_BALL_3_FILL; COMPACT_IMP_CLOSED] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `moi_s35_lift c y`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_lift c y IN moi_s35_aflat c` ASSUME_TAC THENL
   [SUBGOAL_THEN `(phi:real^3->real^3) (moi_s35_lift c y) IN IMAGE phi (moi_s35_aflat c)`
    MP_TAC THENL
     [UNDISCH_TAC `frontier xa INTER frontier xb SUBSET
                   IMAGE (phi:real^3->real^3) (moi_s35_aflat c)` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_s35_lift c y = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term ((=) `moi_s35_dom`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:real^3) IN moi_s35_aflat c` THEN UNDISCH_TAC `abs c <= &1 / &512` THEN
    REWRITE_TAC[moi_s35_aflat; moi_s35_dom; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL;
                moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_circles; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `frontier xb INTER IMAGE (phi:real^3->real^3) moi_s35_ttube SUBSET b` THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  UNDISCH_TAC `moi_s35_lift c y IN moi_s35_aflat c` THEN UNDISCH_TAC `abs c <= &1 / &512` THEN
  REWRITE_TAC[moi_s35_aflat; moi_s35_ttube; IN_ELIM_THM] THEN REAL_ARITH_TAC);;
(* The closest-point retraction onto the closed square Q5.                   *)

let MOI_S5L_RETRACT = prove
 (`(!s. (closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) continuous_on s) /\
   (!y:real^2. y IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) ==> (closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) y = y) /\
   (!y:real^2. (closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) y IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) /\
   (!y:real^2. ~(y IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) ==> max (abs(((closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) y)$1)) (abs(((closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) y)$2)) = &5 / &16)`,
  SUBGOAL_THEN `convex (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) /\ closed (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) /\ ~((interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) = {})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_INTERVAL; CLOSED_INTERVAL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[MOI_S5C_IN_SQI; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CLOSEST_POINT_SELF; CLOSEST_POINT_IN_SET] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])`; `y:real^2`] CLOSEST_POINT_IN_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `(interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; IN_DIFF; MOI_S5C_IN_SQI; MOI_S5C_IN_SQO] THEN
  REAL_ARITH_TAC);;

(* Janiszewski's theorem for finitely many disjoint compact sets.           *)

let MOI_S5L_JANISZEWSKI_FINITE = prove
 (`!FS (a:real^2) b.
     FINITE FS /\ (!s. s IN FS ==> compact s) /\
     (!s. s IN FS ==> connected_component ((:real^2) DIFF s) a b) /\
     (!s t. s IN FS /\ t IN FS /\ ~(s = t) ==> DISJOINT s t)
     ==> connected_component ((:real^2) DIFF UNIONS FS) a b`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> b ==> c`] THEN
  SPEC_TAC(`FS:(real^2->bool)->bool`,`FS:(real^2->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_0; DIFF_EMPTY; CONNECTED_COMPONENT_UNIV] THEN REWRITE_TAC[UNIV];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `FS:(real^2->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[FORALL_IN_INSERT; IN_INSERT; UNIONS_INSERT] THEN STRIP_TAC THEN
  MATCH_MP_TAC JANISZEWSKI THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    SUBGOAL_THEN `s INTER UNIONS FS:real^2->bool = {}`
      (fun th -> REWRITE_TAC[th; CONNECTED_EMPTY]) THEN
    REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `t:real^2->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `DISJOINT (s:real^2->bool) t` MP_TAC THENL
     [ASM_MESON_TAC[]; SET_TAC[]];
    USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* For a PL circle j in the open annulus 3/16 < n < 5/16 of the plane: the  *)
(* closed inner square lies inside or outside j, the closed square Q5 has   *)
(* the far point vector[1;0] outside j, and points outside Q5 are outside j. *)

let MOI_S5L_PLANAR_SIDES = prove
 (`!j:real^2->bool.
     pl_sphere 1 j /\
     j SUBSET {y | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                   max (abs(y$1)) (abs(y$2)) < &5 / &16}
     ==> ({y | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside j \/
          {y | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET outside j) /\
         ((:real^2) DIFF (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) SUBSET outside j) /\
         inside j SUBSET {y | max (abs(y$1)) (abs(y$2)) < &5 / &16} /\
         connected (outside j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5L_CIRCLE_BASIC) THEN
  SUBGOAL_THEN `(j:real^2->bool) SUBSET (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` ASSUME_TAC THENL
   [UNDISCH_TAC `(j:real^2->bool) SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                              max (abs(y$1)) (abs(y$2)) < &5 / &16}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_S5C_IN_SQI] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN inside j` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM];
      DISJ2_TAC THEN
      MP_TAC(ISPEC `j:real^2->bool` MOI_S5C_INESS_PLANAR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM]];
    MP_TAC(ISPEC `(interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` OUTSIDE_CONVEX) THEN REWRITE_TAC[CONVEX_INTERVAL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC OUTSIDE_MONO THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{y:real^2 | max (abs(y$1)) (abs(y$2)) < &5 / &16}` THEN
    REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    REWRITE_TAC[MOI_S5C_SQ_CONVEX_LT] THEN
    UNDISCH_TAC `(j:real^2->bool) SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                              max (abs(y$1)) (abs(y$2)) < &5 / &16}` THEN SET_TAC[];
    MATCH_MP_TAC CONNECTED_OUTSIDE THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; DIMINDEX_2; LE_REFL]]);;
(* The planar circle of a component, its position, and essentiality.        *)

let MOI_S5L_COMPONENT_PLANAR = prove
 (`!phi xa xb ww b b0 b1 c k.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\ k IN components (moi_s35_circles (phi:real^3->real^3) b c)
     ==> pl_sphere 1 (IMAGE moi_s5c_proj k) /\
         k = IMAGE (moi_s35_lift c) (IMAGE moi_s5c_proj k) /\
         IMAGE moi_s5c_proj k SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < &5 / &16} /\
         (moi_s35_ess c k <=> {y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside (IMAGE moi_s5c_proj k)) /\
         (~moi_s35_ess c k <=> {y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET outside (IMAGE moi_s5c_proj k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5L_SETUP) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(moi_s35_circles (phi:real^3->real^3) b c)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5L_LEVEL_STRUCTURE) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `moi_s5c_proj`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `jj = IMAGE moi_s5c_proj (k:real^3->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(jj:real^2->bool) SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < &5 / &16}` ASSUME_TAC THENL
   [EXPAND_TAC "jj" THEN UNDISCH_TAC `(k:real^3->bool) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[MOI_S5C_PROJ_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `jj:real^2->bool` MOI_S5L_PLANAR_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `moi_s35_ess c k <=> {y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside jj` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real`; `k:real^3->bool`; `jj:real^2->bool`] MOI_S5C_ESS_LIFT) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~({y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} = {})` MP_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `jj:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
  UNDISCH_TAC `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside jj \/ {y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET outside jj` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Winding numbers around the axis of projected loops, and Lemma 3 (a       *)
(* circle of A'_e INTER B'_e is essential iff it bounds no disk in b).       *)
(* ------------------------------------------------------------------------- *)

let MOI_S5L_PROJ_CONT = prove
 (`!s. moi_s5c_proj continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[MOI_S5C_PROJ_FACTS]);;

let MOI_S5L_LIFT_CONT = prove
 (`!c s. moi_s35_lift c continuous_on s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJUNCT1(SPEC_ALL MOI_S5C_LIFT_LINEAR)] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_S5C_LIFT_LINEAR]);;

let MOI_S5L_STUBE_AXIS = prove
 (`interior moi_s35_stube SUBSET {x:real^3 | ~(moi_s5c_proj x = vec 0)}`,
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s35_stube` THEN
  REWRITE_TAC[INTERIOR_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s35_stube] THEN X_GEN_TAC `x:real^3` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(CONJUNCT2(CONJUNCT2 MOI_S5C_PROJ_FACTS)) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[VEC_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

(* A PL cell is simply connected and contains its boundary.                  *)

let MOI_S5L_CELL_FACTS = prove
 (`!n (d:real^N->bool) j.
     pl_cell_with_boundary n d j ==> j SUBSET d /\ simply_connected d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [homeomorphism]) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    MATCH_MP_TAC CONTRACTIBLE_IMP_SIMPLY_CONNECTED THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] HOMEOMORPHIC_CONTRACTIBLE) THEN
    EXISTS_TAC `k:real^N->bool` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[CONVEX_IMP_CONTRACTIBLE; SIMPLEX_IMP_CONVEX]]]);;

(* Winding numbers of projected loops are invariant under homotopy in a set *)
(* missing the axis.                                                         *)

let MOI_S5L_W_HOMOTOPIC = prove
 (`!B (g:real^1->real^3) h.
     B SUBSET {x | ~(moi_s5c_proj x = vec 0)} /\ homotopic_loops B g h
     ==> winding_number(moi_s5c_proj o g,vec 0) =
         winding_number(moi_s5c_proj o h,vec 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `B:real^3->bool` THEN ASM_REWRITE_TAC[MOI_S5L_PROJ_CONT] THEN
  ASM SET_TAC[]);;

(* An essential level circle carries a loop of winding number +-1.          *)

let MOI_S5L_ESS_LOOP = prove
 (`!c j. pl_sphere 1 j /\ vec 0 IN inside j
         ==> ?g:real^1->real^3.
               path g /\ pathfinish g = pathstart g /\
               path_image g = IMAGE (moi_s35_lift c) j /\
               (winding_number(moi_s5c_proj o g,vec 0) = Cx(&1) \/
                winding_number(moi_s5c_proj o g,vec 0) = --Cx(&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `moi_s35_lift c o (gam:real^1->real^2)` THEN
  SUBGOAL_THEN `moi_s5c_proj o moi_s35_lift c o (gam:real^1->real^2) = gam`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MOI_S5C_PROJ_LIFT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; MOI_S5L_LIFT_CONT];
    MP_TAC(ISPEC `gam:real^1->real^2` SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Loops in an inessential level circle have winding number 0.              *)

let MOI_S5L_INESS_LOOP = prove
 (`!c j (q:real^1->real^3).
     vec 0 IN outside j /\ path q /\ pathfinish q = pathstart q /\
     path_image q SUBSET IMAGE (moi_s35_lift c) j
     ==> winding_number(moi_s5c_proj o q,vec 0) = Cx(&0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_ZERO_IN_OUTSIDE THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S5L_PROJ_CONT];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ISPEC `moi_s5c_proj` IMAGE_SUBSET)) THEN
    REWRITE_TAC[MOI_S5C_PROJ_IMAGE_LIFT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OUTSIDE_MONO) THEN ASM SET_TAC[]]);;

(* A loop in B whose image under phi lies in a simply connected set d with  *)
(* psi mapping d back into B has winding number 0.                           *)

let MOI_S5L_W_NULL = prove
 (`!B d (g:real^1->real^3) (phi:real^3->real^3) psi.
     B SUBSET {x | ~(moi_s5c_proj x = vec 0)} /\
     path g /\ pathfinish g = pathstart g /\ path_image g SUBSET B /\
     phi continuous_on B /\ psi continuous_on d /\ IMAGE psi d SUBSET B /\
     (!x. x IN B ==> psi(phi x) = x) /\
     IMAGE phi (path_image g) SUBSET d /\ simply_connected d
     ==> winding_number(moi_s5c_proj o g,vec 0) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path ((phi:real^3->real^3) o (g:real^1->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ALL]) THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `IMAGE (phi:real^3->real^3) (path_image g) SUBSET d` THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY; IMAGE_EQ_EMPTY; PATH_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:real^3->real^3) o (g:real^1->real^3)`) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `homotopic_loops B (g:real^1->real^3) (linepath((psi:real^3->real^3) a,psi a))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(psi:real^3->real^3) o phi o (g:real^1->real^3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `path_image (g:real^1->real^3) SUBSET B` THEN
      REWRITE_TAC[path_image] THEN ASM SET_TAC[];
      SUBGOAL_THEN `linepath((psi:real^3->real^3) a,psi a) = psi o linepath(a,a)`
      SUBST1_TAC THENL
       [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `g:real^1->real^3`;
                 `linepath((psi:real^3->real^3) a,psi a)`] MOI_S5L_W_HOMOTOPIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `moi_s5c_proj o linepath((psi:real^3->real^3) a,psi a) =
                linepath(moi_s5c_proj(psi a),moi_s5c_proj(psi a))` SUBST1_TAC THENL
   [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN
  SUBGOAL_THEN `(psi:real^3->real^3) a IN B` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `B SUBSET {x:real^3 | ~(moi_s5c_proj x = vec 0)}` THEN SET_TAC[]);;

(* Under loops_carried (IMAGE phi k) b, a loop in B has the winding number  *)
(* of some loop in k.                                                        *)

let MOI_S5L_W_CARRIED = prove
 (`!B b k (phi:real^3->real^3) psi (g:real^1->real^3).
     B SUBSET {x | ~(moi_s5c_proj x = vec 0)} /\
     phi continuous_on B /\ psi continuous_on b /\ IMAGE psi b SUBSET B /\
     IMAGE phi B SUBSET b /\ (!x. x IN B ==> psi(phi x) = x) /\
     k SUBSET B /\ loops_carried (IMAGE phi k) b /\
     path g /\ pathfinish g = pathstart g /\ path_image g SUBSET B
     ==> ?q. path q /\ pathfinish q = pathstart q /\ path_image q SUBSET k /\
             winding_number(moi_s5c_proj o g,vec 0) =
             winding_number(moi_s5c_proj o q,vec 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path ((phi:real^3->real^3) o (g:real^1->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:real^3->real^3) o (g:real^1->real^3)` o
    GEN_REWRITE_RULE I [loops_carried]) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:real^1->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(psi:real^3->real^3) o (q0:real^1->real^3)` THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `b:real^3->bool` THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_S5L_W_HOMOTOPIC THEN EXISTS_TAC `B:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(psi:real^3->real^3) o phi o (g:real^1->real^3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `path_image (g:real^1->real^3) SUBSET B` THEN
      REWRITE_TAC[path_image] THEN ASM SET_TAC[];
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `b:real^3->bool` THEN ASM_REWRITE_TAC[]]]);;
(* Lemma 3, essential => no disk in b bounded by phi k.                     *)

let MOI_S5L_L3_FWD = prove
 (`!phi xa xb ww b b0 b1 c k.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\ k IN components (moi_s35_circles (phi:real^3->real^3) b c) /\
     moi_s35_ess c k
     ==> ~(?d. pl_cell_with_boundary 2 d (IMAGE phi k) /\ d SUBSET b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `d:real^3->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5L_SETUP) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `psi:real^3->real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(moi_s35_circles (phi:real^3->real^3) b c)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[moi_s35_circles; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `k:real^3->bool`] MOI_S5L_COMPONENT_PLANAR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `jj = IMAGE moi_s5c_proj (k:real^3->bool)` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `k:real^3->bool`)) THEN
  SUBGOAL_THEN `vec 0:real^2 IN inside jj` ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside jj` MP_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o C EQ_MP
        (ASSUME `moi_s35_ess c (IMAGE (moi_s35_lift c) jj)`));
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real`; `jj:real^2->bool`] MOI_S5L_ESS_LOOP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `homeomorphism ({x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b},b) ((phi:real^3->real^3),psi)` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `d:real^3->bool`;
    `IMAGE (phi:real^3->real^3) (IMAGE (moi_s35_lift c) jj)`] MOI_S5L_CELL_FACTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} SUBSET {x:real^3 | ~(moi_s5c_proj x = vec 0)}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior moi_s35_stube` THEN
    ASM_REWRITE_TAC[MOI_S5L_STUBE_AXIS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) continuous_on d /\ IMAGE psi d SUBSET {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `b:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC [`IMAGE (psi:real^3->real^3) b = {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`;
                             `(d:real^3->bool) SUBSET b`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`; `d:real^3->bool`; `g:real^1->real^3`; `phi:real^3->real^3`;
                 `psi:real^3->real^3`] MOI_S5L_W_NULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `winding_number(moi_s5c_proj o (g:real^1->real^3),vec 0) = Cx(&1) \/
               winding_number(moi_s5c_proj o g,vec 0) = --Cx(&1)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[CX_INJ; GSYM CX_NEG] THEN REAL_ARITH_TAC);;

(* Lemma 3, inessential => a disk, by Moise 27.3 in the annulus b, given    *)
(* one essential circle (whose loop of winding number +-1 cannot be carried *)
(* by phi k).                                                                *)

let MOI_S5L_L3_BWD = prove
 (`MOISE_273_STATEMENT (:3)
   ==> !phi xa xb ww b b0 b1 c k k'.
         moi_s35_edge_conf phi xa xb ww b b0 b1 c /\ k IN components (moi_s35_circles (phi:real^3->real^3) b c) /\
         ~moi_s35_ess c k /\ k' IN components (moi_s35_circles (phi:real^3->real^3) b c) /\ moi_s35_ess c k'
         ==> ?d. pl_cell_with_boundary 2 d (IMAGE phi k) /\ d SUBSET b`,
  REWRITE_TAC[MOISE_273_STATEMENT] THEN DISCH_THEN(LABEL_TAC "m273") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_annulus (b:real^3->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
      (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
    DISCH_THEN(MP_TAC o hd o filter (MOI_S5C_HEAD "pl_annulus_with_ends") o CONJUNCTS) THEN
    REWRITE_TAC[pl_annulus_with_ends; pl_annulus] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5L_SETUP) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `psi:real^3->real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} /\ (k':real^3->bool) SUBSET {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(moi_s35_circles (phi:real^3->real^3) b c) SUBSET {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` ASSUME_TAC THENL
     [REWRITE_TAC[moi_s35_circles; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(moi_s35_circles (phi:real^3->real^3) b c)` THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `k:real^3->bool`] MOI_S5L_COMPONENT_PLANAR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `jj = IMAGE moi_s5c_proj (k:real^3->bool)` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `k:real^3->bool`)) THEN
  MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `k':real^3->bool`] MOI_S5L_COMPONENT_PLANAR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `jj' = IMAGE moi_s5c_proj (k':real^3->bool)` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `k':real^3->bool`)) THEN
  SUBGOAL_THEN `vec 0:real^2 IN outside jj /\ vec 0:real^2 IN inside jj'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET outside jj /\ {y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside jj'` MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o C EQ_MP
          (ASSUME `~moi_s35_ess c (IMAGE (moi_s35_lift c) jj)`));
        FIRST_ASSUM(ACCEPT_TAC o C EQ_MP
          (ASSUME `moi_s35_ess c (IMAGE (moi_s35_lift c) jj')`))];
      ALL_TAC] THEN
    SUBGOAL_THEN `max (abs((vec 0:real^2)$1)) (abs((vec 0:real^2)$2)) <= &3 / &16`
    MP_TAC THENL [REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "m273" (MP_TAC o SPECL [`b:real^3->bool`;
    `IMAGE (phi:real^3->real^3) (IMAGE (moi_s35_lift c) jj)`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S5C_SPHERE_TRANSPORT THEN
      MAP_EVERY EXISTS_TAC [`{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`; `b:real^3->bool`; `psi:real^3->real^3`] THEN
      ASM_SIMP_TAC[MOI_S5C_LIFT_SPHERE];
      SUBGOAL_THEN `IMAGE (phi:real^3->real^3) {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} = b` MP_TAC THENL
       [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (moi_s35_lift c) jj SUBSET {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:real`; `jj':real^2->bool`] MOI_S5L_ESS_LOOP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `homeomorphism ({x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b},b) ((phi:real^3->real^3),psi)` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b} SUBSET {x:real^3 | ~(moi_s5c_proj x = vec 0)}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior moi_s35_stube` THEN
    ASM_REWRITE_TAC[MOI_S5L_STUBE_AXIS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`; `b:real^3->bool`; `IMAGE (moi_s35_lift c) jj`;
                 `phi:real^3->real^3`; `psi:real^3->real^3`; `g:real^1->real^3`]
    MOI_S5L_W_CARRIED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real`; `jj:real^2->bool`; `q:real^1->real^3`] MOI_S5L_INESS_LOOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `winding_number(moi_s5c_proj o (g:real^1->real^3),vec 0) = Cx(&1) \/
               winding_number(moi_s5c_proj o g,vec 0) = --Cx(&1)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  REWRITE_TAC[CX_INJ; GSYM CX_NEG] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemma 4 (some circle is essential).  If every circle were                *)
(* inessential, the point a = (3/16,0) and the far point e = (1,0) would be  *)
(* joined in the plane minus the projected circles (Janiszewski); retracting *)
(* that connected set onto the square Q5 contradicts CROSS.                  *)
(* ------------------------------------------------------------------------- *)

(* Each inessential planar circle leaves a and e in one component.          *)

let MOI_S5L_INESS_JOIN = prove
 (`!phi xa xb ww b b0 b1 c k.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\ k IN components (moi_s35_circles (phi:real^3->real^3) b c) /\
     ~moi_s35_ess c k
     ==> compact (IMAGE moi_s5c_proj k) /\
         connected_component ((:real^2) DIFF IMAGE moi_s5c_proj k) (vector[&3 / &16; &0]:real^2) (vector[&1; &0]:real^2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `k:real^3->bool`] MOI_S5L_COMPONENT_PLANAR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `jj = IMAGE moi_s5c_proj (k:real^3->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET outside jj` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o C EQ_MP (ASSUME `~moi_s35_ess c k`)); ALL_TAC] THEN
  MP_TAC(ISPEC `jj:real^2->bool` MOI_S5L_PLANAR_SIDES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5L_CIRCLE_BASIC) THEN
  ASM_REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `outside jj:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `jj:real^2->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[];
    UNDISCH_TAC `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET outside jj` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `(:real^2) DIFF (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) SUBSET outside jj` THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; MOI_S5C_IN_SQI] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC]);;

(* The projections of distinct circles are disjoint.                         *)

let MOI_S5L_PROJ_DISJOINT = prove
 (`!phi b c.
     !s t. s IN IMAGE (IMAGE moi_s5c_proj) (components (moi_s35_circles (phi:real^3->real^3) b c)) /\
           t IN IMAGE (IMAGE moi_s5c_proj) (components (moi_s35_circles (phi:real^3->real^3) b c)) /\ ~(s = t)
           ==> DISJOINT s t`,
  MAP_EVERY X_GEN_TAC [`phi:real^3->real^3`; `b:real^3->bool`; `c:real`] THEN
  SUBGOAL_THEN
   `!x y. x IN (moi_s35_circles (phi:real^3->real^3) b c) /\ y IN (moi_s35_circles (phi:real^3->real^3) b c) /\ moi_s5c_proj x = moi_s5c_proj y ==> x = y`
  (LABEL_TAC "pinj") THENL
   [MATCH_MP_TAC MOI_S5C_PROJ_INJ_LEVEL THEN EXISTS_TAC `c:real` THEN
    REWRITE_TAC[moi_s35_circles; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `k1:real^3->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `k2:real^3->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `DISJOINT (k1:real^3->bool) k2` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN
    MP_TAC(ISPECL [`(moi_s35_circles (phi:real^3->real^3) b c)`; `k1:real^3->bool`; `k2:real^3->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(IMAGE moi_s5c_proj (k1:real^3->bool) = IMAGE moi_s5c_proj k2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k1:real^3->bool) SUBSET (moi_s35_circles (phi:real^3->real^3) b c) /\ (k2:real^3->bool) SUBSET (moi_s35_circles (phi:real^3->real^3) b c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^2` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `x2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `x1:real^3 = x2` ASSUME_TAC THENL
   [USE_THEN "pinj" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(x1:real^3) IN k1`; `(k1:real^3->bool) SUBSET (moi_s35_circles (phi:real^3->real^3) b c)`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`(x2:real^3) IN k2`; `(k2:real^3->bool) SUBSET (moi_s35_circles (phi:real^3->real^3) b c)`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`z = moi_s5c_proj x1`; `z = moi_s5c_proj x2`] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`DISJOINT (k1:real^3->bool) k2`; `(x1:real^3) IN k1`;
                         `(x2:real^3) IN k2`; `x1:real^3 = x2`] THEN
  SET_TAC[]);;

(* Lemma 4.                                                                  *)

let MOI_S5L_SOME_ESS = prove
 (`!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> ?k. k IN components (moi_s35_circles (phi:real^3->real^3) b c) /\ moi_s35_ess c k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "iness" o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5L_LEVEL_STRUCTURE) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!k. k IN components (moi_s35_circles (phi:real^3->real^3) b c)
        ==> compact (IMAGE moi_s5c_proj k) /\
            connected_component ((:real^2) DIFF IMAGE moi_s5c_proj k) (vector[&3 / &16; &0]:real^2) (vector[&1; &0]:real^2)`
  (LABEL_TAC "kfacts") THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5L_INESS_JOIN THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "iness" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE moi_s5c_proj) (components (moi_s35_circles (phi:real^3->real^3) b c))`; `(vector[&3 / &16; &0]:real^2)`; `(vector[&1; &0]:real^2)`]
    MOI_S5L_JANISZEWSKI_FINITE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "kfacts" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(k:real^3->bool) IN components (moi_s35_circles (phi:real^3->real^3) b c)`))) THEN SIMP_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "kfacts" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(k:real^3->bool) IN components (moi_s35_circles (phi:real^3->real^3) b c)`))) THEN SIMP_TAC[];
      REWRITE_TAC[MOI_S5L_PROJ_DISJOINT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (IMAGE (IMAGE moi_s5c_proj) (components (moi_s35_circles (phi:real^3->real^3) b c))) =
                IMAGE moi_s5c_proj (moi_s35_circles (phi:real^3->real^3) b c)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNIONS; GSYM UNIONS_COMPONENTS]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONNECTED_COMPONENT_IN) THEN
  ABBREV_TAC `G = connected_component ((:real^2) DIFF IMAGE moi_s5c_proj (moi_s35_circles (phi:real^3->real^3) b c)) (vector[&3 / &16; &0]:real^2)` THEN
  SUBGOAL_THEN `connected (G:real^2->bool) /\ (vector[&3 / &16; &0]:real^2) IN G /\ (vector[&1; &0]:real^2) IN G /\
                G SUBSET (:real^2) DIFF IMAGE moi_s5c_proj (moi_s35_circles (phi:real^3->real^3) b c)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "G" THEN REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
      EXPAND_TAC "G" THEN REWRITE_TAC[IN] THEN
      REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN] THEN FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "G" THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]];
    ALL_TAC] THEN
  MP_TAC MOI_S5L_RETRACT THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5L_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
    (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `IMAGE (closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) G`; `(vector[&3 / &16; &0]:real^2)`; `(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (vector[&1; &0]:real^2)`] MOI_S5L_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(vector[&3 / &16; &0]:real^2)` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[MOI_S5C_IN_SQI; VECTOR_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `interior xb:real^3->bool` THEN REWRITE_TAC[INTERIOR_SUBSET] THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[moi_s35_sq; IN_ELIM_THM; MOI_S5C_PROJ_LIFT; VECTOR_2] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `!s x:real^3. DISJOINT s xb /\ x IN s ==> ~(x IN xb)`) THEN
      EXISTS_TAC `IMAGE (phi:real^3->real^3) (moi_s35_sq (&5 / &16) c)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[moi_s35_sq; IN_ELIM_THM; MOI_S5C_PROJ_LIFT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[MOI_S5C_IN_SQI; VECTOR_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(x:real^2) IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` THENL
   [SUBGOAL_THEN `(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (x:real^2) = x` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN IMAGE moi_s5c_proj (moi_s35_circles (phi:real^3->real^3) b c)` MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `moi_s35_lift c (x:real^2)` THEN
      ASM_REWRITE_TAC[MOI_S5C_PROJ_LIFT];
      UNDISCH_TAC `(G:real^2->bool) SUBSET (:real^2) DIFF IMAGE moi_s5c_proj (moi_s35_circles (phi:real^3->real^3) b c)` THEN
      UNDISCH_TAC `(x:real^2) IN G` THEN SET_TAC[]];
    SUBGOAL_THEN `moi_s35_lift c ((closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (x:real^2)) IN {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`moi_s35_lift c ((closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (x:real^2)) IN (moi_s35_circles (phi:real^3->real^3) b c)`;
                             `(moi_s35_circles (phi:real^3->real^3) b c) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}`] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; MOI_S5C_PROJ_LIFT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&5 / &16`)) (concl th) &&
      can (find_term is_neg) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The passage from one essential circle to the single-circle outcome.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S5L_INSIDE_CONNECTED = prove
 (`!j:real^2->bool. pl_sphere 1 j ==> connected (inside j)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `g:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Lifts of points of the closed square Q5 lie in dom and map to frontier xa. *)

let MOI_S5L_XA_FRONTIER = prove
 (`!phi xa xb ww b b0 b1 c (y:real^2).
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\ y IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])
     ==> phi (moi_s35_lift c y) IN frontier xa /\ moi_s35_lift c y IN moi_s35_dom`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
    (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
  MP_TAC(ISPECL [`c:real`; `y:real^2`] MOI_S5L_LIFT_Q5) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `c:real`] MOI_S5C_XA_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S5C_PL_BALL_3_FILL; COMPACT_IMP_CLOSED] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `moi_s35_lift c y`) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

(* Bd X_a INTER Bd X_b = phi(circles).                                       *)

let MOI_S5L_FF_EQ = prove
 (`!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> frontier xa INTER frontier xb = IMAGE phi (moi_s35_circles (phi:real^3->real^3) b c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(moi_s35_circles (phi:real^3->real^3) b c) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5L_SETUP) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(ACCEPT_TAC o el 11 o CONJUNCTS);
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
    (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (phi:real^3->real^3) (moi_s35_aflat c)` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`frontier xa INTER frontier xb SUBSET IMAGE (phi:real^3->real^3) (moi_s35_aflat c)`;
        `(x:real^3) IN frontier xa`; `(x:real^3) IN frontier xb`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3) IN moi_s35_ttube /\ z IN moi_s35_dom /\ z$3 = c`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN moi_s35_aflat c` THEN UNDISCH_TAC `abs c <= &1 / &512` THEN
      REWRITE_TAC[moi_s35_aflat; moi_s35_ttube; moi_s35_dom; moi_s35_cube; IN_ELIM_THM;
        IN_INTERVAL; moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[moi_s35_circles; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier xb INTER IMAGE (phi:real^3->real^3) moi_s35_ttube SUBSET b` THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN frontier xb` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(phi:real^3->real^3) z IN b /\ z$3 = c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN (moi_s35_circles (phi:real^3->real^3) b c)` THEN REWRITE_TAC[moi_s35_circles; IN_ELIM_THM] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `moi_s35_lift c (moi_s5c_proj z) = z` (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S5C_PROJ_LIFT)) THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `moi_s5c_proj z`] MOI_S5L_XA_FRONTIER) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOI_S5C_IN_SQI; MOI_S5C_PROJ_FACTS] THEN
      MAP_EVERY UNDISCH_TAC [`(z:real^3) IN (moi_s35_circles (phi:real^3->real^3) b c)`; `(moi_s35_circles (phi:real^3->real^3) b c) SUBSET {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}`] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN REAL_ARITH_TAC;
      UNDISCH_TAC `b SUBSET frontier (xb:real^3->bool)` THEN
      UNDISCH_TAC `(phi:real^3->real^3) z IN b` THEN SET_TAC[]]]);;

(* Bd X_a INTER X_b lies over the disk of the single circle j.               *)

let MOI_S5L_FXB_SUB = prove
 (`!phi xa xb ww b b0 b1 c j.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\ pl_sphere 1 j /\
     j SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < &5 / &16} /\ (moi_s35_circles (phi:real^3->real^3) b c) = IMAGE (moi_s35_lift c) j
     ==> frontier xa INTER xb SUBSET IMAGE phi (IMAGE (moi_s35_lift c) (j UNION inside j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
    (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
  MP_TAC(ISPEC `j:real^2->bool` MOI_S5L_PLANAR_SIDES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC MOI_S5L_RETRACT THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (phi:real^3->real^3)
                  {z | z IN moi_s35_level c /\ moi_s35_n z < &5 / &16}` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`frontier xa INTER xb SUBSET
       IMAGE (phi:real^3->real^3) {x | x IN moi_s35_level c /\ moi_s35_n x < &5 / &16}`;
      `(x:real^3) IN frontier xa`; `(x:real^3) IN xb`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; moi_s35_level] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s35_lift c (moi_s5c_proj z) = z` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S5C_PROJ_LIFT)) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5c_proj z IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5C_IN_SQI; MOI_S5C_PROJ_FACTS] THEN
    UNDISCH_TAC `moi_s35_n z < &5 / &16` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y = moi_s5c_proj z` THEN
  EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_UNION] THEN
  MATCH_MP_TAC(TAUT `(~(a \/ b) ==> F) ==> a \/ b`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^2) IN outside j` ASSUME_TAC THENL
   [MP_TAC(ISPEC `j:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
    UNDISCH_TAC `~((y:real^2) IN j \/ y IN inside j)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `IMAGE (closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (outside j)`; `y:real^2`; `(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (vector[&1; &0]:real^2)`]
    MOI_S5L_CROSS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(:real^2) DIFF (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]) SUBSET outside j` THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; MOI_S5C_IN_SQI] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(x:real^3) IN xb` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `!s x:real^3. DISJOINT s xb /\ x IN s ==> ~(x IN xb)`) THEN
      EXISTS_TAC `IMAGE (phi:real^3->real^3) (moi_s35_sq (&5 / &16) c)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[moi_s35_sq; IN_ELIM_THM; MOI_S5C_PROJ_LIFT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[MOI_S5C_IN_SQI; VECTOR_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (w:real^2) IN j` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_lift c ((closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (w:real^2)) IN (moi_s35_circles (phi:real^3->real^3) b c)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_S5C_IN_LIFT; MOI_S5C_PROJ_LIFT];
    ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^2) IN (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` THENL
   [SUBGOAL_THEN `(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (w:real^2) = w` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `j:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
    MAP_EVERY UNDISCH_TAC [`(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (w:real^2) IN j`; `(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (w:real^2) = w`;
                           `(w:real^2) IN outside j`] THEN
    SET_TAC[];
    UNDISCH_TAC `(j:real^2->bool) SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < &5 / &16}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(closest_point (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])) (w:real^2)`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&5 / &16`)) (concl th) &&
      can (find_term is_neg) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The disk of the single circle j lies in Bd X_a INTER X_b.                 *)

let MOI_S5L_FXB_SUP = prove
 (`!phi xa xb ww b b0 b1 c j.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\ pl_sphere 1 j /\
     j SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < &5 / &16} /\ (moi_s35_circles (phi:real^3->real^3) b c) = IMAGE (moi_s35_lift c) j /\ {y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside j
     ==> IMAGE phi (IMAGE (moi_s35_lift c) (j UNION inside j)) SUBSET frontier xa INTER xb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_edge_conf] o check
    (MOI_S5C_HEAD "moi_s35_edge_conf")) THEN
  MP_TAC(ISPEC `j:real^2->bool` MOI_S5L_PLANAR_SIDES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN `(j:real^2->bool) UNION inside j SUBSET (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(j:real^2->bool) SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < &5 / &16}`;
      `inside j SUBSET {y:real^2 | max (abs(y$1)) (abs(y$2)) < &5 / &16}`] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; MOI_S5C_IN_SQI] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^2` THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `y:real^2`] MOI_S5L_XA_FRONTIER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MAP_EVERY UNDISCH_TAC [`(y:real^2) IN j UNION inside j`;
                               `(j:real^2->bool) UNION inside j SUBSET (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])`] THEN
        SET_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^2) IN j UNION inside j` THEN REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `moi_s35_lift c y IN (moi_s35_circles (phi:real^3->real^3) b c)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[moi_s35_circles; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `frontier xb SUBSET (xb:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
      ASM_SIMP_TAC[MOI_S5C_PL_BALL_3_FILL; COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    UNDISCH_TAC `b SUBSET frontier (xb:real^3->bool)` THEN
    UNDISCH_TAC `(phi:real^3->real^3) (moi_s35_lift c y) IN b` THEN SET_TAC[];
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `inside j:real^2->bool`; `(vector[&3 / &16; &0]:real^2)`; `y:real^2`]
      MOI_S5L_CROSS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC MOI_S5L_INSIDE_CONNECTED THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `(j:real^2->bool) UNION inside j SUBSET (interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]])` THEN SET_TAC[];
        UNDISCH_TAC `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside j` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `interior xb:real^3->bool` THEN REWRITE_TAC[INTERIOR_SUBSET] THEN
        MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[moi_s35_sq; IN_ELIM_THM; MOI_S5C_PROJ_LIFT; VECTOR_2] THEN
        REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^2) IN j` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s35_lift c (w:real^2) IN (moi_s35_circles (phi:real^3->real^3) b c)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_S5C_IN_LIFT; MOI_S5C_PROJ_LIFT];
      ALL_TAC] THEN
    MP_TAC(ISPEC `j:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MAP_EVERY UNDISCH_TAC [`(w:real^2) IN j`; `(w:real^2) IN inside j`] THEN
    SET_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* The main theorems LEMMA1 and SINGLE_FROM_ONE.                             *)
(* ------------------------------------------------------------------------- *)

let LEMMA1 = prove
 (MOI_S35_LEMMA1,
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5L_LEMMA1_STRUCT) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k':real^3->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S5L_SOME_ESS) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `moi_s35_ess c k` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `k:real^3->bool`] MOI_S5L_L3_FWD) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(MATCH_MP MOI_S5L_L3_BWD (ASSUME `MOISE_273_STATEMENT (:3)`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `k:real^3->bool`; `k':real^3->bool`]) THEN
      ASM_REWRITE_TAC[]];
    EXISTS_TAC `k':real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let SINGLE_FROM_ONE = prove
 (MOI_S35_SINGLE_FROM_ONE,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->bool) IN components (moi_s35_circles (phi:real^3->real^3) b c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`; `k:real^3->bool`] MOI_S5L_COMPONENT_PLANAR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `jj = IMAGE moi_s5c_proj (k:real^3->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  SUBGOAL_THEN `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside jj` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o C EQ_MP (ASSUME `moi_s35_ess c k`)); ALL_TAC] THEN
  SUBGOAL_THEN `(moi_s35_circles (phi:real^3->real^3) b c) = IMAGE (moi_s35_lift c) jj` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN
    ASM_REWRITE_TAC[UNIONS_1];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_single] THEN EXISTS_TAC `jj:real^2->bool` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNION; moi_s35_aflat; moi_s35_sq;
                IN_ELIM_THM; MOI_S5C_PROJ_LIFT] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `(jj:real^2->bool) SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < &5 / &16}` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[MOI_S5C_N_LIFT] THEN UNDISCH_TAC `{y:real^2 | max (abs(y$1)) (abs(y$2)) <= &3 / &16} SUBSET inside jj` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    MP_TAC(SPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`] MOI_S5L_FF_EQ) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5L_FXB_SUB THEN
      MAP_EVERY EXISTS_TAC [`ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`;
                            `b1:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5L_FXB_SUP THEN
      MAP_EVERY EXISTS_TAC [`ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`;
                            `b1:real^3->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

