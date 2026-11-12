(* ========================================================================= *)
(* pc_moi_s35_ext2t: the annulus twist for pc_moi_s35_ext2 (TWO_DISK_EXT).   *)
(* M = Q2 minus open Q1 in real^2, C1 = rf Q1, C2 = rf Q2.  Main theorem     *)
(* MOI_S5W_DICHOTOMY (statement MOI_S5W_DICHOTOMY_STMT): for every PLH g of  *)
(* the square circle C1, g or g composed with the diagonal reflection        *)
(* tau(x1,x2) = (x2,x1) is the restriction to C1 of a PLH of M that is the   *)
(* identity on C2.  Route: cone twists of arc-supported maps (apex           *)
(* (3/2,3/2) over the two-edge arc at (1,1)), symmetries of the square,     *)
(* corner moves to normalize g at the corners (1,1) and (-1,-1), and the     *)
(* two remaining open arcs by connectedness.                                 *)
(* ========================================================================= *)

needs "src/pc_moi_s35_minc.ml";;

prioritize_real();;
type_invention_error := true;;

(* The statement of the main theorem MOI_S5W_DICHOTOMY.                     *)

let MOI_S5W_DICHOTOMY_STMT =
 `!(g:real^2->real^2) g'.
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g')
     ==> (?f f'. pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))) (f,f') /\
                 (!x. x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) ==> f x = x) /\ (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> f x = g x)) \/
         (?f f'. pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))) (f,f') /\
                 (!x. x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) ==> f x = x) /\
                 (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> f x = g (vector[x$2; x$1])))`;;

(* ------------------------------------------------------------------------- *)
(* A1: extendable maps of the square circle; symmetries of the square.       *)
(* ------------------------------------------------------------------------- *)

let moi_s5w_ext = new_definition
 `moi_s5w_ext (g:real^2->real^2) <=>
    ?f f'. pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))) (f,f') /\
           (!x. x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) ==> f x = x) /\ (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> f x = g x)`;;

let MOI_S5W_HOMEO_PTS = prove
 (`!(f:real^M->real^N) g s t.
     homeomorphism (s,t) (f,g)
     ==> !x y. (x IN s ==> f x IN t /\ g (f x) = x) /\
               (y IN t ==> g y IN s /\ f (g y) = y)`,
  REWRITE_TAC[homeomorphism] THEN SET_TAC[]);;

let MOI_S5W_MM_POLY = prove
 (`locally_polyhedral (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ locally_polyhedral (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
   pl_polyhedron (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ pl_polyhedron (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  MATCH_MP_TAC(TAUT `(c ==> a) /\ (d ==> b) /\ c /\ d ==> a /\ b /\ c /\ d`) THEN
  REWRITE_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_S5C_SQANN_POLYHEDRON] THEN
  MATCH_MP_TAC MOI_S5C_SQ_RF_POLYHEDRON THEN REAL_ARITH_TAC);;

let MOI_S5W_C_SUB_MM = prove
 (`(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`,
  REWRITE_TAC[SUBSET; MOI_S5C_IN_RF1; MOI_S5C_IN_RF2; MOI_S5C_IN_SQANN] THEN
  REAL_ARITH_TAC);;

let MOI_S5W_EXT_EQ = prove
 (`!g h:real^2->real^2.
     moi_s5w_ext g /\ (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> g x = h x) ==> moi_s5w_ext h`,
  REWRITE_TAC[moi_s5w_ext] THEN MESON_TAC[]);;

let MOI_S5W_EXT_ID = prove
 (`moi_s5w_ext (\x:real^2. x)`,
  REWRITE_TAC[moi_s5w_ext] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^2. x`; `\x:real^2. x`] THEN
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID; IMAGE_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID; MOI_S5W_MM_POLY]);;

let MOI_S5W_EXT_COMPOSE = prove
 (`!g1 g2:real^2->real^2.
     moi_s5w_ext g1 /\ moi_s5w_ext g2 /\ (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> g2 x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))
     ==> moi_s5w_ext (g1 o g2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5w_ext] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f1:real^2->real^2` (X_CHOOSE_THEN `f1':real^2->real^2`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f2:real^2->real^2` (X_CHOOSE_THEN `f2':real^2->real^2`
        STRIP_ASSUME_TAC))
      ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(f1:real^2->real^2) o (f2:real^2->real^2)`; `(f2':real^2->real^2) o (f1':real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[o_THM];
    ASM_SIMP_TAC[o_THM]]);;

let MOI_S5W_EXT_INV = prove
 (`!g g':real^2->real^2.
     moi_s5w_ext g /\ pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') ==> moi_s5w_ext g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5w_ext] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `f':real^2->real^2`
      STRIP_ASSUME_TAC))
    ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`f':real^2->real^2`; `f:real^2->real^2`] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> concl th = `pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))) ((f:real^2->real^2),f')`)) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5W_C_SUB_MM THEN STRIP_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(f:real^2->real^2) x = x` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    SUBGOAL_THEN `(f:real^2->real^2) ((g':real^2->real^2) x) = x` MP_TAC THENL
     [SUBGOAL_THEN `(g':real^2->real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Symmetries: involutive linear maps preserving the norm max |x1|,|x2|.    *)

let moi_s5w_sym = new_definition
 `moi_s5w_sym (s:real^2->real^2) <=>
    linear s /\ (!x. s (s x) = x) /\
    (!x. max (abs((s x)$1)) (abs((s x)$2)) = max (abs(x$1)) (abs(x$2)))`;;

let MOI_S5W_SYM_FACTS = prove
 (`!s:real^2->real^2.
     moi_s5w_sym s
     ==> pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))) (s,s) /\ pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (s,s) /\
         (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> s x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) /\ (!x. x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) ==> s x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) /\
         (!x. x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) ==> s x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])))`,
  GEN_TAC THEN REWRITE_TAC[moi_s5w_sym] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> (s:real^2->real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) /\
    (!x. x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) ==> s x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) /\ (!x. x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) ==> s x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_S5C_IN_RF1; MOI_S5C_IN_RF2; MOI_S5C_IN_SQANN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. (!x. x IN t ==> (s:real^2->real^2) x IN t) /\ locally_polyhedral t
                    ==> pl_homeomorphism (t,t) (s,s)` (fun th ->
    CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[MOI_S5W_MM_POLY]) THEN
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
  SUBGOAL_THEN `IMAGE (s:real^2->real^2) t = t` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^2. (s:real^2->real^2) x + vec 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_RID];
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[]]);;

let MOI_S5W_EXT_CONJ = prove
 (`!s g:real^2->real^2.
     moi_s5w_sym s /\ moi_s5w_ext g ==> moi_s5w_ext (\x. s (g (s x)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s5w_sym]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5W_SYM_FACTS) THEN
  REWRITE_TAC[moi_s5w_ext] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `f':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`((s:real^2->real^2) o f) o s`; `(s:real^2->real^2) o f' o s`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(s:real^2->real^2) x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(s:real^2->real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* The four symmetries used.                                                *)

let MOI_S5W_SYMS = prove
 (`moi_s5w_sym (\x. vector[x$2; x$1]) /\
   moi_s5w_sym (\x. vector[--(x$1); x$2]) /\
   moi_s5w_sym (\x. vector[x$1; --(x$2)]) /\
   moi_s5w_sym (\x. vector[--(x$1); --(x$2)])`,
  REWRITE_TAC[moi_s5w_sym; linear] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A2: the arc L1 at the corner (1,1) and its cone from the apex (3/2,3/2).  *)
(* ------------------------------------------------------------------------- *)

let moi_s5w_l1 = new_definition `moi_s5w_l1 = {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ &0 <= x$1 + x$2}`;;

let moi_s5w_r1 = new_definition `moi_s5w_r1 = UNIONS {segment[(vector[&3 / &2; &3 / &2]:real^2),x] | x IN moi_s5w_l1}`;;

let moi_s5w_m2 = new_definition `moi_s5w_m2 = closure((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF moi_s5w_r1)`;;

let MOI_S5W_IN_L1 = prove
 (`!x:real^2. x IN moi_s5w_l1 <=> x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ &0 <= x$1 + x$2`,
  REWRITE_TAC[moi_s5w_l1; IN_ELIM_THM]);;

let MOI_S5W_EDGES = prove
 (`(!x:real^2. x IN segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] <=> x$2 = &1 /\ abs(x$1) <= &1) /\
   (!x:real^2. x IN segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)] <=> x$1 = &1 /\ abs(x$2) <= &1)`,
  CONJ_TAC THEN X_GEN_TAC `x:real^2` THENL
   [MP_TAC(ISPECL [`(vector[-- &1;&1]:real^2)`; `(vector[&1;&1]:real^2)`; `x:real^2`] SEGMENT_HORIZONTAL);
    MP_TAC(ISPECL [`(vector[&1;&1]:real^2)`; `(vector[&1;-- &1]:real^2)`; `x:real^2`] SEGMENT_VERTICAL)] THEN
  REWRITE_TAC[VECTOR_2] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let MOI_S5W_L1_EQ = prove
 (`moi_s5w_l1 = segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)]`,
  REWRITE_TAC[EXTENSION; MOI_S5W_IN_L1; IN_UNION; MOI_S5W_EDGES; MOI_S5C_IN_RF1] THEN
  REAL_ARITH_TAC);;

let MOI_S5W_L1_FACTS = prove
 (`pl_polyhedron moi_s5w_l1 /\ ~(moi_s5w_l1 = {}) /\ ~((vector[&3 / &2; &3 / &2]:real^2) IN moi_s5w_l1) /\ moi_s5w_l1 SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
   (!x y. x IN moi_s5w_l1 /\ y IN moi_s5w_l1 /\ y IN segment[(vector[&3 / &2; &3 / &2]:real^2),x] ==> y = x)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_S5W_L1_EQ; pl_polyhedron] THEN
    EXISTS_TAC `{segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)], segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)]}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                POLYTOPE_SEGMENT; UNIONS_2];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(vector[&1;&1]:real^2)` THEN
    REWRITE_TAC[MOI_S5W_IN_L1; MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC;
    REWRITE_TAC[MOI_S5W_IN_L1; MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; MOI_S5W_IN_L1] THEN SIMP_TAC[];
    REWRITE_TAC[MOI_S5W_IN_L1; MOI_S5C_IN_RF1; IN_SEGMENT] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(y:real^2)$1 = (&1 - u) * &3 / &2 + u * (x:real^2)$1 /\
                  y$2 = (&1 - u) * &3 / &2 + u * x$2` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2)$2 = &1 \/ x$1 = &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_THEN DISJ_CASES_TAC] THEN
    SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `max (abs((y:real^2)$1)) (abs(y$2)) = &1` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      UNDISCH_TAC `max (abs((y:real^2)$1)) (abs(y$2)) = &1` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

(* The cone over L1 from (3/2,3/2) is the part of M in the triangle with   *)
(* vertices (3/2,3/2), (-1,1), (1,-1).                                       *)

let MOI_S5W_CONE_EQ = prove
 (`moi_s5w_r1 = {z:real^2 | z IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ &0 <= z$1 + z$2 /\ &0 <= z$1 - &5 * z$2 + &6 /\ &0 <= z$2 - &5 * z$1 + &6}`,
  REWRITE_TAC[moi_s5w_r1; EXTENSION; MOI_CON_IN_CONE; IN_ELIM_THM] THEN
  REWRITE_TAC[MOI_S5W_IN_L1] THEN X_GEN_TAC `z:real^2` THEN
  EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM; MOI_S5C_IN_RF1; MOI_S5C_IN_SQANN] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^2)$1 = &3 / &2 + t * ((x:real^2)$1 - &3 / &2) /\
                  z$2 = &3 / &2 + t * (x$2 - &3 / &2)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
                      VECTOR_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= t * ((x:real^2)$1 + &1) /\ &0 <= t * (&1 - x$1) /\
                  &0 <= t * (x$2 + &1) /\ &0 <= t * (&1 - x$2)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2)$2 = &1 \/ x$1 = &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_THEN DISJ_CASES_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    ASM_CASES_TAC `z = (vector[&3 / &2; &3 / &2]:real^2)` THENL
     [MAP_EVERY EXISTS_TAC [`(vector[&1;&1]:real^2)`; `&0`] THEN
      ASM_REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^2)$1 < &3 / &2 \/ z$2 < &3 / &2` ASSUME_TAC THENL
     [UNDISCH_TAC `~(z = (vector[&3 / &2; &3 / &2]:real^2))` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `z IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN REWRITE_TAC[MOI_S5C_IN_SQANN] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(z:real^2)$1 <= z$2` THENL
     [SUBGOAL_THEN `&1 <= (z:real^2)$2 /\ z$2 < &3 / &2` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `t = &3 - &2 * (z:real^2)$2` THEN
      SUBGOAL_THEN `&0 < t /\ t <= &1` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC
       [`vector[&3 / &2 + ((z:real^2)$1 - &3 / &2) / t; &1]:real^2`; `t:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
       [REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
        SUBGOAL_THEN `--(&5 / &2) * t <= (z:real^2)$1 - &3 / &2 /\
                      (z:real^2)$1 - &3 / &2 <= --(&1 / &2) * t` STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `--(&5 / &2) <= ((z:real^2)$1 - &3 / &2) / t /\
                      ((z:real^2)$1 - &3 / &2) / t <= --(&1 / &2)` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ]; REAL_ARITH_TAC];
        REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                    VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
          EXPAND_TAC "t" THEN REAL_ARITH_TAC]];
      SUBGOAL_THEN `&1 <= (z:real^2)$1 /\ z$1 < &3 / &2` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `t = &3 - &2 * (z:real^2)$1` THEN
      SUBGOAL_THEN `&0 < t /\ t <= &1` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC
       [`vector[&1; &3 / &2 + ((z:real^2)$2 - &3 / &2) / t]:real^2`; `t:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
       [REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
        SUBGOAL_THEN `--(&5 / &2) * t <= (z:real^2)$2 - &3 / &2 /\
                      (z:real^2)$2 - &3 / &2 <= --(&1 / &2) * t` STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `--(&5 / &2) <= ((z:real^2)$2 - &3 / &2) / t /\
                      ((z:real^2)$2 - &3 / &2) / t <= --(&1 / &2)` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ]; REAL_ARITH_TAC];
        REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                    VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
        CONJ_TAC THENL
         [EXPAND_TAC "t" THEN REAL_ARITH_TAC;
          UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD]]]]);;

(* ------------------------------------------------------------------------- *)
(* A3: the cone twist: a PLH of C1 fixing the half x1 + x2 <= 0 pointwise   *)
(* extends to a PLH of M that is the identity on C2.                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S5W_LOW_FIX = prove
 (`!g g':real^2->real^2.
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\
     (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 + x$2 <= &0 ==> g x = x)
     ==> (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 + x$2 <= &0 ==> g' x = x) /\
         IMAGE g moi_s5w_l1 = moi_s5w_l1 /\ IMAGE g' moi_s5w_l1 = moi_s5w_l1 /\
         pl_homeomorphism (moi_s5w_l1,moi_s5w_l1) (g,g')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2")) THEN
  SUBGOAL_THEN `!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> (g:real^2->real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
                  (g':real^2->real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ g' (g x) = x /\ g (g' x) = x`
  (LABEL_TAC "h1") THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 + x$2 <= &0 ==> (g':real^2->real^2) x = x`
  (LABEL_TAC "h3") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^2->real^2) x = x` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
     [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ((g:real^2->real^2) x)$1 + (g x)$2 <= &0 ==> g x = x`
  (LABEL_TAC "h4") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(g':real^2->real^2) ((g:real^2->real^2) x) = g x` MP_TAC THENL
     [USE_THEN "h3" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ((g':real^2->real^2) x)$1 + (g' x)$2 <= &0 ==> g' x = x`
  (LABEL_TAC "h5") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^2->real^2) ((g':real^2->real^2) x) = g' x` MP_TAC THENL
     [USE_THEN "h2" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN moi_s5w_l1 ==> (g:real^2->real^2) x IN moi_s5w_l1 /\ g' x IN moi_s5w_l1`
  (LABEL_TAC "h6") THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[MOI_S5W_IN_L1] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(g:real^2->real^2) x = x` MP_TAC THENL
       [USE_THEN "h4" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        DISCH_TAC THEN UNDISCH_TAC `((g:real^2->real^2) x)$1 + (g x)$2 < &0` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(g':real^2->real^2) x = x` MP_TAC THENL
       [USE_THEN "h5" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        DISCH_TAC THEN UNDISCH_TAC `((g':real^2->real^2) x)$1 + (g' x)$2 < &0` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_l1 SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5W_L1_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^2) moi_s5w_l1 = moi_s5w_l1 /\ IMAGE (g':real^2->real^2) moi_s5w_l1 = moi_s5w_l1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THENL
     [EXISTS_TAC `(g':real^2->real^2) y`; EXISTS_TAC `(g:real^2->real^2) y`] THEN
    SUBGOAL_THEN `(y:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]; ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[pl_homeomorphism] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`; `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]);
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_S5W_L1_FACTS] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [pl_homeomorphism]);
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_S5W_L1_FACTS] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [pl_homeomorphism])]);;

(* Facts about the cone region R1 and the closure M2 of its complement.     *)

let MOI_S5W_CLOSED_LIN = prove
 (`!a b c. closed {z:real^2 | a * z$1 + b * z$2 + c <= &0}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vector[a;b]:real^2`; `--c:real`] CLOSED_HALFSPACE_LE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_2; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S5W_HULL3 = prove
 (`!a b c:real^2. convex hull {a,b,c} = UNIONS {segment[a,x] | x IN segment[b,c]}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; SEGMENT_CONVEX_HULL]);;

let MOI_S5W_R1_HULLS = prove
 (`moi_s5w_r1 = convex hull {(vector[&3 / &2; &3 / &2]:real^2),(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)} UNION convex hull {(vector[&3 / &2; &3 / &2]:real^2),(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)}`,
  REWRITE_TAC[moi_s5w_r1; MOI_S5W_L1_EQ; MOI_S5W_HULL3] THEN
  REWRITE_TAC[EXTENSION; MOI_CON_IN_CONE; IN_UNION] THEN MESON_TAC[]);;

let MOI_S5W_DEL_BOUND = prove
 (`!z:real^2. &0 <= z$1 + z$2 /\ &0 <= z$1 - &5 * z$2 + &6 /\ &0 <= z$2 - &5 * z$1 + &6 ==> abs(z$1) <= &3 / &2 /\ abs(z$2) <= &3 / &2`,
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5W_R1_FACTS = prove
 (`moi_s5w_r1 SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ closed moi_s5w_r1 /\ pl_polyhedron moi_s5w_r1 /\
   moi_s5w_r1 INTER (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) = {} /\ moi_s5w_r1 INTER (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = moi_s5w_l1 /\
   closed moi_s5w_m2 /\ pl_polyhedron moi_s5w_m2 /\ (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) = moi_s5w_r1 UNION moi_s5w_m2 /\
   moi_s5w_r1 INTER moi_s5w_m2 SUBSET (segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[-- &1;&1]:real^2)] UNION segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[&1;-- &1]:real^2)]) /\ moi_s5w_l1 SUBSET moi_s5w_r1`,
  SUBGOAL_THEN `moi_s5w_r1 SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5W_CONE_EQ] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed moi_s5w_r1 /\ pl_polyhedron moi_s5w_r1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5W_R1_HULLS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      SIMP_TAC[FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY];
      REWRITE_TAC[pl_polyhedron] THEN
      EXISTS_TAC `{convex hull {(vector[&3 / &2; &3 / &2]:real^2),(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)}, convex hull {(vector[&3 / &2; &3 / &2]:real^2),(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)}}` THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY; UNIONS_2] THEN
      SIMP_TAC[POLYTOPE_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_l1 SUBSET moi_s5w_r1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; moi_s5w_r1; MOI_CON_IN_CONE] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^2`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_m2 SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) = moi_s5w_r1 UNION moi_s5w_m2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5w_m2] THEN
    MP_TAC(ISPEC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF moi_s5w_r1` CLOSURE_SUBSET) THEN
    SUBGOAL_THEN `closure((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF moi_s5w_r1) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s5w_r1 SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN
    SPEC_TAC(`closure((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF moi_s5w_r1)`,`cc:real^2->bool`) THEN
    SPEC_TAC(`moi_s5w_r1`,`rr:real^2->bool`) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_S5W_CONE_EQ; IN_ELIM_THM;
                MOI_S5C_IN_RF2] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    MP_TAC(SPEC `z:real^2` MOI_S5W_DEL_BOUND) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; MOI_S5W_CONE_EQ; IN_ELIM_THM; MOI_S5W_IN_L1] THEN
      SIMP_TAC[];
      UNDISCH_TAC `moi_s5w_l1 SUBSET moi_s5w_r1` THEN MP_TAC MOI_S5W_L1_FACTS THEN SET_TAC[]];
    REWRITE_TAC[moi_s5w_m2; CLOSED_CLOSURE];
    REWRITE_TAC[moi_s5w_m2] THEN MATCH_MP_TAC MOI_S5C_CLOSURE_DIFF_POLYHEDRON THEN
    ASM_REWRITE_TAC[MOI_S5C_SQANN_POLYHEDRON];
    SUBGOAL_THEN
     `moi_s5w_m2 SUBSET {z:real^2 | &1 * z$1 + &1 * z$2 + &0 <= &0 \/
                              &1 * z$1 + -- &5 * z$2 + &6 <= &0 \/
                              -- &5 * z$1 + &1 * z$2 + &6 <= &0}`
    MP_TAC THENL
     [REWRITE_TAC[moi_s5w_m2] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF; MOI_S5W_CONE_EQ; IN_ELIM_THM] THEN
        X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[SET_RULE `{z:real^2 | P z \/ Q z \/ R z} =
                              {z | P z} UNION {z | Q z} UNION {z | R z}`] THEN
        REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
        REWRITE_TAC[MOI_S5W_CLOSED_LIN]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^2) IN moi_s5w_r1` THEN
    REWRITE_TAC[MOI_S5W_CONE_EQ; IN_ELIM_THM; MOI_S5C_IN_SQANN] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNION; IN_SEGMENT] THENL
     [SUBGOAL_THEN `z = (vector[-- &1;&1]:real^2) \/ z = (vector[&1;-- &1]:real^2)` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
        DISJ1_TAC THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
        VECTOR_ARITH_TAC;
        DISJ2_TAC THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
        VECTOR_ARITH_TAC];
      DISJ1_TAC THEN EXISTS_TAC `&3 - &2 * (z:real^2)$2` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN EXISTS_TAC `&3 - &2 * (z:real^2)$1` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_2] THEN ASM_REAL_ARITH_TAC]]);;

(* The cone twist.                                                           *)

(* Pasting a PLH of the cone region R1 that fixes S1 with the identity.     *)

let MOI_S5W_PASTE_MAP = prove
 (`!k:real^2->real^2.
     pl_map_on moi_s5w_r1 k /\ (!z. z IN (segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[-- &1;&1]:real^2)] UNION segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[&1;-- &1]:real^2)]) ==> k z = z)
     ==> pl_map_on (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) (\z. if z IN moi_s5w_r1 then k z else z)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1")) THEN
  MP_TAC MOI_S5W_R1_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^2. z IN moi_s5w_r1 /\ z IN moi_s5w_m2 ==> k z = z` (LABEL_TAC "ov") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "s1" MATCH_MP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; IN_INTER] o check (fun th ->
      aconv (concl th) `moi_s5w_r1 INTER moi_s5w_m2 SUBSET (segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[-- &1;&1]:real^2)] UNION segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[&1;-- &1]:real^2)])`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) = moi_s5w_r1 UNION moi_s5w_m2` SUBST1_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `k:real^2->real^2` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\z:real^2. z` THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "ov" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[SUBSET_UNION];
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[SUBSET_UNION]]);;

let MOI_S5W_PASTE = prove
 (`!h h':real^2->real^2.
     pl_homeomorphism (moi_s5w_r1,moi_s5w_r1) (h,h') /\
     (!z. z IN (segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[-- &1;&1]:real^2)] UNION segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[&1;-- &1]:real^2)]) ==> h z = z /\ h' z = z)
     ==> pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])))
           ((\z. if z IN moi_s5w_r1 then h z else z),(\z. if z IN moi_s5w_r1 then h' z else z))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1")) THEN
  FIRST_ASSUM(LABEL_TAC "pts" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  ABBREV_TAC `H = \z:real^2. if z IN moi_s5w_r1 then (h:real^2->real^2) z else z` THEN
  ABBREV_TAC `H' = \z:real^2. if z IN moi_s5w_r1 then (h':real^2->real^2) z else z` THEN
  SUBGOAL_THEN `pl_map_on (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) (H:real^2->real^2) /\ pl_map_on (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) (H':real^2->real^2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "H'"] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S5W_PASTE_MAP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) ==> (H:real^2->real^2) x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\
                  (H':real^2->real^2) x IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ H' (H x) = x /\ H (H' x) = x`
  (LABEL_TAC "pp") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["H"; "H'"] THEN
    ASM_CASES_TAC `(x:real^2) IN moi_s5w_r1` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pts" (MP_TAC o SPECL [`x:real^2`; `x:real^2`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT1 MOI_S5W_R1_FACTS) THEN REWRITE_TAC[SUBSET] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN EXISTS_TAC `(H':real^2->real^2) y` THEN ASM_SIMP_TAC[];
    STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN EXISTS_TAC `(H:real^2->real^2) y` THEN ASM_SIMP_TAC[]]);;

let MOI_S5W_ARC_TWIST = prove
 (`!g g':real^2->real^2.
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\
     (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 + x$2 <= &0 ==> g x = x)
     ==> moi_s5w_ext g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lo")) THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `g':real^2->real^2`] MOI_S5W_LOW_FIX) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; USE_THEN "lo" ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lo'") STRIP_ASSUME_TAC)] THEN
  MP_TAC MOI_S5W_L1_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s5w_l1`; `moi_s5w_l1`; `(vector[&3 / &2; &3 / &2]:real^2)`; `(vector[&3 / &2; &3 / &2]:real^2)`; `g:real^2->real^2`;
                 `g':real^2->real^2`] MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_s5w_r1] THEN
  ABBREV_TAC `ps = moi_con_conemap moi_s5w_l1 (vector[&3 / &2; &3 / &2]:real^2) (vector[&3 / &2; &3 / &2]:real^2) (g:real^2->real^2)` THEN
  ABBREV_TAC `qs = moi_con_conemap moi_s5w_l1 (vector[&3 / &2; &3 / &2]:real^2) (vector[&3 / &2; &3 / &2]:real^2) (g':real^2->real^2)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base")) THEN
  SUBGOAL_THEN `(vector[-- &1;&1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ (vector[-- &1;&1]:real^2)$1 + (vector[-- &1;&1]:real^2)$2 <= &0 /\
                (vector[&1;-- &1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ (vector[&1;-- &1]:real^2)$1 + (vector[&1;-- &1]:real^2)$2 <= &0 /\
                (vector[-- &1;&1]:real^2) IN moi_s5w_l1 /\ (vector[&1;-- &1]:real^2) IN moi_s5w_l1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5W_IN_L1; MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2) (vector[-- &1;&1]:real^2) = (vector[-- &1;&1]:real^2) /\ g (vector[&1;-- &1]:real^2) = (vector[&1;-- &1]:real^2) /\
                (g':real^2->real^2) (vector[-- &1;&1]:real^2) = (vector[-- &1;&1]:real^2) /\ g' (vector[&1;-- &1]:real^2) = (vector[&1;-- &1]:real^2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "lo" MATCH_MP_TAC; USE_THEN "lo" MATCH_MP_TAC;
      USE_THEN "lo'" MATCH_MP_TAC; USE_THEN "lo'" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN (segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[-- &1;&1]:real^2)] UNION segment[(vector[&3 / &2; &3 / &2]:real^2),(vector[&1;-- &1]:real^2)]) ==> (ps:real^2->real^2) z = z /\ (qs:real^2->real^2) z = z`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_SEGMENT] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % a + u % b:real^N = a + u % (b - a)`] THEN
    MAP_EVERY EXPAND_TAC ["ps"; "qs"] THEN
    ASM_SIMP_TAC[MOI_CON_CONEMAP_EQ];
    ALL_TAC] THEN
  MP_TAC MOI_S5W_R1_FACTS THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s5w_ext] THEN
  MAP_EVERY EXISTS_TAC [`\z:real^2. if z IN moi_s5w_r1 then (ps:real^2->real^2) z else z`;
                        `\z:real^2. if z IN moi_s5w_r1 then (qs:real^2->real^2) z else z`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5W_PASTE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((z:real^2) IN moi_s5w_r1)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `moi_s5w_r1 INTER (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) = {}` THEN UNDISCH_TAC `(z:real^2) IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))` THEN
    SPEC_TAC(`(relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`,`c:real^2->bool`) THEN SPEC_TAC(`moi_s5w_r1`,`r:real^2->bool`) THEN
    SET_TAC[];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [USE_THEN "base" MATCH_MP_TAC THEN
      UNDISCH_TAC `moi_s5w_r1 INTER (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = moi_s5w_l1` THEN
      UNDISCH_TAC `(z:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN UNDISCH_TAC `(z:real^2) IN moi_s5w_r1` THEN
      SPEC_TAC(`(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,`c:real^2->bool`) THEN SPEC_TAC(`moi_s5w_r1`,`r:real^2->bool`) THEN
      SPEC_TAC(`moi_s5w_l1`,`l:real^2->bool`) THEN SET_TAC[];
      CONV_TAC SYM_CONV THEN USE_THEN "lo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `~(&0 <= a) ==> a <= &0`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((z:real^2) IN moi_s5w_r1)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s5w_l1 SUBSET moi_s5w_r1` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOI_S5W_IN_L1]]]);;

(* ------------------------------------------------------------------------- *)
(* A4: the corner move: for a = (t,1) on the open top edge, a PLH of C1     *)
(* fixing the half x1 + x2 <= 0 and taking a to the corner (1,1).  It is    *)
(* glued from segment maps: [(-1,1),a] onto the top edge, [a,(1,1)] onto    *)
(* [(1,1),(1,0)], the right edge onto [(1,0),(1,-1)], and the identity on   *)
(* the two low edges.                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S5W_SEG_PLH = prove
 (`!(u:real^2) (x:real^2) (v:real^2) (y:real^2).
     ~(u = x) /\ ~(v = y)
     ==> ?f f'. pl_homeomorphism (segment[u,x],segment[v,y]) (f,f') /\
                f u = v /\ f x = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron {x:real^2} /\ pl_polyhedron {y:real^2}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN CONJ_TAC THENL
     [EXISTS_TAC `{{x:real^2}}`; EXISTS_TAC `{{y:real^2}}`] THEN
    REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN MESON_TAC[POLYTOPE_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^2}`; `{y:real^2}`; `u:real^2`; `v:real^2`;
                 `(\z:real^2. y):real^2->real^2`; `(\z:real^2. x):real^2->real^2`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_SING; NOT_INSERT_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[];
      MESON_TAC[];
      ASM_SIMP_TAC[pl_homeomorphism; PL_MAP_ON_CONST; LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
      REWRITE_TAC[homeomorphism; IN_SING; IMAGE_CLAUSES; CONTINUOUS_ON_CONST] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_1; IN_SING] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`moi_con_conemap {x:real^2} u v (\z:real^2. y:real^2)`;
                        `moi_con_conemap {y:real^2} v u (\z:real^2. x:real^2)`] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_CON_CONEMAP_APEX THEN
  ASM_REWRITE_TAC[IN_SING; NOT_INSERT_EMPTY] THEN MESON_TAC[]);;

let MOI_S5W_CM_SEGS = prove
 (`!t. -- &1 <= t /\ t <= &1
       ==> (!x:real^2. x IN segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] <=> x$2 = &1 /\ -- &1 <= x$1 /\ x$1 <= t) /\
           (!x:real^2. x IN segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)] <=> x$2 = &1 /\ t <= x$1 /\ x$1 <= &1) /\
           (!x:real^2. x IN segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)] <=> x$1 = &1 /\ &0 <= x$2 /\ x$2 <= &1) /\
           (!x:real^2. x IN segment[(vector[&1;&0]:real^2),(vector[&1;-- &1]:real^2)] <=> x$1 = &1 /\ -- &1 <= x$2 /\ x$2 <= &0) /\
           (!x:real^2. x IN segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] <=>
                       x$1 = -- &1 /\ -- &1 <= x$2 /\ x$2 <= &1) /\
           (!x:real^2. x IN segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)] <=>
                       x$2 = -- &1 /\ -- &1 <= x$1 /\ x$1 <= &1) /\
           (!x:real^2. x IN segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] <=> x$2 = &1 /\ -- &1 <= x$1 /\ x$1 <= &1) /\
           (!x:real^2. x IN segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)] <=> x$1 = &1 /\ -- &1 <= x$2 /\ x$2 <= &1)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN X_GEN_TAC `x:real^2` THENL
   [MP_TAC(ISPECL [`(vector[-- &1;&1]:real^2)`; `(vector[t;&1]:real^2)`; `x:real^2`] SEGMENT_HORIZONTAL);
    MP_TAC(ISPECL [`(vector[t;&1]:real^2)`; `(vector[&1;&1]:real^2)`; `x:real^2`] SEGMENT_HORIZONTAL);
    MP_TAC(ISPECL [`(vector[&1;&1]:real^2)`; `(vector[&1;&0]:real^2)`; `x:real^2`] SEGMENT_VERTICAL);
    MP_TAC(ISPECL [`(vector[&1;&0]:real^2)`; `(vector[&1;-- &1]:real^2)`; `x:real^2`] SEGMENT_VERTICAL);
    MP_TAC(ISPECL [`(vector[-- &1;&1]:real^2)`; `(vector[-- &1;-- &1]:real^2)`; `x:real^2`] SEGMENT_VERTICAL);
    MP_TAC(ISPECL [`(vector[-- &1;-- &1]:real^2)`; `(vector[&1;-- &1]:real^2)`; `x:real^2`] SEGMENT_HORIZONTAL);
    MP_TAC(ISPECL [`(vector[-- &1;&1]:real^2)`; `(vector[&1;&1]:real^2)`; `x:real^2`] SEGMENT_HORIZONTAL);
    MP_TAC(ISPECL [`(vector[&1;&1]:real^2)`; `(vector[&1;-- &1]:real^2)`; `x:real^2`] SEGMENT_VERTICAL)] THEN
  REWRITE_TAC[VECTOR_2] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S5W_CM_SETS = prove
 (`!t. -- &1 < t /\ t < &1
       ==> segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] INTER segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)] = {(vector[t;&1]:real^2)} /\
           segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] INTER segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)] = {(vector[&1;&1]:real^2)} /\
           (segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]) INTER segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)] = {(vector[&1;&1]:real^2)} /\
           (segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)]) INTER segment[(vector[&1;&0]:real^2),(vector[&1;-- &1]:real^2)] = {(vector[&1;&0]:real^2)} /\
           ((segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]) UNION segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)]) INTER (segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)]) = {(vector[-- &1;&1]:real^2),(vector[&1;-- &1]:real^2)} /\
           ((segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)]) UNION segment[(vector[&1;&0]:real^2),(vector[&1;-- &1]:real^2)]) INTER (segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)]) = {(vector[-- &1;&1]:real^2),(vector[&1;-- &1]:real^2)} /\
           ((segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]) UNION segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)]) UNION (segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)]) = (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
           ((segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)]) UNION segment[(vector[&1;&0]:real^2),(vector[&1;-- &1]:real^2)]) UNION (segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)]) = (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
           (vector[t;&1]:real^2) IN segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] /\ (vector[-- &1;&1]:real^2) IN segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] /\ ~((vector[&1;&1]:real^2) IN segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)]) /\
           ~((vector[&1;-- &1]:real^2) IN segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]) /\
           (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 + x$2 <= &0 ==> x IN (segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)]))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `t:real` MOI_S5W_CM_SEGS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_SING; IN_INSERT; NOT_IN_EMPTY;
                  MOI_S5C_IN_RF1] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `x:real^2`) THEN ASM_REAL_ARITH_TAC);;

let MOI_S5W_LOW_PLH = prove
 (`pl_homeomorphism ((segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)]),(segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)])) ((\x:real^2. x),(\x:real^2. x))`,
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)], segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)]}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_SEGMENT; UNIONS_2]);;

let MOI_S5W_CORNER_MOVE = prove
 (`!t. -- &1 < t /\ t < &1
       ==> ?g g'. pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\
                  (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 + x$2 <= &0 ==> g x = x) /\
                  g (vector[t; &1]) = (vector[&1;&1]:real^2)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `t:real` MOI_S5W_CM_SETS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(vector[-- &1;&1]:real^2)`; `(vector[t;&1]:real^2)`; `(vector[-- &1;&1]:real^2)`; `(vector[&1;&1]:real^2)`] MOI_S5W_SEG_PLH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^2` (X_CHOOSE_THEN `f1':real^2->real^2`
      STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`(vector[t;&1]:real^2)`; `(vector[&1;&1]:real^2)`; `(vector[&1;&1]:real^2)`; `(vector[&1;&0]:real^2)`] MOI_S5W_SEG_PLH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^2` (X_CHOOSE_THEN `f2':real^2->real^2`
      STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`(vector[&1;&1]:real^2)`; `(vector[&1;-- &1]:real^2)`; `(vector[&1;&0]:real^2)`; `(vector[&1;-- &1]:real^2)`] MOI_S5W_SEG_PLH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `f3:real^2->real^2` (X_CHOOSE_THEN `f3':real^2->real^2`
      STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)]`; `segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]`; `segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)]`; `segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)]`;
                 `f1:real^2->real^2`; `f1':real^2->real^2`;
                 `f2:real^2->real^2`; `f2':real^2->real^2`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLOSED_SEGMENT; IN_SING; IMAGE_CLAUSES] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g12 = \x:real^2. if x IN segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] then (f1:real^2->real^2) x else f2 x` THEN
  ABBREV_TAC `g12' = \y:real^2. if y IN segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] then (f1':real^2->real^2) y else f2' y` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(g12:real^2->real^2) (vector[t;&1]:real^2) = (vector[&1;&1]:real^2) /\ g12 (vector[&1;&1]:real^2) = (vector[&1;&0]:real^2) /\ g12 (vector[-- &1;&1]:real^2) = (vector[-- &1;&1]:real^2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g12" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]`; `segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)]`; `segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)]`; `segment[(vector[&1;&0]:real^2),(vector[&1;-- &1]:real^2)]`;
                 `g12:real^2->real^2`; `g12':real^2->real^2`;
                 `f3:real^2->real^2`; `f3':real^2->real^2`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_SEGMENT; CLOSED_UNION; IN_SING; IMAGE_CLAUSES];
    ALL_TAC] THEN
  ABBREV_TAC `g123 = \x:real^2. if x IN segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)] then (g12:real^2->real^2) x
                                else f3 x` THEN
  ABBREV_TAC `g123' = \y:real^2. if y IN segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)] then (g12':real^2->real^2) y
                                 else f3' y` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(g123:real^2->real^2) (vector[t;&1]:real^2) = (vector[&1;&1]:real^2) /\ g123 (vector[-- &1;&1]:real^2) = (vector[-- &1;&1]:real^2) /\ g123 (vector[&1;-- &1]:real^2) = (vector[&1;-- &1]:real^2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g123" THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]) UNION segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)]`; `(segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)])`;
                 `(segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)]) UNION segment[(vector[&1;&0]:real^2),(vector[&1;-- &1]:real^2)]`; `(segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)])`;
                 `g123:real^2->real^2`; `g123':real^2->real^2`;
                 `\x:real^2. x`; `\x:real^2. x`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_SEGMENT; CLOSED_UNION; MOI_S5W_LOW_PLH; IN_INSERT;
                 NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
    GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^2. if x IN (segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]) UNION segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)] then (g123:real^2->real^2) x
                else (\x:real^2. x) x`;
    `\y:real^2. if y IN (segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;&0]:real^2)]) UNION segment[(vector[&1;&0]:real^2),(vector[&1;-- &1]:real^2)] then (g123':real^2->real^2) y
                else (\x:real^2. x) y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^2) IN ((segment[(vector[-- &1;&1]:real^2),(vector[t;&1]:real^2)] UNION segment[(vector[t;&1]:real^2),(vector[&1;&1]:real^2)]) UNION segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)]) INTER (segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)])` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_UNION]]);;

(* ------------------------------------------------------------------------- *)
(* A5: moving points of C1 by extendable PLHs of C1 (corner moves and their  *)
(* conjugates by symmetries of the square), keeping a point k fixed.        *)
(* ------------------------------------------------------------------------- *)

let moi_s5w_move = new_definition
 `moi_s5w_move (k:real^2) p q <=>
    ?g g'. pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\ moi_s5w_ext g /\
           (k IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> g k = k) /\ g p = q`;;

(* (k is a point that must stay fixed; with k outside C1 there is no         *)
(* condition.)                                                               *)

let MOI_S5W_MOV_REFL = prove
 (`!k p:real^2. moi_s5w_move k p p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5w_move] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^2. x`; `\x:real^2. x`] THEN
  REWRITE_TAC[MOI_S5W_EXT_ID; pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID; MOI_S5W_MM_POLY]);;

let MOI_S5W_MOV_TRANS = prove
 (`!k p q r:real^2.
     moi_s5w_move k p q /\ moi_s5w_move k q r ==> moi_s5w_move k p r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5w_move] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g1:real^2->real^2` (X_CHOOSE_THEN `g1':real^2->real^2`
      STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `g2:real^2->real^2` (X_CHOOSE_THEN `g2':real^2->real^2`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`(g2:real^2->real^2) o (g1:real^2->real^2)`;
                        `(g1':real^2->real^2) o (g2':real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5W_EXT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th -> aconv (concl th)
        `pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) ((g1:real^2->real^2),g1')`)) THEN
    MESON_TAC[];
    DISCH_TAC THEN ASM_SIMP_TAC[o_THM];
    ASM_REWRITE_TAC[o_THM]]);;

let MOI_S5W_MOV_SYM = prove
 (`!k p q:real^2. moi_s5w_move k p q /\ p IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> moi_s5w_move k q p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5w_move] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g:real^2->real^2` (X_CHOOSE_THEN `g':real^2->real^2`
      STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`g':real^2->real^2`; `g:real^2->real^2`] THEN
  FIRST_ASSUM(LABEL_TAC "pts" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_S5W_EXT_INV THEN EXISTS_TAC `g:real^2->real^2` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^2->real^2) k = k` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
     [ASM_SIMP_TAC[]; ASM_MESON_TAC[]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `q:real^2`)) THEN
    ASM_MESON_TAC[]]);;

let MOI_S5W_MOV_CONJ = prove
 (`!s k p q:real^2.
     moi_s5w_sym s /\ moi_s5w_move (s k) p q ==> moi_s5w_move k (s p) (s q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s5w_sym]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5W_SYM_FACTS) THEN
  REWRITE_TAC[moi_s5w_move] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^2` (X_CHOOSE_THEN `g':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`((s:real^2->real^2) o g) o s`; `(s:real^2->real^2) o g' o s`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5W_EXT_EQ THEN EXISTS_TAC `\x:real^2. (s:real^2->real^2) ((g:real^2->real^2) (s x))` THEN
    ASM_SIMP_TAC[MOI_S5W_EXT_CONJ; o_THM];
    DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g:real^2->real^2) ((s:real^2->real^2) k) = s k` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[o_THM]]);;

(* The basic move: (t,1) -> (1,1), fixing x1 + x2 <= 0.                     *)

let MOI_S5W_MOV_BASE = prove
 (`!t k. -- &1 < t /\ t < &1 /\ (k IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> k$1 + k$2 <= &0)
         ==> moi_s5w_move k (vector[t; &1]) (vector[&1;&1]:real^2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `t:real` MOI_S5W_CORNER_MOVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^2` (X_CHOOSE_THEN `g':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s5w_move] THEN
  MAP_EVERY EXISTS_TAC [`g:real^2->real^2`; `g':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5W_ARC_TWIST THEN EXISTS_TAC `g':real^2->real^2` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A5b: every point of C1 moves to (1,1); every point other than (1,1)      *)
(* moves to (-1,-1) keeping (1,1) fixed.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5W_MOV_CONJ0 = prove
 (`!s p q:real^2.
     moi_s5w_sym s /\ moi_s5w_move (vec 0) p q ==> moi_s5w_move (vec 0) (s p) (s q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5W_MOV_CONJ THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^2->real^2) (vec 0) = vec 0` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(ISPEC `s:real^2->real^2` LINEAR_0) THEN
  UNDISCH_TAC `moi_s5w_sym s` THEN SIMP_TAC[moi_s5w_sym]);;

let MOI_S5W_C1_CASES = prove
 (`!a b. max (abs a) (abs b) = &1
     ==> (-- &1 < a /\ a < &1 /\ b = &1) \/ (a = &1 /\ -- &1 < b /\ b < &1) \/
         (a = -- &1 /\ -- &1 < b /\ b < &1) \/ (-- &1 < a /\ a < &1 /\ b = -- &1) \/
         (a = &1 /\ b = &1) \/ (a = -- &1 /\ b = &1) \/
         (a = -- &1 /\ b = -- &1) \/ (a = &1 /\ b = -- &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `b = &1` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `a = &1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `a = -- &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `b = -- &1` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `a = &1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `a = -- &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a = &1` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `a = -- &1` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5W_IN_C1_PTS = prove
 (`!t. -- &1 < t /\ t < &1
       ==> vector[t; &1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ vector[&1; t] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
           vector[-- &1; t] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ vector[t; -- &1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S5W_TO_K1 = prove
 (`!q:real^2. q IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> moi_s5w_move (vec 0) q (vector[&1;&1]:real^2)`,
  MP_TAC MOI_S5W_SYMS THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((vec 0:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5C_IN_RF1; VEC_COMPONENT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vec 0) (vector[t; &1]) (vector[&1;&1]:real^2)`
  (LABEL_TAC "top") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5W_MOV_BASE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vec 0) (vector[&1; t]) (vector[&1;&1]:real^2)`
  (LABEL_TAC "right") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[x$2; x$1]:real^2)`; `vector[t; &1]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ0) THEN
    ASM_SIMP_TAC[VECTOR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_move (vec 0) (vector[-- &1;&1]:real^2) (vector[&1;&1]:real^2)` (LABEL_TAC "k2") THENL
   [MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN EXISTS_TAC `vector[&0; &1]:real^2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5W_MOV_SYM THEN
      REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MP_TAC(ISPECL [`(\x:real^2. vector[--(x$1); x$2]:real^2)`; `vector[&0; &1]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ0) THEN
      ASM_SIMP_TAC[VECTOR_2; REAL_NEG_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "top" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "top" MATCH_MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_move (vec 0) (vector[&1;-- &1]:real^2) (vector[&1;&1]:real^2)` (LABEL_TAC "k4") THENL
   [MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN EXISTS_TAC `vector[&1; &0]:real^2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5W_MOV_SYM THEN
      REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MP_TAC(ISPECL [`(\x:real^2. vector[x$1; --(x$2)]:real^2)`; `vector[&1; &0]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ0) THEN
      ASM_SIMP_TAC[VECTOR_2; REAL_NEG_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "right" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "right" MATCH_MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vec 0) (vector[-- &1; t]) (vector[&1;&1]:real^2)`
  (LABEL_TAC "left") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN
    EXISTS_TAC `(vector[-- &1;&1]:real^2)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[--(x$1); x$2]:real^2)`; `vector[&1; t]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ0) THEN
    ASM_SIMP_TAC[VECTOR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vec 0) (vector[t; -- &1]) (vector[&1;&1]:real^2)`
  (LABEL_TAC "bottom") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN
    EXISTS_TAC `(vector[&1;-- &1]:real^2)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[x$1; --(x$2)]:real^2)`; `vector[t; &1]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ0) THEN
    ASM_SIMP_TAC[VECTOR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_move (vec 0) (vector[-- &1;-- &1]:real^2) (vector[&1;&1]:real^2)` (LABEL_TAC "k3") THENL
   [MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN EXISTS_TAC `vector[&0; -- &1]:real^2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5W_MOV_SYM THEN
      REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MP_TAC(ISPECL [`(\x:real^2. vector[--(x$1); --(x$2)]:real^2)`; `vector[&0; &1]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ0) THEN
      ASM_SIMP_TAC[VECTOR_2; REAL_NEG_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "top" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "bottom" MATCH_MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q = vector[(q:real^2)$1; q$2]` SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`(q:real^2)$1`; `(q:real^2)$2`] MOI_S5W_C1_CASES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5C_IN_RF1]; ALL_TAC] THEN
  SPEC_TAC(`(q:real^2)$2`,`b:real`) THEN SPEC_TAC(`(q:real^2)$1`,`a:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_S5W_MOV_REFL]);;

let MOI_S5W_C1_INDUCT = prove
 (`!P. (!t. -- &1 < t /\ t < &1 ==> P (vector[t; &1])) /\
       (!t. -- &1 < t /\ t < &1 ==> P (vector[&1; t])) /\
       (!t. -- &1 < t /\ t < &1 ==> P (vector[-- &1; t])) /\
       (!t. -- &1 < t /\ t < &1 ==> P (vector[t; -- &1])) /\
       P (vector[&1;&1]:real^2) /\ P (vector[-- &1;&1]:real^2) /\ P (vector[-- &1;-- &1]:real^2) /\ P (vector[&1;-- &1]:real^2)
       ==> !q:real^2. q IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> P q`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q = vector[(q:real^2)$1; q$2]` SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`(q:real^2)$1`; `(q:real^2)$2`] MOI_S5W_C1_CASES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5C_IN_RF1]; ALL_TAC] THEN
  SPEC_TAC(`(q:real^2)$2`,`b:real`) THEN SPEC_TAC(`(q:real^2)$1`,`a:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S5W_TO_K3 = prove
 (`!q:real^2. q IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ~(q = (vector[&1;&1]:real^2)) ==> moi_s5w_move (vector[&1;&1]:real^2) q (vector[-- &1;-- &1]:real^2)`,
  MP_TAC MOI_S5W_SYMS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vector[&1;&1]:real^2) (vector[t; -- &1]) (vector[-- &1;-- &1]:real^2)`
  (LABEL_TAC "bot") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[--(x$1); --(x$2)]:real^2)`; `(vector[&1;&1]:real^2)`; `vector[--t; &1]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ) THEN
    ASM_REWRITE_TAC[VECTOR_2; REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_S5W_MOV_BASE THEN REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vector[&1;&1]:real^2) (vector[-- &1; t]) (vector[-- &1;-- &1]:real^2)`
  (LABEL_TAC "left") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[x$2; x$1]:real^2)`; `(vector[&1;&1]:real^2)`; `vector[t; -- &1]:real^2`; `(vector[-- &1;-- &1]:real^2)`] MOI_S5W_MOV_CONJ) THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "bot" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vector[&1;&1]:real^2) (vector[t; &1]) (vector[-- &1;&1]:real^2)`
  (LABEL_TAC "topk2") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[--(x$1); x$2]:real^2)`; `(vector[&1;&1]:real^2)`; `vector[--t; &1]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ) THEN
    ASM_REWRITE_TAC[VECTOR_2; REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_S5W_MOV_BASE THEN REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vector[&1;&1]:real^2) (vector[&1; t]) (vector[&1;-- &1]:real^2)`
  (LABEL_TAC "rightk4") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[x$2; x$1]:real^2)`; `(vector[&1;&1]:real^2)`; `vector[t; &1]:real^2`; `(vector[-- &1;&1]:real^2)`] MOI_S5W_MOV_CONJ) THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "topk2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vector[&1;&1]:real^2) (vector[t; -- &1]) (vector[&1;-- &1]:real^2)`
  (LABEL_TAC "botk4") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[x$1; --(x$2)]:real^2)`; `(vector[&1;&1]:real^2)`; `vector[t; &1]:real^2`; `(vector[&1;&1]:real^2)`] MOI_S5W_MOV_CONJ) THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_S5W_MOV_BASE THEN REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. -- &1 < t /\ t < &1 ==> moi_s5w_move (vector[&1;&1]:real^2) (vector[-- &1; t]) (vector[-- &1;&1]:real^2)`
  (LABEL_TAC "leftk2") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\x:real^2. vector[x$2; x$1]:real^2)`; `(vector[&1;&1]:real^2)`; `vector[t; -- &1]:real^2`; `(vector[&1;-- &1]:real^2)`] MOI_S5W_MOV_CONJ) THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "botk4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_move (vector[&1;&1]:real^2) (vector[-- &1;&1]:real^2) (vector[-- &1;-- &1]:real^2)` (LABEL_TAC "k2") THENL
   [MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN EXISTS_TAC `vector[-- &1; &0]:real^2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5W_MOV_SYM THEN
      REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      USE_THEN "leftk2" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "left" MATCH_MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_move (vector[&1;&1]:real^2) (vector[&1;-- &1]:real^2) (vector[-- &1;-- &1]:real^2)` (LABEL_TAC "k4") THENL
   [MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN EXISTS_TAC `vector[&0; -- &1]:real^2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5W_MOV_SYM THEN
      REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      USE_THEN "botk4" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "bot" MATCH_MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC MOI_S5W_C1_INDUCT THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN TRY DISCH_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[MOI_S5W_MOV_REFL] THENL
   [MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN EXISTS_TAC `(vector[-- &1;&1]:real^2)` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MOI_S5W_MOV_TRANS THEN EXISTS_TAC `(vector[&1;-- &1]:real^2)` THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    UNDISCH_TAC `~((vector[&1;&1]:real^2) = (vector[&1;&1]:real^2))` THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A6: a PLH of C1 fixing (1,1) and (-1,-1) keeps or swaps the two open     *)
(* arcs x1 < x2 and x2 < x1; if it keeps them it is a product of two         *)
(* half-supported PLHs, each a conjugated cone twist, hence extendable.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5W_DIAG = prove
 (`!x:real^2. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 = x$2 ==> x = (vector[&1;&1]:real^2) \/ x = (vector[-- &1;-- &1]:real^2)`,
  GEN_TAC THEN REWRITE_TAC[MOI_S5C_IN_RF1; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S5W_D_EQ = prove
 (`{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2} = (segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] DELETE (vector[-- &1;-- &1]:real^2)) UNION (segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] DELETE (vector[&1;&1]:real^2)) /\
   {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1} = (segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)] DELETE (vector[-- &1;-- &1]:real^2)) UNION (segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)] DELETE (vector[&1;&1]:real^2))`,
  MP_TAC(SPEC `&0` MOI_S5W_CM_SEGS) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_DELETE; MOI_S5C_IN_RF1] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN REAL_ARITH_TAC);;

let MOI_S5W_D_CONN = prove
 (`connected {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2} /\ connected {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1}`,
  REWRITE_TAC[MOI_S5W_D_EQ] THEN CONJ_TAC THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DELETE] THENL
   [EXISTS_TAC `(vector[-- &1;&1]:real^2)`; EXISTS_TAC `(vector[&1;-- &1]:real^2)`] THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S5W_OPEN_LT = prove
 (`open {x:real^2 | x$1 < x$2} /\ open {x:real^2 | x$2 < x$1}`,
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`basis 1 - basis 2:real^2`; `&0`] OPEN_HALFSPACE_LT);
    MP_TAC(ISPECL [`basis 2 - basis 1:real^2`; `&0`] OPEN_HALFSPACE_LT)] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_LSUB] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let MOI_S5W_ARC_SIDE = prove
 (`!g g' d. pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\ g (vector[&1;&1]:real^2) = (vector[&1;&1]:real^2) /\ g (vector[-- &1;-- &1]:real^2) = (vector[-- &1;-- &1]:real^2) /\
            connected d /\ d SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ~((vector[&1;&1]:real^2) IN d) /\ ~((vector[-- &1;-- &1]:real^2) IN d)
            ==> (!x. x IN d ==> ((g:real^2->real^2) x)$1 < (g x)$2) \/
                (!x. x IN d ==> ((g:real^2->real^2) x)$2 < (g x)$1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "pts" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `(vector[&1;&1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ (vector[-- &1;-- &1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN d ==> ~(((g:real^2->real^2) x)$1 = (g x)$2)`
  (LABEL_TAC "ne") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MP_TAC(SPEC `(g:real^2->real^2) x` MOI_S5W_DIAG) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g':real^2->real^2) ((g:real^2->real^2) x) = x /\
                  g' (g (vector[&1;&1]:real^2)) = (vector[&1;&1]:real^2) /\ g' (g (vector[-- &1;-- &1]:real^2)) = (vector[-- &1;-- &1]:real^2)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(g:real^2->real^2) x`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?x:real^2. x IN d /\ ((g:real^2->real^2) x)$1 < (g x)$2` THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`IMAGE (g:real^2->real^2) d`; `{x:real^2 | x$2 < x$1}`;
                   `{x:real^2 | x$1 < x$2}`] MOI_S5C_CONN_SUB) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MOI_S5W_OPEN_LT] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
        ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        USE_THEN "ne" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN d`)) THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN
        ASM_MESON_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]];
    DISJ2_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "ne" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN d`)) THEN
    UNDISCH_TAC `~(?x:real^2. x IN d /\ ((g:real^2->real^2) x)$1 < (g x)$2)` THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_S5W_SIDES = prove
 (`!g g':real^2->real^2.
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\ g (vector[&1;&1]:real^2) = (vector[&1;&1]:real^2) /\ g (vector[-- &1;-- &1]:real^2) = (vector[-- &1;-- &1]:real^2)
     ==> ((!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2 ==> (g x)$1 < (g x)$2) /\
          (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1 ==> (g x)$2 < (g x)$1)) \/
         ((!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2 ==> (g x)$2 < (g x)$1) /\
          (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1 ==> (g x)$1 < (g x)$2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "pts" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2} SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ~((vector[&1;&1]:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2}) /\ ~((vector[-- &1;-- &1]:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2}) /\
                {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1} SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ~((vector[&1;&1]:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1}) /\ ~((vector[-- &1;-- &1]:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; VECTOR_2] THEN REPEAT CONJ_TAC THEN
    TRY(SIMP_TAC[] THEN NO_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ~(y = (vector[&1;&1]:real^2)) /\ ~(y = (vector[-- &1;-- &1]:real^2))
                ==> ?z. z IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ (z$1 < z$2 \/ z$2 < z$1) /\ (g:real^2->real^2) z = y`
  (LABEL_TAC "sur") THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `(g':real^2->real^2) y` THEN
    USE_THEN "pts" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(y:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
      SPECL [`y:real^2`; `y:real^2`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `~(a:real = b) ==> a < b \/ b < a`) THEN DISCH_TAC THEN
    MP_TAC(SPEC `(g':real^2->real^2) y` MOI_S5W_DIAG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `g':real^2->real^2`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2}`] MOI_S5W_ARC_SIDE) THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `g':real^2->real^2`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1}`] MOI_S5W_ARC_SIDE) THEN
  ASM_REWRITE_TAC[MOI_S5W_D_CONN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN (LABEL_TAC "b")) THEN
  DISCH_THEN(DISJ_CASES_THEN (LABEL_TAC "a")) THEN
  ASM_REWRITE_TAC[] THENL
   [USE_THEN "sur" (MP_TAC o SPEC `(vector[&1;-- &1]:real^2)`);
    USE_THEN "sur" (MP_TAC o SPEC `(vector[-- &1;&1]:real^2)`)] THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[MOI_S5C_IN_RF1; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC))) THENL
   [USE_THEN "a" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(z:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                                           (ASSUME `(z:real^2)$1 < z$2`)));
    USE_THEN "b" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(z:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                                           (ASSUME `(z:real^2)$2 < z$1`)));
    USE_THEN "a" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(z:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                                           (ASSUME `(z:real^2)$1 < z$2`)));
    USE_THEN "b" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(z:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                                           (ASSUME `(z:real^2)$2 < z$1`)))] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `(g:real^2->real^2) z`)) THEN
  REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S5W_HALVES = prove
 (`{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} = segment[(vector[-- &1;&1]:real^2),(vector[-- &1;-- &1]:real^2)] UNION segment[(vector[-- &1;&1]:real^2),(vector[&1;&1]:real^2)] /\
   {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} = segment[(vector[-- &1;-- &1]:real^2),(vector[&1;-- &1]:real^2)] UNION segment[(vector[&1;&1]:real^2),(vector[&1;-- &1]:real^2)] /\
   {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} UNION {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} = (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} INTER {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} = {(vector[&1;&1]:real^2),(vector[-- &1;-- &1]:real^2)}`,
  MP_TAC(SPEC `&0` MOI_S5W_CM_SEGS) THEN ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_INTER; IN_INSERT; NOT_IN_EMPTY;
                  MOI_S5C_IN_RF1] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN REAL_ARITH_TAC);;

let MOI_S5W_PL_2SEG = prove
 (`!a b c d:real^2.
     pl_polyhedron (segment[a,b] UNION segment[c,d]) /\
     closed (segment[a,b] UNION segment[c,d])`,
  REPEAT GEN_TAC THEN SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT] THEN
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{segment[a:real^2,b], segment[c,d]}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_SEGMENT; UNIONS_2]);;

let MOI_S5W_HALF_FACTS = prove
 (`closed {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} /\ closed {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} /\ pl_polyhedron {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} /\ pl_polyhedron {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} /\
   {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[MOI_S5W_HALVES; MOI_S5W_PL_2SEG]);;

let MOI_S5W_ID_PLH = prove
 (`!s:real^2->bool. pl_polyhedron s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_S5W_RESTRICT = prove
 (`!(g:real^2->real^2) g' (h:real^2->bool).
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\ h SUBSET (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ pl_polyhedron h /\
     IMAGE g h = h
     ==> pl_homeomorphism (h,h) (g,g')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`; `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]);
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [pl_homeomorphism]);
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [pl_homeomorphism])]);;

let MOI_S5W_TWIST_SYM = prove
 (`!s b b':real^2->real^2.
     moi_s5w_sym s /\ pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (b,b') /\
     (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 + x$2 <= &0 ==> b (s x) = s x)
     ==> moi_s5w_ext b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))) THEN
  MP_TAC(REWRITE_RULE[moi_s5w_sym] (ASSUME `moi_s5w_sym (s:real^2->real^2)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5W_SYM_FACTS (ASSUME `moi_s5w_sym (s:real^2->real^2)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s5w_ext (((s:real^2->real^2) o (b:real^2->real^2)) o s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5W_ARC_TWIST THEN
    EXISTS_TAC `(s:real^2->real^2) o (b':real^2->real^2) o s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(b:real^2->real^2) ((s:real^2->real^2) x) = s x` SUBST1_TAC THENL
       [USE_THEN "fix" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->real^2`; `((s:real^2->real^2) o (b:real^2->real^2)) o s`]
    MOI_S5W_EXT_CONJ) THEN
  ASM_REWRITE_TAC[o_THM; ETA_AX]);;

let MOI_S5W_HAB = prove
 (`{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} UNION {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} = (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} INTER {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} = {(vector[&1;&1]:real^2),(vector[-- &1;-- &1]:real^2)}`,
  REWRITE_TAC[CONJUNCT2(CONJUNCT2 MOI_S5W_HALVES)]);;

let MOI_S5W_SPLIT = prove
 (`!g g':real^2->real^2.
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g') /\ g (vector[&1;&1]:real^2) = (vector[&1;&1]:real^2) /\ g (vector[-- &1;-- &1]:real^2) = (vector[-- &1;-- &1]:real^2) /\
     (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 < x$2 ==> (g x)$1 < (g x)$2) /\
     (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 < x$1 ==> (g x)$2 < (g x)$1)
     ==> moi_s5w_ext g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lt") (LABEL_TAC "gt"))))) THEN
  FIRST_ASSUM(LABEL_TAC "pts" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  MP_TAC MOI_S5W_HALF_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^2. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
                 ==> (((g:real^2->real^2) x)$1 <= (g x)$2 <=> x$1 <= x$2) /\
                     ((g x)$2 <= (g x)$1 <=> x$2 <= x$1)` (LABEL_TAC "pa") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^2)$1 < x$2` THENL
     [USE_THEN "lt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                                             (ASSUME `(x:real^2)$1 < x$2`))) THEN
      UNDISCH_TAC `(x:real^2)$1 < x$2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^2)$2 < x$1` THENL
     [USE_THEN "gt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                                             (ASSUME `(x:real^2)$2 < x$1`))) THEN
      UNDISCH_TAC `(x:real^2)$2 < x$1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `x:real^2` MOI_S5W_DIAG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
                 ==> (((g:real^2->real^2) x) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} <=> x IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}) /\
                     ((g x) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} <=> x IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1})` (LABEL_TAC "ph") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "pts" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
      SPECL [`x:real^2`; `x:real^2`]) THEN
    USE_THEN "pa" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^2) {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} = {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} /\ IMAGE g {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} = {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}` THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      USE_THEN "ph" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g':real^2->real^2) y` THEN
      SUBGOAL_THEN `(y:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}` THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      USE_THEN "pts" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(y:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
        SPECL [`y:real^2`; `y:real^2`]) THEN
      USE_THEN "ph" (MP_TAC o C MATCH_MP (ASSUME `(g':real^2->real^2) y IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}` THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      USE_THEN "ph" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g':real^2->real^2) y` THEN
      SUBGOAL_THEN `(y:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}` THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      USE_THEN "pts" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(y:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
        SPECL [`y:real^2`; `y:real^2`]) THEN
      USE_THEN "ph" (MP_TAC o C MATCH_MP (ASSUME `(g':real^2->real^2) y IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism ({x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2},{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}) ((g:real^2->real^2),g') /\
                pl_homeomorphism ({x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1},{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}) ((g:real^2->real^2),g')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5W_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} INTER {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1} ==> (g:real^2->real^2) x = x`
  (LABEL_TAC "agr") THENL
   [REWRITE_TAC[MOI_S5W_HAB; IN_INSERT; NOT_IN_EMPTY] THEN
    GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^2) ({x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} INTER {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}) = {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} INTER {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5W_HAB; IMAGE_CLAUSES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}`; `g:real^2->real^2`; `g':real^2->real^2`;
                 `\x:real^2. x`; `\x:real^2. x`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC MOI_S5W_ID_PLH THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[] THEN USE_THEN "agr" ACCEPT_TAC];
    REWRITE_TAC[MOI_S5W_HAB] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}`; `{x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$2 <= x$1}`; `\x:real^2. x`; `\x:real^2. x`;
                 `g:real^2->real^2`; `g':real^2->real^2`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC MOI_S5W_ID_PLH THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "agr" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IMAGE_ID]];
    REWRITE_TAC[MOI_S5W_HAB] THEN DISCH_TAC] THEN
  ABBREV_TAC `b2 = \x:real^2. if x IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} then (g:real^2->real^2) x else x` THEN
  ABBREV_TAC `b4 = \x:real^2. if x IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} then x else (g:real^2->real^2) x` THEN
  SUBGOAL_THEN `moi_s5w_ext (b2:real^2->real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5W_TWIST_SYM THEN
    MAP_EVERY EXISTS_TAC
     [`(\x:real^2. vector[--(x$1); x$2]:real^2)`; `\y:real^2. if y IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} then (g':real^2->real^2) y else y`] THEN
    ASM_REWRITE_TAC[MOI_S5W_SYMS] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN EXPAND_TAC "b2" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "agr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    REWRITE_TAC[IN_ELIM_THM; MOI_S5C_IN_RF1; VECTOR_2] THEN
    UNDISCH_TAC `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN UNDISCH_TAC `(x:real^2)$1 + x$2 <= &0` THEN
    REWRITE_TAC[MOI_S5C_IN_RF1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5w_ext (b4:real^2->real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5W_TWIST_SYM THEN
    MAP_EVERY EXISTS_TAC
     [`(\x:real^2. vector[x$1; --(x$2)]:real^2)`; `\y:real^2. if y IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2} then y else (g':real^2->real^2) y`] THEN
    ASM_REWRITE_TAC[MOI_S5W_SYMS] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN EXPAND_TAC "b4" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; MOI_S5C_IN_RF1; VECTOR_2] THEN
    UNDISCH_TAC `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN UNDISCH_TAC `(x:real^2)$1 + x$2 <= &0` THEN
    REWRITE_TAC[MOI_S5C_IN_RF1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5W_EXT_EQ THEN
  EXISTS_TAC `(b2:real^2->real^2) o (b4:real^2->real^2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5W_EXT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
        MOI_S5C_HEAD "pl_homeomorphism" th &&
        can (find_term ((=) `b4:real^2->real^2`)) (concl th))) THEN
    MESON_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MAP_EVERY EXPAND_TAC ["b2"; "b4"] THEN
    ASM_CASES_TAC `(x:real^2) IN {x:real^2 | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ x$1 <= x$2}` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ph" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
    ASM_SIMP_TAC[]]);;

(* Cancelling an extendable PLH on the left.                                *)

let MOI_S5W_EXT_CANCEL = prove
 (`!h h' f:real^2->real^2.
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (h,h') /\ moi_s5w_ext h /\
     moi_s5w_ext (h o f) /\ (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> f x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))
     ==> moi_s5w_ext f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "pts" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `moi_s5w_ext (h':real^2->real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5W_EXT_INV THEN EXISTS_TAC `h:real^2->real^2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5W_EXT_EQ THEN
  EXISTS_TAC `(h':real^2->real^2) o ((h:real^2->real^2) o (f:real^2->real^2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5W_EXT_COMPOSE THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "pts" (MP_TAC o SPECL [`(f:real^2->real^2) x`; `(f:real^2->real^2) x`]) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "pts" (MP_TAC o SPECL [`(f:real^2->real^2) x`; `(f:real^2->real^2) x`]) THEN
    ASM_SIMP_TAC[]]);;

let MOI_S5W_DICHOTOMY_EXT = prove
 (`!g g':real^2->real^2.
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) (g,g')
     ==> moi_s5w_ext g \/ moi_s5w_ext (\x. g (vector[x$2; x$1]))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "gp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `(vector[&1;&1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ (vector[-- &1;-- &1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ ~((vector[-- &1;-- &1]:real^2) = (vector[&1;&1]:real^2))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5C_IN_RF1; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "gp" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(vector[-- &1;-- &1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
    SPECL [`(vector[-- &1;-- &1]:real^2)`; `(vector[-- &1;-- &1]:real^2)`]) THEN
  USE_THEN "gp" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(vector[&1;&1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
    SPECL [`(vector[&1;&1]:real^2)`; `(vector[&1;&1]:real^2)`]) THEN
  MP_TAC(SPEC `(g:real^2->real^2) (vector[&1;&1]:real^2)` MOI_S5W_TO_K1) THEN
  ASM_REWRITE_TAC[moi_s5w_move] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^2` (X_CHOOSE_THEN `h1':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(LABEL_TAC "h1p" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `h1:real^2->real^2`)) (concl th))) THEN
  USE_THEN "h1p" (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `(g:real^2->real^2) (vector[-- &1;-- &1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
    SPECL [`(g:real^2->real^2) (vector[-- &1;-- &1]:real^2)`; `(g:real^2->real^2) (vector[-- &1;-- &1]:real^2)`]) THEN
  USE_THEN "h1p" (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `(g:real^2->real^2) (vector[&1;&1]:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] o
    SPECL [`(g:real^2->real^2) (vector[&1;&1]:real^2)`; `(g:real^2->real^2) (vector[&1;&1]:real^2)`]) THEN
  SUBGOAL_THEN `~((h1:real^2->real^2) ((g:real^2->real^2) (vector[-- &1;-- &1]:real^2)) = (vector[&1;&1]:real^2))` ASSUME_TAC THENL
   [MP_TAC(ASSUME `(h1':real^2->real^2) ((h1:real^2->real^2)
                     ((g:real^2->real^2) (vector[-- &1;-- &1]:real^2))) = g (vector[-- &1;-- &1]:real^2)`) THEN
    MP_TAC(ASSUME `(h1':real^2->real^2) ((h1:real^2->real^2)
                     ((g:real^2->real^2) (vector[&1;&1]:real^2))) = g (vector[&1;&1]:real^2)`) THEN
    MP_TAC(ASSUME `(g':real^2->real^2) ((g:real^2->real^2) (vector[-- &1;-- &1]:real^2)) = (vector[-- &1;-- &1]:real^2)`) THEN
    MP_TAC(ASSUME `(g':real^2->real^2) ((g:real^2->real^2) (vector[&1;&1]:real^2)) = (vector[&1;&1]:real^2)`) THEN
    MP_TAC(ASSUME `(h1:real^2->real^2) ((g:real^2->real^2) (vector[&1;&1]:real^2)) = (vector[&1;&1]:real^2)`) THEN
    MP_TAC(ASSUME `~((vector[-- &1;-- &1]:real^2) = (vector[&1;&1]:real^2))`) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `(h1:real^2->real^2) ((g:real^2->real^2) (vector[-- &1;-- &1]:real^2))` MOI_S5W_TO_K3) THEN
  ASM_REWRITE_TAC[moi_s5w_move] THEN
  DISCH_THEN(X_CHOOSE_THEN `h3:real^2->real^2` (X_CHOOSE_THEN `h3':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(LABEL_TAC "h3p" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `h3:real^2->real^2`)) (concl th))) THEN
  SUBGOAL_THEN `!x:real^2. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> (h3:real^2->real^2) ((h1:real^2->real^2)
                  ((g:real^2->real^2) x)) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` (LABEL_TAC "in3") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "gp" (MP_TAC o SPECL [`x:real^2`; `x:real^2`]) THEN
    USE_THEN "h1p" (MP_TAC o SPECL [`(g:real^2->real^2) x`; `(g:real^2->real^2) x`]) THEN
    USE_THEN "h3p" (MP_TAC o SPECL [`(h1:real^2->real^2) ((g:real^2->real^2) x)`;
                                    `(h1:real^2->real^2) ((g:real^2->real^2) x)`]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))
                 ((h3:real^2->real^2) o ((h1:real^2->real^2) o (g:real^2->real^2)),
                  ((g':real^2->real^2) o (h1':real^2->real^2)) o (h3':real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((h3:real^2->real^2) o ((h1:real^2->real^2) o (g:real^2->real^2))) (vector[&1;&1]:real^2) =
                (vector[&1;&1]:real^2) /\
                ((h3:real^2->real^2) o ((h1:real^2->real^2) o (g:real^2->real^2))) (vector[-- &1;-- &1]:real^2) =
                (vector[-- &1;-- &1]:real^2)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^2->real^2.
                  (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> f x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) /\
                  moi_s5w_ext ((h3:real^2->real^2) o ((h1:real^2->real^2) o f))
                  ==> moi_s5w_ext f` (LABEL_TAC "canc") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S5W_EXT_CANCEL THEN
    MAP_EVERY EXISTS_TAC [`h1:real^2->real^2`; `h1':real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5W_EXT_CANCEL THEN
    MAP_EVERY EXISTS_TAC [`h3:real^2->real^2`; `h3':real^2->real^2`] THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "h1p" (MP_TAC o SPECL [`(f:real^2->real^2) x`; `(f:real^2->real^2) x`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h3:real^2->real^2) o ((h1:real^2->real^2) o (g:real^2->real^2))`;
                 `((g':real^2->real^2) o (h1':real^2->real^2)) o (h3':real^2->real^2)`]
    MOI_S5W_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN2 (LABEL_TAC "s1") (LABEL_TAC "s2"))) THENL
   [DISJ1_TAC THEN USE_THEN "canc" MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      USE_THEN "gp" (MP_TAC o SPECL [`x:real^2`; `x:real^2`]) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_S5W_SPLIT THEN
      EXISTS_TAC `((g':real^2->real^2) o (h1':real^2->real^2)) o (h3':real^2->real^2)` THEN
      ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN USE_THEN "canc" MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `vector[(x:real^2)$2; x$1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
        REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "gp" (MP_TAC o SPECL [`vector[(x:real^2)$2; x$1]:real^2`;
                                    `vector[(x:real^2)$2; x$1]:real^2`]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S5W_EXT_EQ THEN
    EXISTS_TAC `((h3:real^2->real^2) o ((h1:real^2->real^2) o (g:real^2->real^2))) o
                (\x:real^2. vector[x$2; x$1]:real^2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5W_SPLIT THEN
      EXISTS_TAC `(\x:real^2. vector[x$2; x$1]:real^2) o (((g':real^2->real^2) o (h1':real^2->real^2)) o
                          (h3':real^2->real^2))` THEN
      MP_TAC(MATCH_MP MOI_S5W_SYM_FACTS (CONJUNCT1 MOI_S5W_SYMS)) THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[o_THM; VECTOR_2];
        ASM_REWRITE_TAC[o_THM; VECTOR_2];
        X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
        SUBGOAL_THEN `vector[(x:real^2)$2; x$1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
         [UNDISCH_TAC `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
          REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `(vector[(x:real^2)$2; x$1]:real^2)$2 <
                      (vector[(x:real^2)$2; x$1]:real^2)$1` ASSUME_TAC THENL
         [REWRITE_TAC[VECTOR_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "s2" (MP_TAC o C MATCH_MP
          (CONJ (ASSUME `vector[(x:real^2)$2; x$1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                (ASSUME `(vector[(x:real^2)$2; x$1]:real^2)$2 <
                         (vector[(x:real^2)$2; x$1]:real^2)$1`))) THEN
        REWRITE_TAC[o_THM];
        X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
        SUBGOAL_THEN `vector[(x:real^2)$2; x$1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
         [UNDISCH_TAC `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
          REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `(vector[(x:real^2)$2; x$1]:real^2)$1 <
                      (vector[(x:real^2)$2; x$1]:real^2)$2` ASSUME_TAC THENL
         [REWRITE_TAC[VECTOR_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "s1" (MP_TAC o C MATCH_MP
          (CONJ (ASSUME `vector[(x:real^2)$2; x$1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)
                (ASSUME `(vector[(x:real^2)$2; x$1]:real^2)$1 <
                         (vector[(x:real^2)$2; x$1]:real^2)$2`))) THEN
        REWRITE_TAC[o_THM]];
      REWRITE_TAC[o_THM]]]);;

let MOI_S5W_DICHOTOMY = prove
 (MOI_S5W_DICHOTOMY_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `g':real^2->real^2`] MOI_S5W_DICHOTOMY_EXT) THEN
  ASM_REWRITE_TAC[moi_s5w_ext]);;

