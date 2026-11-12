(* ========================================================================= *)
(* pc_moi_fnd_surfa: foundations of the Moise PL core (Moise, Geometric     *)
(* Topology in Dimensions 2 and 3, GTM 47, Secs 21-22, pp.147-162).         *)
(* Main theorem (the statement term MOI_FND_SURFACE_SPHERE of               *)
(* pc_moi_fnd_stmt.ml):                                                      *)
(*   SURFACE_EULER_SPHERE: a finite connected nonempty combinatorial        *)
(*   2-manifold has Euler characteristic at most 2, with equality exactly   *)
(*   when its polyhedron is a PL 2-sphere.                                  *)
(* Route (shorter than the classification of 22.1-22.5, same ingredients;  *)
(* the numbers are those of the sections below):                            *)
(*   1   abstract counting: for a dual-connected finite set of triangles    *)
(*       (3-element vertex sets) in which every edge lies in at most two    *)
(*       triangles, V + F <= E + 2, and V + F <= E + 1 when some edge lies *)
(*       in exactly one triangle (a spanning tree of the dual graph, as in  *)
(*       22.1, and the cotree argument; parity of boundary degrees).        *)
(*   2   local and dual connectivity of subsets of a surface.               *)
(*   3   un-pinching one vertex (needed to exclude non-separating chords). *)
(*   4   PL disks with planar models and the gluing of two of them along  *)
(*       a boundary arc (as PL_BALL_2_UNION of pc_moi_pl2, in real^N).      *)
(*   5   good pieces of a surface and the four cases (A, B, C1, C2) of the  *)
(*       induction step (remove the triangle at a boundary edge).           *)
(*   6   recognition of the disk: a good piece (dual-connected, locally     *)
(*       connected, with boundary, V + F = E + 1) is a PL disk bounded      *)
(*       by its boundary edges (induction on the number of triangles).      *)
(*   7   the closed case: removing one triangle leaves a disk; two disks    *)
(*       with a common boundary curve form a PL 2-sphere (model: frontier   *)
(*       of a tetrahedron in real^(2,1)finite_sum).                         *)
(*   8   vertex links of a combinatorial 2-manifold are cycles (invariance  *)
(*       of domain, connectedness of punctured circles, chi = 0).           *)
(*   9   finite combinatorial 2-manifolds: vertex sets of simplices,        *)
(*       purity, every edge in exactly two triangles, local connectivity.   *)
(*   10  the abstract surface of a complex: counts, complex_euler as        *)
(*       V - E + F, dual connectivity from connectedness.                   *)
(*   11  the main theorem; in dimension at most 2 invariance of domain      *)
(*       excludes a 2-sphere, otherwise the sphere model is moved into      *)
(*       real^N.                                                            *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_star.ml";;
needs "src/pc_moi_smo_cf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Abstract 2-complexes: a set d of triangles (3-element vertex sets),   *)
(* its edges (2-element subsets of triangles), dual connectivity (through   *)
(* shared edges) and connectivity of a graph in partition form.             *)
(* ------------------------------------------------------------------------- *)

let moi_fsa_edges = new_definition
 `moi_fsa_edges (d:(A->bool)->bool) =
    {e:A->bool | e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t}`;;

let moi_fsa_dconn = new_definition
 `moi_fsa_dconn (d:(A->bool)->bool) <=>
    !X. X SUBSET d /\ ~(X = {}) /\
        (!t t' e. t IN X /\ t' IN d /\ e HAS_SIZE 2 /\
                  e SUBSET t /\ e SUBSET t' ==> t' IN X)
        ==> X = d`;;

let moi_fsa_gconn = new_definition
 `moi_fsa_gconn (w:A->bool) (l:(A->bool)->bool) <=>
    !a. a SUBSET w /\ ~(a = {}) /\ ~(a = w)
        ==> ?e x y. e IN l /\ x IN e /\ y IN e /\ x IN a /\ ~(y IN a)`;;

let MOI_FSA_EDGES_FINITE = prove
 (`!d:(A->bool)->bool.
        FINITE d /\ (!t. t IN d ==> FINITE t) ==> FINITE(moi_fsa_edges d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\t:A->bool. {e:A->bool | e SUBSET t}) d)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET];
    REWRITE_TAC[moi_fsa_edges; SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[]]);;

let MOI_FSA_CARD_EQ_1 = prove
 (`!s:A->bool. FINITE s /\ CARD s = 1 <=> ?a. s = {a}`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE; HAS_SIZE_1_EXISTS; EXISTS_UNIQUE_THM] THEN
    STRIP_TAC THEN EXISTS_TAC `x:A` THEN ASM SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[FINITE_SING; CARD_SING]]);;

let MOI_FSA_THREE = prove
 (`!s a b c:A.
        FINITE s /\ a IN s /\ b IN s /\ c IN s /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> 3 <= CARD s`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LE_TRANS `CARD {a:A,b,c}` THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
    MATCH_MP_TAC CARD_SUBSET THEN ASM SET_TAC[]]);;

let MOI_FSA_TWO = prove
 (`!s a b:A. FINITE s /\ a IN s /\ b IN s /\ ~(a = b) ==> 2 <= CARD s`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LE_TRANS `CARD {a:A,b}` THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
    MATCH_MP_TAC CARD_SUBSET THEN ASM SET_TAC[]]);;

let MOI_FSA_PAIR_SIZE = prove
 (`!x y:A. ~(x = y) ==> {x,y} HAS_SIZE 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let MOI_FSA_PAIR = prove
 (`!e x y:A. e HAS_SIZE 2 /\ x IN e /\ y IN e /\ ~(x = y) ==> e = {x,y}`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let MOI_FSA_DOUBLE_COUNT = prove
 (`!(R:A->B->bool) s t.
        FINITE s /\ FINITE t
        ==> nsum s (\x. CARD {y | y IN t /\ R x y}) =
            nsum t (\y. CARD {x | x IN s /\ R x y})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:A->B->bool`; `(\x:A y:B. 1)`; `s:A->bool`; `t:B->bool`]
    NSUM_NSUM_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT]);;

let MOI_FSA_EVEN_NSUM = prove
 (`!(f:A->num) s. FINITE s /\ (!x. x IN s ==> EVEN(f x)) ==> EVEN(nsum s f)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; EVEN; EVEN_ADD; FORALL_IN_INSERT]);;

(* Handshake in partition form: if x in a is the only vertex of a with odd *)
(* degree, some edge leaves a.                                              *)

let MOI_FSA_HANDSHAKE = prove
 (`!(f:(A->bool)->bool) a x.
        FINITE f /\ (!e. e IN f ==> e HAS_SIZE 2) /\ x IN a /\
        ~EVEN(CARD {e | e IN f /\ x IN e}) /\
        (!z. z IN a /\ ~(z = x) ==> EVEN(CARD {e | e IN f /\ z IN e}))
        ==> ?e y z. e IN f /\ y IN e /\ z IN e /\ y IN a /\ ~(z IN a)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!e:A->bool. e IN f ==> FINITE e` ASSUME_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  ABBREV_TAC `a0 = (a:A->bool) INTER UNIONS f` THEN
  SUBGOAL_THEN `FINITE(a0:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "a0" THEN MATCH_MP_TAC FINITE_INTER THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[FINITE_UNIONS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:A->bool. e IN f ==> EVEN(CARD {z | z IN a0 /\ z IN e})`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `?y:A. y IN e /\ y IN a` THENL
     [SUBGOAL_THEN `{z:A | z IN a0 /\ z IN e} = e` SUBST1_TAC THENL
       [EXPAND_TAC "a0" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER;
                                         IN_UNIONS] THEN
        ASM_MESON_TAC[];
        SUBGOAL_THEN `CARD(e:A->bool) = 2` SUBST1_TAC THENL
         [ASM_MESON_TAC[HAS_SIZE]; CONV_TAC NUM_REDUCE_CONV]];
      SUBGOAL_THEN `{z:A | z IN a0 /\ z IN e} = {}` SUBST1_TAC THENL
       [EXPAND_TAC "a0" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER;
                                         NOT_IN_EMPTY] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[CARD_CLAUSES; EVEN]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN a0` ASSUME_TAC THENL
   [EXPAND_TAC "a0" THEN REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~EVEN(CARD {e:A->bool | e IN f /\ x IN e})` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `{e:A->bool | e IN f /\ x IN e} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES; EVEN]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EVEN(nsum (a0:A->bool) (\z. CARD {e:A->bool | e IN f /\ z IN e}))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`\z:A e:A->bool. z IN e`; `a0:A->bool`;
                   `f:(A->bool)->bool`] MOI_FSA_DOUBLE_COUNT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:A. CARD {e:A->bool | e IN f /\ z IN e}`; `a0:A->bool`;
                 `x:A`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EVEN_ADD] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  EXPAND_TAC "a0" THEN SIMP_TAC[IN_INTER] THEN ASM_MESON_TAC[]);;

(* A connected graph (partition form) on w has at least CARD w - 1 edges.  *)

let MOI_FSA_GCONN_CARD = prove
 (`!(w:A->bool) l.
        FINITE w /\ ~(w = {}) /\
        (!e. e IN l ==> e HAS_SIZE 2 /\ e SUBSET w) /\ moi_fsa_gconn w l
        ==> CARD w <= CARD l + 1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conn")))) THEN
  SUBGOAL_THEN `FINITE(l:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{e:A->bool | e SUBSET w}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n < CARD(w:A->bool)
        ==> ?a m. a SUBSET w /\ CARD a = SUC n /\
                  m SUBSET (l:(A->bool)->bool) /\ CARD m = n /\
                  (!e. e IN m ==> e SUBSET a)`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(w:A->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `x0:A`) THEN
      MAP_EVERY EXISTS_TAC [`{x0:A}`; `{}:(A->bool)->bool`] THEN
      ASM_REWRITE_TAC[SING_SUBSET; CARD_SING; EMPTY_SUBSET; CARD_CLAUSES;
                      NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:A->bool` (X_CHOOSE_THEN `m:(A->bool)->bool`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `FINITE(a:A->bool) /\ FINITE(m:(A->bool)->bool)`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      USE_THEN "conn" (MP_TAC o SPEC `a:A->bool` o REWRITE_RULE[moi_fsa_gconn]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
         [UNDISCH_TAC `CARD(a:A->bool) = SUC n` THEN
          ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
          UNDISCH_TAC `SUC n < CARD(w:A->bool)` THEN
          UNDISCH_TAC `CARD(a:A->bool) = SUC n` THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:A->bool` (X_CHOOSE_THEN `x:A`
        (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`(y:A) INSERT a`; `(e:A->bool) INSERT m`] THEN
      SUBGOAL_THEN `~((e:A->bool) IN m)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(y:A) IN w /\ (e:A->bool) IN l /\ e HAS_SIZE 2`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_CLAUSES; INSERT_SUBSET; FORALL_IN_INSERT] THEN
      SUBGOAL_THEN `e = {x:A,y}` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC MOI_FSA_PAIR THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `CARD(w:A->bool) - 1`) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `~(CARD(w:A->bool) = 0)` MP_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0]; ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A->bool` (X_CHOOSE_THEN `m:(A->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `CARD(m:(A->bool)->bool) <= CARD(l:(A->bool)->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Boundary edges (edges in exactly one triangle) have even degree at      *)
(* every vertex when no edge lies in three triangles.                       *)

let MOI_FSA_EVEN_BDRY = prove
 (`!d:(A->bool)->bool z.
        FINITE d /\ (!t. t IN d ==> t HAS_SIZE 3) /\
        (!e. e IN moi_fsa_edges d ==> CARD {t | t IN d /\ e SUBSET t} <= 2)
        ==> EVEN(CARD {e | e IN moi_fsa_edges d /\
                           CARD {t | t IN d /\ e SUBSET t} = 1 /\ z IN e})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `dz = {t:A->bool | t IN d /\ z IN t}` THEN
  ABBREV_TAC `U = {u:A | ~(u = z) /\ ?t. t IN dz /\ u IN t}` THEN
  SUBGOAL_THEN `FINITE(dz:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "dz" THEN ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(U:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `UNIONS d:A->bool` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN ASM_MESON_TAC[HAS_SIZE];
      MAP_EVERY EXPAND_TAC ["U"; "dz"] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:A. u IN U
          ==> {t | t IN dz /\ u IN t} = {t | t IN d /\ {z,u} SUBSET t} /\
              {z,u} IN moi_fsa_edges d /\ ~(u = z)`
  (LABEL_TAC "U7") THENL
   [X_GEN_TAC `u:A` THEN MAP_EVERY EXPAND_TAC ["U"; "dz"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; INSERT_SUBSET;
                    EMPTY_SUBSET] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[HAS_SIZE] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:A. u IN U ==> 1 <= CARD {t:A->bool | t IN dz /\ u IN t} /\
                     CARD {t:A->bool | t IN dz /\ u IN t} <= 2`
  (LABEL_TAC "U8") THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    USE_THEN "U7" (MP_TAC o SPEC `u:A`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT] THEN
    UNDISCH_TAC `(u:A) IN U` THEN MAP_EVERY EXPAND_TAC ["U"; "dz"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    DISCH_THEN(MP_TAC o SYM) THEN
    MAP_EVERY EXPAND_TAC ["dz"] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EVEN(nsum U (\u:A. CARD {t:A->bool | t IN dz /\ u IN t}))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\u:A t:A->bool. u IN t`; `U:A->bool`;
                   `dz:(A->bool)->bool`] MOI_FSA_DOUBLE_COUNT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{u:A | u IN U /\ u IN t} = t DELETE z` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["U"] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t:A->bool) HAS_SIZE 3 /\ (z:A) IN t` MP_TAC THENL
     [UNDISCH_TAC `(t:A->bool) IN dz` THEN EXPAND_TAC "dz" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CARD_DELETE] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{e | e IN moi_fsa_edges d /\ CARD {t | t IN d /\ e SUBSET t} = 1 /\
         (z:A) IN e} =
    IMAGE (\u. {z,u})
          {u | u IN U /\ CARD {t:A->bool | t IN dz /\ u IN t} = 1}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `e:A->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` ASSUME_TAC THENL
       [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges d` THEN
        SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`e:A->bool`; `z:A`] MOI_SCF_OTHER) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(u:A) IN U` ASSUME_TAC THENL
       [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges d` THEN
        REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
        MAP_EVERY EXPAND_TAC ["U"; "dz"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:A->bool` THEN ASM SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "U7" (MP_TAC o SPEC `u:A`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `CARD {t:A->bool | t IN d /\ e SUBSET t} = 1` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:A`
        (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      USE_THEN "U7" (MP_TAC o SPEC `u:A`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
      UNDISCH_TAC `CARD {t:A->bool | t IN dz /\ u IN t} = 1` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(u:A = z) /\ ~(v:A = z)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `{z:A,u} = {z,v}` THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `EVEN(nsum U (\u:A. CARD {t:A->bool | t IN dz /\ u IN t}))` THEN
  SUBGOAL_THEN
   `nsum U (\u:A. CARD {t:A->bool | t IN dz /\ u IN t}) =
    nsum U (\u. if CARD {t:A->bool | t IN dz /\ u IN t} = 1 then 1 else 0) +
    nsum U (\u. if CARD {t:A->bool | t IN dz /\ u IN t} = 1 then 0
                else CARD {t:A->bool | t IN dz /\ u IN t})`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM NSUM_ADD] THEN MATCH_MP_TAC NSUM_EQ THEN
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[GSYM CARD_EQ_NSUM; FINITE_RESTRICT] THEN
  REWRITE_TAC[EVEN_ADD] THEN
  MATCH_MP_TAC(TAUT `q ==> (p <=> q) ==> p`) THEN
  MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:A` THEN DISCH_TAC THEN BETA_TAC THEN
  USE_THEN "U7" (MP_TAC o SPEC `u:A`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "U8" (MP_TAC o SPEC `u:A`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  SPEC_TAC(`CARD {t:A->bool | t IN d /\ {z,u} SUBSET t}`,`k:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[EVEN] THEN
  SUBGOAL_THEN `k = 2` SUBST1_TAC THENL
   [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]);;

(* A spanning tree of the dual graph: CARD d - 1 edges, each in exactly two *)
(* triangles, such that every nonempty set of them has a leaf triangle.     *)

let MOI_FSA_TREE = prove
 (`!d:(A->bool)->bool.
        FINITE d /\ ~(d = {}) /\
        (!e. e IN moi_fsa_edges d ==> CARD {t | t IN d /\ e SUBSET t} <= 2) /\
        moi_fsa_dconn d
        ==> ?tr. tr SUBSET moi_fsa_edges d /\ FINITE tr /\
                 CARD tr + 1 = CARD d /\
                 (!e. e IN tr ==> CARD {t | t IN d /\ e SUBSET t} = 2) /\
                 (!xx. xx SUBSET tr /\ ~(xx = {})
                       ==> ?t. t IN d /\ CARD {e | e IN xx /\ e SUBSET t} = 1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "le2") (LABEL_TAC "dconn")))) THEN
  SUBGOAL_THEN
   `!e t1 t2 t3:A->bool.
        e IN moi_fsa_edges d /\ t1 IN d /\ t2 IN d /\ t3 IN d /\
        e SUBSET t1 /\ e SUBSET t2 /\ e SUBSET t3 /\
        ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3) ==> F`
  (LABEL_TAC "no3") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "le2" (MP_TAC o SPEC `e:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `3 <= n ==> 2 < n`) THEN
    MATCH_MP_TAC MOI_FSA_THREE THEN
    MAP_EVERY EXISTS_TAC [`t1:A->bool`; `t2:A->bool`; `t3:A->bool`] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n < CARD(d:(A->bool)->bool)
        ==> ?D tr. D SUBSET d /\ CARD D = SUC n /\
                   tr SUBSET moi_fsa_edges d /\ FINITE tr /\ CARD tr = n /\
                   (!e. e IN tr ==> ?t t'. t IN D /\ t' IN D /\ ~(t = t') /\
                                           e SUBSET t /\ e SUBSET t') /\
                   (!xx. xx SUBSET tr /\ ~(xx = {})
                         ==> ?t. t IN D /\ CARD {e | e IN xx /\ e SUBSET t} = 1)`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(d:(A->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t0:A->bool`) THEN
      MAP_EVERY EXISTS_TAC [`{t0:A->bool}`; `{}:(A->bool)->bool`] THEN
      ASM_REWRITE_TAC[SING_SUBSET; CARD_SING; EMPTY_SUBSET; CARD_CLAUSES;
                      NOT_IN_EMPTY; FINITE_EMPTY; ONE] THEN
      REWRITE_TAC[SUBSET_EMPTY] THEN MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(A->bool)->bool` (X_CHOOSE_THEN
      `tr:(A->bool)->bool` (fun th ->
        let cs = CONJUNCTS th in
        MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
        LABEL_TAC "two" (last(butlast cs)) THEN
        LABEL_TAC "one" (last cs)))) THEN
    SUBGOAL_THEN `FINITE(D:(A->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?t t' e. t IN D /\ t' IN d /\ ~((t':A->bool) IN D) /\ e HAS_SIZE 2 /\
               e SUBSET t /\ (e:A->bool) SUBSET t'`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      USE_THEN "dconn"
        (MP_TAC o SPEC `D:(A->bool)->bool` o REWRITE_RULE[moi_fsa_dconn]) THEN
      ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `CARD(D:(A->bool)->bool) = SUC n` THEN
        ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
        ASM_MESON_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `SUC n < CARD(d:(A->bool)->bool)` THEN
        UNDISCH_TAC `CARD(D:(A->bool)->bool) = SUC n` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:A->bool) IN moi_fsa_edges d` ASSUME_TAC THENL
     [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!e':A->bool. e' IN tr /\ e' SUBSET t' ==> F`
    ASSUME_TAC THENL
     [X_GEN_TAC `e':A->bool` THEN STRIP_TAC THEN
      USE_THEN "two" (MP_TAC o SPEC `e':A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t1:A->bool` (X_CHOOSE_THEN `t2:A->bool`
        STRIP_ASSUME_TAC)) THEN
      USE_THEN "no3" (MATCH_MP_TAC o SPECL
        [`e':A->bool`; `t1:A->bool`; `t2:A->bool`; `t':A->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((e:A->bool) IN tr)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`(t':A->bool) INSERT D`; `(e:A->bool) INSERT tr`] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; INSERT_SUBSET; FINITE_INSERT] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_INSERT] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`t:A->bool`; `t':A->bool`] THEN
        ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
        X_GEN_TAC `e':A->bool` THEN DISCH_TAC THEN
        USE_THEN "two" (MP_TAC o SPEC `e':A->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `xx:(A->bool)->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(e:A->bool) IN xx` THENL
     [EXISTS_TAC `t':A->bool` THEN REWRITE_TAC[IN_INSERT] THEN
      SUBGOAL_THEN `{e':A->bool | e' IN xx /\ e' SUBSET t'} = {e}`
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
        X_GEN_TAC `e':A->bool` THEN EQ_TAC THENL
         [STRIP_TAC THEN ASM_CASES_TAC `e':A->bool = e` THEN
          ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check
            (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `F`)) (concl th))) THEN
          EXISTS_TAC `e':A->bool` THEN ASM SET_TAC[];
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[CARD_SING]];
      USE_THEN "one" (MP_TAC o SPEC `xx:(A->bool)->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t0:A->bool` THEN ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `CARD(d:(A->bool)->bool) - 1`) THEN
  SUBGOAL_THEN `~(CARD(d:(A->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(A->bool)->bool` (X_CHOOSE_THEN
    `tr:(A->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `D:(A->bool)->bool = d` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `tr:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= n /\ n <= 2 ==> n = 2`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e:A->bool` o check
      (fun th -> is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
                 is_exists(rand(snd(dest_forall(concl th)))))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:A->bool` (X_CHOOSE_THEN `t2:A->bool`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_FSA_TWO THEN
    MAP_EVERY EXISTS_TAC [`t1:A->bool`; `t2:A->bool`] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    USE_THEN "le2" MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* The edges outside the tree connect all vertices: a vertex partition     *)
(* crossed only by tree edges would give a nonempty set of tree edges with  *)
(* no leaf triangle, since a triangle has 0 or 2 crossing edges.            *)

let MOI_FSA_COTREE = prove
 (`!d:(A->bool)->bool tr.
        (!t. t IN d ==> t HAS_SIZE 3) /\ moi_fsa_dconn d /\
        tr SUBSET moi_fsa_edges d /\
        (!xx. xx SUBSET tr /\ ~(xx = {})
              ==> ?t. t IN d /\ CARD {e | e IN xx /\ e SUBSET t} = 1)
        ==> moi_fsa_gconn (UNIONS d) (moi_fsa_edges d DIFF tr)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h3") (CONJUNCTS_THEN2
    (LABEL_TAC "dconn") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "one")))) THEN
  REWRITE_TAC[moi_fsa_gconn] THEN X_GEN_TAC `a:A->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `xx = {e | e IN moi_fsa_edges (d:(A->bool)->bool) /\
                        ?y z. y IN e /\ z IN e /\ y IN a /\ ~((z:A) IN a)}` THEN
  SUBGOAL_THEN `(xx:(A->bool)->bool) SUBSET tr` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `e:A->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check
      (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
    REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`e:A->bool`; `y:A`; `z:A`] THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(xx:(A->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `!t:A->bool. t IN d /\ (?y. y IN t /\ y IN a) ==> t SUBSET a`
    (LABEL_TAC "all") THENL
     [X_GEN_TAC `t:A->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `y:A`)) THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      ASM_CASES_TAC `z:A = y` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `{y:A,z} IN xx` MP_TAC THENL
       [EXPAND_TAC "xx" THEN REWRITE_TAC[IN_ELIM_THM; moi_fsa_edges] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_MESON_TAC[];
          EXISTS_TAC `t:A->bool` THEN ASM SET_TAC[];
          MAP_EVERY EXISTS_TAC [`y:A`; `z:A`] THEN
          ASM_REWRITE_TAC[IN_INSERT]];
        ASM_REWRITE_TAC[NOT_IN_EMPTY]];
      ALL_TAC] THEN
    USE_THEN "dconn" (MP_TAC o
      SPEC `{t:A->bool | t IN d /\ ?y. y IN t /\ y IN a}` o
      REWRITE_RULE[moi_fsa_dconn]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [SET_TAC[];
        UNDISCH_TAC `~(a:A->bool = {})` THEN
        UNDISCH_TAC `(a:A->bool) SUBSET UNIONS d` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
        MESON_TAC[];
        MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `e:A->bool`] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(t:A->bool) SUBSET a` ASSUME_TAC THENL
         [USE_THEN "all" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `~(e:A->bool = {})` MP_TAC THENL
         [DISCH_TAC THEN UNDISCH_TAC `(e:A->bool) HAS_SIZE 2` THEN
          ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES] THEN ARITH_TAC;
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM SET_TAC[]]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(a:A->bool = UNIONS d)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:A->bool) IN {t | t IN d /\ ?y. y IN t /\ (y:A) IN a}`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:A->bool) SUBSET a` MP_TAC THENL
     [USE_THEN "all" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "one" (MP_TAC o SPEC `xx:(A->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:A->bool) HAS_SIZE 3` ASSUME_TAC THENL
   [USE_THEN "h3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {e:A->bool | e IN xx /\ e SUBSET t}` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{e:A->bool | e SUBSET t}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_POWERSET THEN ASM_MESON_TAC[HAS_SIZE];
      SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `CARD {e:A->bool | e IN xx /\ e SUBSET t} = 1` THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[MOI_FSA_CARD_EQ_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:A->bool` (LABEL_TAC "e0")) THEN
  SUBGOAL_THEN
   `!e:A->bool. e IN xx /\ e SUBSET t ==> e = e0`
  (LABEL_TAC "uniq") THENL
   [REMOVE_THEN "e0" (MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e0:A->bool) IN xx /\ e0 SUBSET t` MP_TAC THENL
   [REMOVE_THEN "e0" (MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "xx" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)))
    ASSUME_TAC) THEN
  SUBGOAL_THEN `~(y:A = z)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e0:A->bool) = {y,z}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_PAIR THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e0:A->bool) IN moi_fsa_edges d` THEN
    SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:A->bool`; `y:A`; `z:A`] MOI_SCF_THIRD) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!p q:A. p IN t /\ q IN t /\ ~(p = q) /\ p IN a /\ ~(q IN a)
            ==> {p,q} = e0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "uniq" MATCH_MP_TAC THEN
    EXPAND_TAC "xx" THEN REWRITE_TAC[IN_ELIM_THM; moi_fsa_edges] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t:A->bool` THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`p:A`; `q:A`] THEN ASM_REWRITE_TAC[IN_INSERT];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(u:A) IN a` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:A`; `z:A`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `u:A`])] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[]);;

(* The counting theorem.                                                     *)

let MOI_FSA_COUNT = prove
 (`!d:(A->bool)->bool.
        FINITE d /\ ~(d = {}) /\ (!t. t IN d ==> t HAS_SIZE 3) /\
        (!e. e IN moi_fsa_edges d ==> CARD {t | t IN d /\ e SUBSET t} <= 2) /\
        moi_fsa_dconn d
        ==> CARD(UNIONS d) + CARD d <= CARD(moi_fsa_edges d) + 2 /\
            ((?e. e IN moi_fsa_edges d /\ CARD {t | t IN d /\ e SUBSET t} = 1)
             ==> CARD(UNIONS d) + CARD d <= CARD(moi_fsa_edges d) + 1)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `d:(A->bool)->bool` MOI_FSA_TREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tr:(A->bool)->bool` (fun th ->
    let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
    LABEL_TAC "tr2" (last(butlast cs)) THEN
    LABEL_TAC "one" (last cs))) THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `tr:(A->bool)->bool`] MOI_FSA_COTREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `FINITE(moi_fsa_edges(d:(A->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN ASM_MESON_TAC[HAS_SIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(UNIONS d:A->bool) /\ ~(UNIONS d:A->bool = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN ASM_MESON_TAC[HAS_SIZE];
      UNDISCH_TAC `~(d:(A->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t0:A->bool`) THEN
      SUBGOAL_THEN `~(t0:A->bool = {})` MP_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `(t0:A->bool) HAS_SIZE 3` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES] THEN
          ARITH_TAC];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:A->bool. e IN moi_fsa_edges d DIFF tr ==> e HAS_SIZE 2 /\ e SUBSET UNIONS d`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF; moi_fsa_edges; IN_ELIM_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(moi_fsa_edges d DIFF tr) + CARD(tr:(A->bool)->bool) =
    CARD(moi_fsa_edges(d:(A->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DIFF] THEN
    SUBGOAL_THEN
     `CARD(tr:(A->bool)->bool) <= CARD(moi_fsa_edges(d:(A->bool)->bool))`
    MP_TAC THENL [ASM_SIMP_TAC[CARD_SUBSET]; ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`UNIONS d:A->bool`; `moi_fsa_edges d DIFF tr:(A->bool)->bool`]
      MOI_FSA_GCONN_CARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e0:A->bool) IN moi_fsa_edges d DIFF tr` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
    USE_THEN "tr2" (MP_TAC o SPEC `e0:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `bd = {e | e IN moi_fsa_edges d /\
              CARD {t | t IN d /\ e SUBSET t} = 1}:(A->bool)->bool` THEN
  SUBGOAL_THEN `!z:A. EVEN(CARD {e | e IN bd /\ z IN e})` (LABEL_TAC "evb") THENL
   [X_GEN_TAC `z:A` THEN
    MP_TAC(ISPECL [`d:(A->bool)->bool`; `z:A`] MOI_FSA_EVEN_BDRY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "bd" THEN REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(bd:(A->bool)->bool) /\ (e0:A->bool) IN bd /\
                (!e:A->bool. e IN bd ==> e HAS_SIZE 2 /\ ~(e IN tr))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bd" THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    X_GEN_TAC `e:A->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges d` THEN
      SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
      DISCH_TAC THEN USE_THEN "tr2" (MP_TAC o SPEC `e:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_gconn (UNIONS d) ((moi_fsa_edges d DIFF tr) DELETE (e0:A->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_gconn] THEN X_GEN_TAC `a:A->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `moi_fsa_gconn (UNIONS d) (moi_fsa_edges d DIFF tr:(A->bool)->bool)` THEN
    REWRITE_TAC[moi_fsa_gconn] THEN DISCH_THEN(MP_TAC o SPEC `a:A->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:A->bool` (X_CHOOSE_THEN `x:A`
      (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC))) THEN
    ASM_CASES_TAC `e:A->bool = e0` THENL
     [ALL_TAC;
      MAP_EVERY EXISTS_TAC [`e:A->bool`; `x:A`; `y:A`] THEN
      ASM_REWRITE_TAC[IN_DELETE]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(e0:A->bool) = {x,y}` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(bd:(A->bool)->bool) DELETE {x,y}`; `a:A->bool`; `x:A`]
      MOI_FSA_HANDSHAKE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `{e:A->bool | (e IN bd /\ ~(e = {x,y})) /\ x IN e} =
          {e | e IN bd /\ x IN e} DELETE {x,y}`
        SUBST1_TAC THENL
         [GEN_REWRITE_TAC I [EXTENSION] THEN
          REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `FINITE {e:A->bool | e IN bd /\ x IN e}` ASSUME_TAC THENL
         [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
        SUBGOAL_THEN `{x:A,y} IN {e | e IN bd /\ x IN e}` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT]; ALL_TAC] THEN
        ASM_SIMP_TAC[CARD_DELETE] THEN
        SUBGOAL_THEN `~(CARD {e:A->bool | e IN bd /\ x IN e} = 0)` MP_TAC THENL
         [ASM_SIMP_TAC[CARD_EQ_0] THEN
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        USE_THEN "evb" (MP_TAC o SPEC `x:A`) THEN
        SPEC_TAC(`CARD {e:A->bool | e IN bd /\ x IN e}`,`k:num`) THEN
        INDUCT_TAC THEN REWRITE_TAC[EVEN; SUC_SUB1; NOT_SUC];
        X_GEN_TAC `z:A` THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `{e:A->bool | (e IN bd /\ ~(e = {x,y})) /\ z IN e} =
          {e | e IN bd /\ z IN e}`
        SUBST1_TAC THENL
         [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
          X_GEN_TAC `ee:A->bool` THEN
          ASM_CASES_TAC `ee = {x:A,y}` THEN
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
          USE_THEN "evb" (MP_TAC o SPEC `z:A`) THEN REWRITE_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ee:A->bool` (X_CHOOSE_THEN `p:A`
      (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`ee:A->bool`; `p:A`; `q:A`] THEN
    UNDISCH_TAC `(ee:A->bool) IN bd DELETE {x,y}` THEN
    REWRITE_TAC[IN_DELETE; IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(ee:A->bool) IN bd` THEN EXPAND_TAC "bd" THEN
      SIMP_TAC[IN_ELIM_THM];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS d:A->bool`;
                 `(moi_fsa_edges d DIFF tr) DELETE (e0:A->bool)`]
    MOI_FSA_GCONN_CARD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(moi_fsa_edges d DIFF tr:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_DIFF]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE] THEN
  SUBGOAL_THEN `~(CARD(moi_fsa_edges d DIFF tr:(A->bool)->bool) = 0)` MP_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. Local connectivity at a vertex (through edges at the vertex), closed   *)
(* sets and components for dual and local adjacency, and abstract closed    *)
(* surfaces: every edge in exactly two triangles, connected vertex stars.   *)
(* ------------------------------------------------------------------------- *)

let moi_fsa_lclosed = new_definition
 `moi_fsa_lclosed (s:(A->bool)->bool) (x:A) (y:(A->bool)->bool) <=>
    !t t' u. t IN y /\ t' IN s /\ x IN t' /\ ~(u = x) /\ u IN t /\ u IN t'
             ==> t' IN y`;;

let moi_fsa_lconn = new_definition
 `moi_fsa_lconn (s:(A->bool)->bool) (x:A) <=>
    !y. y SUBSET {t | t IN s /\ x IN t} /\ ~(y = {}) /\ moi_fsa_lclosed s x y
        ==> y = {t | t IN s /\ x IN t}`;;

let moi_fsa_dclosed = new_definition
 `moi_fsa_dclosed (s:(A->bool)->bool) (y:(A->bool)->bool) <=>
    !t t' e. t IN y /\ t' IN s /\ e HAS_SIZE 2 /\ e SUBSET t /\ e SUBSET t'
             ==> t' IN y`;;

let moi_fsa_dcomp = new_definition
 `moi_fsa_dcomp (s:(A->bool)->bool) (t0:A->bool) =
    {t | t IN s /\
         !y. y SUBSET s /\ t0 IN y /\ moi_fsa_dclosed s y ==> t IN y}`;;

let moi_fsa_lcomp = new_definition
 `moi_fsa_lcomp (s:(A->bool)->bool) (x:A) (t0:A->bool) =
    {t | t IN s /\ x IN t /\
         !y. y SUBSET {t | t IN s /\ x IN t} /\ t0 IN y /\
             moi_fsa_lclosed s x y ==> t IN y}`;;

let moi_fsa_surf = new_definition
 `moi_fsa_surf (d:(A->bool)->bool) <=>
    FINITE d /\ (!t. t IN d ==> t HAS_SIZE 3) /\
    (!e. e IN moi_fsa_edges d ==> CARD {t | t IN d /\ e SUBSET t} = 2) /\
    (!x. moi_fsa_lconn d x)`;;

let MOI_FSA_DCONN_ALT = prove
 (`!s:(A->bool)->bool.
        moi_fsa_dconn s <=>
        !y. y SUBSET s /\ ~(y = {}) /\ moi_fsa_dclosed s y ==> y = s`,
  REWRITE_TAC[moi_fsa_dconn; moi_fsa_dclosed]);;

(* Complements of closed sets are closed (adjacency is symmetric).          *)

let MOI_FSA_DCLOSED_DIFF = prove
 (`!s y:(A->bool)->bool.
        moi_fsa_dclosed s y ==> moi_fsa_dclosed s (s DIFF y)`,
  REWRITE_TAC[moi_fsa_dclosed; IN_DIFF] THEN MESON_TAC[]);;

let MOI_FSA_LCLOSED_DIFF = prove
 (`!s (x:A) y.
        moi_fsa_lclosed s x y
        ==> moi_fsa_lclosed s x ({t | t IN s /\ x IN t} DIFF y)`,
  REWRITE_TAC[moi_fsa_lclosed; IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FSA_DCOMP = prove
 (`!s t0:A->bool.
        t0 IN s
        ==> moi_fsa_dcomp s t0 SUBSET s /\ t0 IN moi_fsa_dcomp s t0 /\
            moi_fsa_dclosed s (moi_fsa_dcomp s t0) /\
            (!y. y SUBSET s /\ t0 IN y /\ moi_fsa_dclosed s y
                 ==> moi_fsa_dcomp s t0 SUBSET y)`,
  REPEAT STRIP_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[moi_fsa_dcomp; IN_ELIM_THM] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[moi_fsa_dcomp; IN_ELIM_THM] THEN MESON_TAC[];
    GEN_REWRITE_TAC I [moi_fsa_dclosed] THEN
    REWRITE_TAC[moi_fsa_dcomp; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `e:A->bool`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:(A->bool)->bool` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(t:A->bool) IN y` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_fsa_dclosed s (y:(A->bool)->bool)` THEN
    REWRITE_TAC[moi_fsa_dclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:A->bool`; `e:A->bool`] THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[moi_fsa_dcomp; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

let MOI_FSA_DCOMP_DCONN = prove
 (`!s t0:A->bool. t0 IN s ==> moi_fsa_dconn (moi_fsa_dcomp s t0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSA_DCOMP) THEN
  ABBREV_TAC `c = moi_fsa_dcomp s (t0:A->bool)` THEN
  REWRITE_TAC[MOI_FSA_DCONN_ALT] THEN X_GEN_TAC `y:(A->bool)->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(t0:A->bool) IN y` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_fsa_dclosed s ((c:(A->bool)->bool) DIFF y)`
    ASSUME_TAC THENL
     [REWRITE_TAC[moi_fsa_dclosed; IN_DIFF] THEN
      MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `e:A->bool`] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_fsa_dclosed s (c:(A->bool)->bool)` THEN
        REWRITE_TAC[moi_fsa_dclosed] THEN ASM_MESON_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `moi_fsa_dclosed c (y:(A->bool)->bool)` THEN
        REWRITE_TAC[moi_fsa_dclosed] THEN
        DISCH_THEN(MP_TAC o SPECL [`t':A->bool`; `t:A->bool`; `e:A->bool`]) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:(A->bool)->bool) SUBSET c DIFF y` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_dclosed] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `e:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(t':A->bool) IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_dclosed s (c:(A->bool)->bool)` THEN
    REWRITE_TAC[moi_fsa_dclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:A->bool`; `e:A->bool`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_fsa_dclosed c (y:(A->bool)->bool)` THEN
  REWRITE_TAC[moi_fsa_dclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:A->bool`; `e:A->bool`] THEN ASM_REWRITE_TAC[]);;

let MOI_FSA_LCOMP = prove
 (`!s (x:A) t0.
        t0 IN s /\ x IN t0
        ==> moi_fsa_lcomp s x t0 SUBSET {t | t IN s /\ x IN t} /\
            t0 IN moi_fsa_lcomp s x t0 /\
            moi_fsa_lclosed s x (moi_fsa_lcomp s x t0) /\
            (!y. y SUBSET {t | t IN s /\ x IN t} /\ t0 IN y /\
                 moi_fsa_lclosed s x y
                 ==> moi_fsa_lcomp s x t0 SUBSET y)`,
  REPEAT STRIP_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[moi_fsa_lcomp; IN_ELIM_THM] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[moi_fsa_lcomp; IN_ELIM_THM] THEN MESON_TAC[];
    GEN_REWRITE_TAC I [moi_fsa_lclosed] THEN
    REWRITE_TAC[moi_fsa_lcomp; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `u:A`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:(A->bool)->bool` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(t:A->bool) IN y` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_fsa_lclosed s (x:A) y` THEN
    REWRITE_TAC[moi_fsa_lclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:A->bool`; `u:A`] THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[moi_fsa_lcomp; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

(* lconn only depends on the triangles at the vertex.                       *)

let MOI_FSA_LCONN_LOCAL = prove
 (`!s s' (x:A).
        {t | t IN s /\ x IN t} = {t | t IN s' /\ x IN t}
        ==> (moi_fsa_lconn s x <=> moi_fsa_lconn s' x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t':A->bool. t' IN s /\ x IN t' <=> t' IN s' /\ x IN t'`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. moi_fsa_lclosed s x y <=> moi_fsa_lclosed s' (x:A) y`
  (fun th -> REWRITE_TAC[moi_fsa_lconn; th]) THENL
   [REWRITE_TAC[moi_fsa_lclosed] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_FSA_LCOMP_LCONN = prove
 (`!s (x:A) t0.
        t0 IN s /\ x IN t0 ==> moi_fsa_lconn (moi_fsa_lcomp s x t0) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSA_LCOMP o
    CONJ (ASSUME `(t0:A->bool) IN s`)) THEN
  ABBREV_TAC `c = moi_fsa_lcomp s (x:A) t0` THEN
  SUBGOAL_THEN `{t | t IN c /\ (x:A) IN t} = c` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_lconn] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:(A->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t0:A->bool) IN y` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:(A->bool)->bool) SUBSET c DIFF y` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[moi_fsa_lclosed; IN_DIFF; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[moi_fsa_lclosed; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Edges of a subset of a surface; the second triangle at an edge.          *)

let MOI_FSA_EDGES_MONO = prove
 (`!s d:(A->bool)->bool.
        s SUBSET d ==> moi_fsa_edges s SUBSET moi_fsa_edges d`,
  REWRITE_TAC[moi_fsa_edges; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FSA_SURF_SUB_NTRI = prove
 (`!d s e:A->bool.
        moi_fsa_surf d /\ s SUBSET d /\ e IN moi_fsa_edges s
        ==> e IN moi_fsa_edges d /\ FINITE {t | t IN s /\ e SUBSET t} /\
            1 <= CARD {t | t IN s /\ e SUBSET t} /\
            CARD {t | t IN s /\ e SUBSET t} <= 2`,
  REWRITE_TAC[moi_fsa_surf] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:A->bool) IN moi_fsa_edges d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_EDGES_MONO; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT] THEN
    UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s` THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[];
    SUBGOAL_THEN `CARD {t:A->bool | t IN d /\ e SUBSET t} = 2` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[]]);;

let MOI_FSA_OTHER_TRI = prove
 (`!d (t:A->bool) e.
        moi_fsa_surf d /\ t IN d /\ e HAS_SIZE 2 /\ e SUBSET t
        ==> ?t'. t' IN d /\ ~(t' = t) /\ e SUBSET t' /\
                 {tt | tt IN d /\ e SUBSET tt} = {t,t'}`,
  REWRITE_TAC[moi_fsa_surf] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{tt:A->bool | tt IN d /\ e SUBSET tt} HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A->bool` (X_CHOOSE_THEN `q:A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq")))) THEN
  SUBGOAL_THEN `!tt:A->bool. tt IN d /\ e SUBSET tt <=> tt = p \/ tt = q`
  (LABEL_TAC "mem") THENL
   [USE_THEN "eq" (MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:A->bool) IN d /\ e SUBSET p /\ (q:A->bool) IN d /\ e SUBSET q`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "mem" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `t:A->bool = p \/ t = q` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [USE_THEN "mem" (fun th -> ASM_MESON_TAC[th]);
    EXISTS_TAC `q:A->bool` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `p:A->bool` THEN ASM_REWRITE_TAC[INSERT_AC]]);;

(* Sum of link degrees at a vertex: each triangle at x has two other        *)
(* vertices.                                                                *)

let MOI_FSA_LINK_SUM = prove
 (`!(y:(A->bool)->bool) (x:A) U.
        FINITE y /\ FINITE U /\ ~(x IN U) /\
        (!t. t IN y ==> t HAS_SIZE 3 /\ x IN t /\ t SUBSET x INSERT U)
        ==> nsum U (\u. CARD {t | t IN y /\ u IN t}) = 2 * CARD y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u:A t:A->bool. u IN t`; `U:A->bool`; `y:(A->bool)->bool`]
    MOI_FSA_DOUBLE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS `nsum (y:(A->bool)->bool) (\t. 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `{u:A | u IN U /\ u IN t} = t DELETE x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((x:A) IN U)` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CARD_DELETE] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC]);;

let MOI_FSA_EVEN_NSUM_TWO = prove
 (`!(f:A->num) U p q.
        FINITE U /\ p IN U /\ q IN U /\ ~(p = q) /\
        (!u. u IN U /\ ~(u = p) /\ ~(u = q) ==> EVEN(f u)) /\
        EVEN(nsum U f)
        ==> (EVEN(f p) <=> EVEN(f q))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `EVEN(nsum U (f:A->num))` THEN
  MP_TAC(ISPECL [`f:A->num`; `U:A->bool`; `p:A`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`f:A->num`; `U DELETE (p:A)`; `q:A`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[FINITE_DELETE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `EVEN(nsum ((U DELETE (p:A)) DELETE q) f)` MP_TAC THENL
   [MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    REWRITE_TAC[EVEN_ADD] THEN CONV_TAC TAUT]);;

(* Removing one triangle from a vertex star of a closed surface leaves it   *)
(* locally connected (a cycle minus an edge is connected; parity).          *)

let MOI_FSA_CYC_ADJ = prove
 (`!d (t:A->bool) x p q tp tq w.
        moi_fsa_surf d /\ t IN d /\ t = {x,p,q} /\
        ~(p = x) /\ ~(q = x) /\ ~(p = q) /\
        {tt | tt IN d /\ {x,p} SUBSET tt} = {t,tp} /\
        {tt | tt IN d /\ {x,q} SUBSET tt} = {t,tq} /\
        w SUBSET {tt | tt IN d DELETE t /\ x IN tt} /\ ~(w = {}) /\
        moi_fsa_lclosed (d DELETE t) x w
        ==> tp IN w \/ tq IN w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_surf]) THEN
  SUBGOAL_THEN
   `!tt:A->bool. tt IN d /\ {x,p} SUBSET tt <=> tt = t \/ tt = tp`
  (LABEL_TAC "mp") THENL
   [UNDISCH_TAC `{tt:A->bool | tt IN d /\ {x,p} SUBSET tt} = {t,tp}` THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tt:A->bool. tt IN d /\ {x,q} SUBSET tt <=> tt = t \/ tt = tq`
  (LABEL_TAC "mq") THENL
   [UNDISCH_TAC `{tt:A->bool | tt IN d /\ {x,q} SUBSET tt} = {t,tq}` THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~moi_fsa_lclosed d (x:A) w` MP_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `w = {tt:A->bool | tt IN d /\ x IN tt}` MP_TAC THENL
     [UNDISCH_TAC `!x:A. moi_fsa_lconn d x` THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN REWRITE_TAC[moi_fsa_lconn] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN d DELETE t /\ x IN tt}` THEN
      SET_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `\v:(A->bool)->bool. (t:A->bool) IN v`) THEN
      UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN d DELETE t /\ x IN tt}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_lclosed; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:A->bool` (X_CHOOSE_THEN `t2:A->bool`
    (X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `t2:A->bool = t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_fsa_lclosed (d DELETE t) (x:A) w` THEN
    REWRITE_TAC[moi_fsa_lclosed] THEN
    DISCH_THEN(MP_TAC o SPECL [`t1:A->bool`; `t2:A->bool`; `u:A`]) THEN
    ASM_REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t1:A->bool) IN d /\ x IN t1 /\ ~(t1 = t)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN d DELETE t /\ x IN tt}` THEN
    UNDISCH_TAC `(t1:A->bool) IN w` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(u:A) IN t` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `t1:A->bool = tp` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "mp" (MP_TAC o SPEC `t1:A->bool`) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN
    SUBGOAL_THEN `t1:A->bool = tq` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "mq" (MP_TAC o SPEC `t1:A->bool`) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[]]);;

let MOI_FSA_CYC_SING = prove
 (`!d (t:A->bool) x p tp w.
        {tt | tt IN d /\ {x,p} SUBSET tt} = {t,tp} /\
        w SUBSET {tt | tt IN d DELETE t /\ x IN tt}
        ==> (EVEN(CARD {tt | tt IN w /\ p IN tt}) <=> ~(tp IN w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{tt:A->bool | tt IN w /\ p IN tt} = (if tp IN w then {tp} else {})`
  SUBST1_TAC THENL
   [UNDISCH_TAC `{tt:A->bool | tt IN d /\ {x,p} SUBSET tt} = {t,tp}` THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; INSERT_SUBSET;
                EMPTY_SUBSET] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN d DELETE t /\ x IN tt}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[CARD_SING; CARD_CLAUSES; EVEN] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let MOI_FSA_CYC_PARITY = prove
 (`!d (t:A->bool) x p q w.
        moi_fsa_surf d /\ t IN d /\ t = {x,p,q} /\
        ~(p = x) /\ ~(q = x) /\ ~(p = q) /\
        w SUBSET {tt | tt IN d DELETE t /\ x IN tt} /\
        moi_fsa_lclosed (d DELETE t) x w
        ==> (EVEN(CARD {tt | tt IN w /\ p IN tt}) <=>
             EVEN(CARD {tt | tt IN w /\ q IN tt}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_surf]) THEN
  ABBREV_TAC `U = UNIONS d DELETE (x:A)` THEN
  SUBGOAL_THEN `FINITE(U:A->bool) /\ FINITE(w:(A->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[FINITE_DELETE; FINITE_UNIONS] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `d:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN d DELETE t /\ x IN tt}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tt:A->bool. tt IN w ==> tt IN d /\ x IN tt /\ ~(tt = t)`
  (LABEL_TAC "inw") THENL
   [UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN d DELETE t /\ x IN tt}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN U /\ (q:A) IN U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_DELETE; IN_UNIONS] THEN
    ASM_MESON_TAC[IN_INSERT];
    ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
    [`\u:A. CARD {tt:A->bool | tt IN w /\ u IN tt}`;
     `U:A->bool`; `p:A`; `q:A`] MOI_FSA_EVEN_NSUM_TWO)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:A` THEN STRIP_TAC THEN
    ASM_CASES_TAC `?tt:A->bool. tt IN w /\ v IN tt` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `t1:A->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(v:A = x)` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:A) IN U` THEN EXPAND_TAC "U" THEN
        REWRITE_TAC[IN_DELETE] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~((v:A) IN t)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
      SUBGOAL_THEN
       `{tt:A->bool | tt IN w /\ v IN tt} = {tt | tt IN d /\ {x,v} SUBSET tt}`
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN
        REWRITE_TAC[IN_ELIM_THM; INSERT_SUBSET; EMPTY_SUBSET] THEN
        X_GEN_TAC `t2:A->bool` THEN EQ_TAC THENL
         [ASM_MESON_TAC[];
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `moi_fsa_lclosed (d DELETE t) (x:A) w` THEN
          REWRITE_TAC[moi_fsa_lclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
          MAP_EVERY EXISTS_TAC [`t1:A->bool`; `v:A`] THEN
          ASM_REWRITE_TAC[IN_DELETE] THEN
          DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `CARD {tt:A->bool | tt IN d /\ {x,v} SUBSET tt} = 2`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_MESON_TAC[];
          EXISTS_TAC `t1:A->bool` THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_MESON_TAC[]];
        CONV_TAC NUM_REDUCE_CONV];
      SUBGOAL_THEN `{tt:A->bool | tt IN w /\ v IN tt} = {}` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES; EVEN]]];
    MP_TAC(ISPECL [`w:(A->bool)->bool`; `x:A`; `U:A->bool`]
      MOI_FSA_LINK_SUM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "U" THEN SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `t1:A->bool` THEN DISCH_TAC THEN
      USE_THEN "inw" (MP_TAC o SPEC `t1:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_DELETE; IN_UNIONS] THEN
      ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EVEN_MULT] THEN
      CONV_TAC NUM_REDUCE_CONV]]);;

let MOI_FSA_CYC_KEY = prove
 (`!d (t:A->bool) x p q tp tq w.
        moi_fsa_surf d /\ t IN d /\ t = {x,p,q} /\
        ~(p = x) /\ ~(q = x) /\ ~(p = q) /\
        {tt | tt IN d /\ {x,p} SUBSET tt} = {t,tp} /\
        {tt | tt IN d /\ {x,q} SUBSET tt} = {t,tq} /\
        w SUBSET {tt | tt IN d DELETE t /\ x IN tt} /\ ~(w = {}) /\
        moi_fsa_lclosed (d DELETE t) x w
        ==> tp IN w /\ tq IN w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `x:A`; `p:A`; `q:A`;
                 `tp:A->bool`; `tq:A->bool`; `w:(A->bool)->bool`]
    MOI_FSA_CYC_ADJ) THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `x:A`; `p:A`; `q:A`;
                 `w:(A->bool)->bool`] MOI_FSA_CYC_PARITY) THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `x:A`; `p:A`;
                 `tp:A->bool`; `w:(A->bool)->bool`] MOI_FSA_CYC_SING) THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `x:A`; `q:A`;
                 `tq:A->bool`; `w:(A->bool)->bool`] MOI_FSA_CYC_SING) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let MOI_FSA_CYC = prove
 (`!d (t:A->bool) x.
        moi_fsa_surf d /\ t IN d /\ x IN t ==> moi_fsa_lconn (d DELETE t) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:A->bool) HAS_SIZE 3` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fsa_surf]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:A->bool`; `x:A`] MOI_SCF_TWO_OTHERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `{x:A,p}`]
    MOI_FSA_OTHER_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_MESON_TAC[]; SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `tp:A->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `{x:A,q}`]
    MOI_FSA_OTHER_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_MESON_TAC[]; SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `tq:A->bool` STRIP_ASSUME_TAC)] THEN
  REWRITE_TAC[moi_fsa_lconn] THEN X_GEN_TAC `y:(A->bool)->bool` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `z = {tt | tt IN d DELETE t /\ (x:A) IN tt} DIFF y` THEN
  SUBGOAL_THEN `~(z:(A->bool)->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_lclosed (d DELETE t) (x:A) z` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC MOI_FSA_LCLOSED_DIFF THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tp:A->bool) IN y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `x:A`; `p:A`; `q:A`;
                   `tp:A->bool`; `tq:A->bool`; `y:(A->bool)->bool`]
      MOI_FSA_CYC_KEY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `z SUBSET {tt | tt IN d DELETE t /\ (x:A) IN tt}`
  ASSUME_TAC THENL [EXPAND_TAC "z" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(tp:A->bool) IN z` MP_TAC THENL
   [MP_TAC(ISPECL [`d:(A->bool)->bool`; `t:A->bool`; `x:A`; `p:A`; `q:A`;
                   `tp:A->bool`; `tq:A->bool`; `z:(A->bool)->bool`]
      MOI_FSA_CYC_KEY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    EXPAND_TAC "z" THEN ASM_REWRITE_TAC[IN_DIFF]]);;

(* Removing a triangle with a boundary edge at x keeps the star at x       *)
(* locally connected.                                                       *)

let MOI_FSA_LEAF = prove
 (`!s (t:A->bool) x p q.
        FINITE s /\ moi_fsa_lconn s x /\ t IN s /\ t = {x,p,q} /\
        ~(p = x) /\ ~(q = x) /\ ~(p = q) /\
        {tt | tt IN s /\ {x,p} SUBSET tt} = {t} /\
        CARD {tt | tt IN s /\ {x,q} SUBSET tt} <= 2
        ==> moi_fsa_lconn (s DELETE t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w SUBSET {tt | tt IN s DELETE t /\ (x:A) IN tt} /\ ~(w = {}) /\
        moi_fsa_lclosed (s DELETE t) x w
        ==> ?tw. tw IN w /\ {x,q} SUBSET tw`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `w:(A->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~moi_fsa_lclosed s (x:A) w` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `w = {tt:A->bool | tt IN s /\ x IN tt}` MP_TAC THENL
       [UNDISCH_TAC `moi_fsa_lconn s (x:A)` THEN REWRITE_TAC[moi_fsa_lconn] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN s DELETE t /\ x IN tt}` THEN
        SET_TAC[];
        DISCH_THEN(MP_TAC o AP_TERM `\v:(A->bool)->bool. (t:A->bool) IN v`) THEN
        UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN s DELETE t /\ x IN tt}` THEN
        UNDISCH_TAC `(t:A->bool) IN s` THEN
        SUBGOAL_THEN `(x:A) IN t` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fsa_lclosed; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:A->bool` (X_CHOOSE_THEN `t2:A->bool`
      (X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `t2:A->bool = t` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `moi_fsa_lclosed (s DELETE t) (x:A) w` THEN
      REWRITE_TAC[moi_fsa_lclosed] THEN
      DISCH_THEN(MP_TAC o SPECL [`t1:A->bool`; `t2:A->bool`; `u:A`]) THEN
      ASM_REWRITE_TAC[IN_DELETE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t1:A->bool) IN s /\ x IN t1 /\ ~(t1 = t)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `w SUBSET {tt:A->bool | tt IN s DELETE t /\ x IN tt}` THEN
      UNDISCH_TAC `(t1:A->bool) IN w` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `t1:A->bool` THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    UNDISCH_TAC `(u:A) IN t` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{tt:A->bool | tt IN s /\ {x,p} SUBSET tt} = {t}` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:(A->bool)->bool. (t1:A->bool) IN v`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING; INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_lconn] THEN X_GEN_TAC `y:(A->bool)->bool` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `z = {tt | tt IN s DELETE t /\ (x:A) IN tt} DIFF y` THEN
  SUBGOAL_THEN `z SUBSET {tt | tt IN s DELETE t /\ (x:A) IN tt} /\
                ~(z = {}) /\ moi_fsa_lclosed (s DELETE t) x z`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REPEAT CONJ_TAC THENL
     [SET_TAC[]; ASM SET_TAC[];
      MATCH_MP_TAC MOI_FSA_LCLOSED_DIFF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "key" (MP_TAC o SPEC `y:(A->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ty:A->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "key" (MP_TAC o SPEC `z:(A->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tz:A->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `CARD {tt:A->bool | tt IN s /\ {x,q} SUBSET tt} <= 2` THEN
  REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC(ARITH_RULE `3 <= n ==> 2 < n`) THEN
  MATCH_MP_TAC MOI_FSA_THREE THEN
  MAP_EVERY EXISTS_TAC [`t:A->bool`; `ty:A->bool`; `tz:A->bool`] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  SUBGOAL_THEN `(ty:A->bool) IN s DELETE t /\ (tz:A->bool) IN s DELETE t`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
    UNDISCH_TAC `(tz:A->bool) IN z` THEN EXPAND_TAC "z" THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[]]);;

(* At a triangle t = {w,a,b} whose edges at w are interior, every other     *)
(* triangle at w is locally connected to ta or tb: a closed set containing  *)
(* both is everything.                                                       *)

let MOI_FSA_SPLIT = prove
 (`!s (t:A->bool) w a b ta tb y.
        moi_fsa_lconn s w /\ t IN s /\ t = {w,a,b} /\
        {tt | tt IN s /\ {w,a} SUBSET tt} = {t,ta} /\
        {tt | tt IN s /\ {w,b} SUBSET tt} = {t,tb} /\
        y SUBSET {tt | tt IN s DELETE t /\ w IN tt} /\
        moi_fsa_lclosed (s DELETE t) w y /\ ta IN y /\ tb IN y
        ==> y = {tt | tt IN s DELETE t /\ w IN tt}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:A->bool) INSERT y = {tt | tt IN s /\ w IN tt}` MP_TAC THENL
   [UNDISCH_TAC `moi_fsa_lconn s (w:A)` THEN REWRITE_TAC[moi_fsa_lconn] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fsa_lclosed; IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `u:A`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_CASES_TAC `t2:A->bool = t` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(u:A) IN t` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
       [UNDISCH_TAC `{tt:A->bool | tt IN s /\ {w,a} SUBSET tt} = {t,ta}`;
        UNDISCH_TAC `{tt:A->bool | tt IN s /\ {w,b} SUBSET tt} = {t,tb}`] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\v:(A->bool)->bool. (t2:A->bool) IN v`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; INSERT_SUBSET;
                      EMPTY_SUBSET] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `t2:A->bool = t` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fsa_lclosed (s DELETE t) (w:A) y` THEN
      REWRITE_TAC[moi_fsa_lclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`t1:A->bool`; `u:A`] THEN
      ASM_REWRITE_TAC[IN_DELETE]];
    ALL_TAC] THEN
  UNDISCH_TAC `y SUBSET {tt | tt IN s DELETE t /\ (w:A) IN tt}` THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_INSERT; IN_ELIM_THM; IN_DELETE] THEN
  MESON_TAC[]);;

(* A locally connected vertex star has a connected link graph.              *)

let MOI_FSA_LCONN_GCONN = prove
 (`!s (w:A).
        moi_fsa_lconn s w
        ==> moi_fsa_gconn (UNIONS {tt | tt IN s /\ w IN tt} DELETE w)
                          (IMAGE (\tt. tt DELETE w) {tt | tt IN s /\ w IN tt})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_gconn] THEN
  X_GEN_TAC `a:A->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!tt x y:A. tt IN s /\ w IN tt /\ x IN tt /\ ~(x = w) /\ y IN tt /\
               ~(y = w) /\ x IN a ==> y IN a`
  (LABEL_TAC "nc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check
      (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `(tt:A->bool) DELETE w` THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `tt:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Z = {tt | tt IN s /\ (w:A) IN tt /\
                        ?x. x IN tt /\ ~(x = w) /\ x IN a}` THEN
  SUBGOAL_THEN `Z = {tt | tt IN s /\ (w:A) IN tt}` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_lconn s (w:A)` THEN REWRITE_TAC[moi_fsa_lconn] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Z" THEN SET_TAC[];
      UNDISCH_TAC `~(a:A->bool = {})` THEN
      UNDISCH_TAC `a SUBSET UNIONS {tt | tt IN s /\ (w:A) IN tt} DELETE w` THEN
      EXPAND_TAC "Z" THEN
      REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIONS; IN_ELIM_THM;
                  GSYM MEMBER_NOT_EMPTY] THEN
      MESON_TAC[];
      EXPAND_TAC "Z" THEN REWRITE_TAC[moi_fsa_lclosed; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `u:A`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:A` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "nc" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`t1:A->bool`; `x:A`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~(a = UNIONS {tt | tt IN s /\ (w:A) IN tt} DELETE w)` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIONS] THEN X_GEN_TAC `v:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t1:A->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  SUBGOAL_THEN `(t1:A->bool) IN Z` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t1 IN {tt | tt IN s /\ (w:A) IN tt}` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "nc" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1:A->bool`; `x:A`] THEN ASM_REWRITE_TAC[]);;

(* At a boundary vertex w, the two neighbours ta, tb of a triangle t whose  *)
(* edges at w are interior are not locally connected once t is removed:     *)
(* otherwise the star at w minus t is locally connected, and counting link  *)
(* degrees shows that every edge at w lies in two triangles.                *)

let MOI_FSA_NOTLOC_CONN = prove
 (`!s (t:A->bool) w a b ta tb.
        moi_fsa_lconn s w /\ t IN s /\ t = {w,a,b} /\
        {tt | tt IN s /\ {w,a} SUBSET tt} = {t,ta} /\ ~(ta = t) /\
        {tt | tt IN s /\ {w,b} SUBSET tt} = {t,tb} /\ ~(tb = t) /\
        tb IN moi_fsa_lcomp (s DELETE t) w ta
        ==> moi_fsa_lconn (s DELETE t) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl) o
    check (fun th -> is_eq(concl th) && is_setenum(rhs(concl th)) &&
                     length(dest_setenum(rhs(concl th))) = 3)) THEN
  SUBGOAL_THEN `(ta:A->bool) IN s /\ w IN ta` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{tt:A->bool | tt IN s /\ {w,a} SUBSET tt} = {{w,a,b},ta}` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:(A->bool)->bool. (ta:A->bool) IN v`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s DELETE {w:A,a,b}`; `w:A`; `ta:A->bool`] MOI_FSA_LCOMP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_fsa_lcomp (s DELETE {w,a,b}) w (ta:A->bool) =
    {tt | tt IN s DELETE {w,a,b} /\ w IN tt}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_SPLIT THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `b:A`; `ta:A->bool`; `tb:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s DELETE {w:A,a,b}`; `w:A`; `ta:A->bool`]
    MOI_FSA_LCOMP_LCONN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MOI_FSA_LCONN_LOCAL THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FSA_CARD_PAIR = prove
 (`!x y:A. ~(x = y) ==> CARD {x,y} = 2`,
  MESON_TAC[MOI_FSA_PAIR_SIZE; HAS_SIZE]);;

let MOI_FSA_NOTLOC_COUNT = prove
 (`!d s (t:A->bool) w a b ta tb u.
        moi_fsa_surf d /\ s SUBSET d /\ t IN s /\
        (!v. v IN t <=> v = w \/ v = a \/ v = b) /\
        ~(a = w) /\ ~(b = w) /\
        ta IN s /\ ~(ta = t) /\ w IN ta /\ a IN ta /\
        tb IN s /\ ~(tb = t) /\ w IN tb /\ b IN tb /\
        moi_fsa_lconn (s DELETE t) w /\
        ~(u = w) /\ {w,u} IN moi_fsa_edges s /\
        CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 1
        ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_surf]) THEN
  SUBGOAL_THEN `FINITE(s:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `Q = {tt | tt IN s DELETE t /\ (w:A) IN tt}` THEN
  ABBREV_TAC `U = UNIONS Q DELETE (w:A)` THEN
  SUBGOAL_THEN `!tt:A->bool. tt IN Q <=> tt IN s /\ ~(tt = t) /\ w IN tt`
  (LABEL_TAC "inq") THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tt:A->bool. tt IN s ==> tt HAS_SIZE 3` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Q:(A->bool)->bool) /\ FINITE(U:A->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:(A->bool)->bool` THEN
      ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[FINITE_DELETE; FINITE_UNIONS] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[HAS_SIZE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN U /\ (b:A) IN U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `ta:A->bool`; EXISTS_TAC `tb:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(U:A->bool) <= CARD(Q:(A->bool)->bool) + 1` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS
     `CARD(IMAGE (\tt. tt DELETE w) (Q:(A->bool)->bool)) + 1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_GCONN_CARD THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `t1:A->bool` THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `(t1:A->bool) HAS_SIZE 3 /\ w IN t1` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
        ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE] THEN
        CONV_TAC NUM_REDUCE_CONV THEN EXPAND_TAC "U" THEN
        UNDISCH_TAC `(t1:A->bool) IN Q` THEN SET_TAC[];
        MAP_EVERY EXPAND_TAC ["U"; "Q"] THEN
        MATCH_MP_TAC MOI_FSA_LCONN_GCONN THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(ARITH_RULE `a <= b ==> a + 1 <= b + 1`) THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `sw = {tt | tt IN s /\ (w:A) IN tt}` THEN
  SUBGOAL_THEN `sw = (t:A->bool) INSERT Q /\ ~(t IN Q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "sw" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      X_GEN_TAC `t1:A->bool` THEN REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
      USE_THEN "inq" (fun th -> REWRITE_TAC[th]) THEN
      ASM_CASES_TAC `t1:A->bool = t` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      USE_THEN "inq" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sw:(A->bool)->bool`; `w:A`; `U:A->bool`] MOI_FSA_LINK_SUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[IN_DELETE];
      UNDISCH_TAC `!tt:A->bool. tt IN s ==> tt HAS_SIZE 3` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_INSERT] THEN X_GEN_TAC `v:A` THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t1:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `!tt:A->bool. tt IN s ==> tt HAS_SIZE 3` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "U" THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_DELETE; IN_UNIONS] THEN
      X_GEN_TAC `v:A` THEN DISCH_TAC THEN
      ASM_CASES_TAC `v:A = w` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t1:A->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `CARD(sw:(A->bool)->bool) = CARD(Q:(A->bool)->bool) + 1`
  ASSUME_TAC THENL [ASM_SIMP_TAC[CARD_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check
    (fun th -> concl th = `sw = (t:A->bool) INSERT Q`)) THEN
  SUBGOAL_THEN
   `!v:A. v IN U ==> {tt | tt IN sw /\ v IN tt} =
                     {tt | tt IN s /\ {w,v} SUBSET tt} /\ ~(v = w)`
  (LABEL_TAC "eqv") THENL
   [X_GEN_TAC `v:A` THEN EXPAND_TAC "U" THEN REWRITE_TAC[IN_DELETE] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    EXPAND_TAC "sw" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; INSERT_SUBSET; EMPTY_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:A. v IN U ==> CARD {tt | tt IN sw /\ v IN tt} <= 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:A` THEN DISCH_TAC THEN
    USE_THEN "eqv" (MP_TAC o SPEC `v:A`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `{w:A,v}`]
      MOI_FSA_SURF_SUB_NTRI) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_MESON_TAC[];
      UNDISCH_TAC `(v:A) IN U` THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[IN_DELETE; IN_UNIONS; INSERT_SUBSET; EMPTY_SUBSET] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t1:A->bool`
        STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `t1:A->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inq" (MP_TAC o SPEC `t1:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:A) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `{w:A,u} IN moi_fsa_edges s` THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; INSERT_SUBSET; EMPTY_SUBSET] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:A->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `t1:A->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(u:A) IN t` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [UNDISCH_TAC `CARD {tt:A->bool | tt IN s /\ {w,a} SUBSET tt} = 1` THEN
      MATCH_MP_TAC(ARITH_RULE `2 <= n ==> n = 1 ==> F`) THEN
      MATCH_MP_TAC MOI_FSA_TWO THEN
      MAP_EVERY EXISTS_TAC [`t:A->bool`; `ta:A->bool`];
      UNDISCH_TAC `CARD {tt:A->bool | tt IN s /\ {w,b} SUBSET tt} = 1` THEN
      MATCH_MP_TAC(ARITH_RULE `2 <= n ==> n = 1 ==> F`) THEN
      MATCH_MP_TAC MOI_FSA_TWO THEN
      MAP_EVERY EXISTS_TAC [`t:A->bool`; `tb:A->bool`]] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {tt | tt IN sw /\ (u:A) IN tt} < 2` ASSUME_TAC THENL
   [USE_THEN "eqv" (MP_TAC o SPEC `u:A`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:A->bool`; `\u:A. CARD {t:A->bool | t IN sw /\ u IN t}`; `2`]
    NSUM_BOUND_LT) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN ASM_SIMP_TAC[] THEN EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* Removing a triangle keeps dual connectivity when its neighbours lie in  *)
(* one dual component of the rest.                                          *)

let MOI_FSA_DCONN_DEL_A = prove
 (`!s (t:A->bool) c y.
        moi_fsa_dconn s /\ t IN s /\
        (!n e. n IN s /\ ~(n = t) /\ e HAS_SIZE 2 /\ e SUBSET n /\
               e SUBSET t ==> n IN c) /\
        c SUBSET y /\ y SUBSET s DELETE t /\ moi_fsa_dclosed (s DELETE t) y
        ==> t INSERT y = s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dc") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "nb") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ycl")))))) THEN
  USE_THEN "dc" (MATCH_MP_TAC o REWRITE_RULE[MOI_FSA_DCONN_ALT]) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; INSERT_SUBSET] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `y SUBSET s DELETE (t:A->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_dclosed; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `e:A->bool`] THEN
  ASM_CASES_TAC `t2:A->bool = t` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `(t2:A->bool) IN c` MP_TAC THENL
     [USE_THEN "nb" MATCH_MP_TAC THEN
      EXISTS_TAC `e:A->bool` THEN
      UNDISCH_TAC `(e:A->bool) SUBSET t1` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(c:(A->bool)->bool) SUBSET y` THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
    USE_THEN "ycl" (MP_TAC o GEN_REWRITE_RULE I [moi_fsa_dclosed]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t1:A->bool`; `e:A->bool`] THEN
    ASM_REWRITE_TAC[IN_DELETE]]);;

let MOI_FSA_DCONN_DEL_B = prove
 (`!s (t:A->bool) c y.
        moi_fsa_dconn s /\ t IN s /\
        (!n e. n IN s /\ ~(n = t) /\ e HAS_SIZE 2 /\ e SUBSET n /\
               e SUBSET t ==> n IN c) /\
        c SUBSET (s DELETE t) DIFF y /\ y SUBSET s DELETE t /\ ~(y = {}) /\
        moi_fsa_dclosed (s DELETE t) y
        ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dc") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "nb") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (LABEL_TAC "ycl"))))))) THEN
  SUBGOAL_THEN `y:(A->bool)->bool = s` MP_TAC THENL
   [USE_THEN "dc" (MATCH_MP_TAC o REWRITE_RULE[MOI_FSA_DCONN_ALT]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `y SUBSET s DELETE (t:A->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fsa_dclosed] THEN
    MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `e:A->bool`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `t2:A->bool = t` THENL
     [SUBGOAL_THEN `(t1:A->bool) IN s /\ ~(t1 = t)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `y SUBSET s DELETE (t:A->bool)` THEN
        UNDISCH_TAC `(t1:A->bool) IN y` THEN
        REWRITE_TAC[SUBSET; IN_DELETE] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(t1:A->bool) IN c` MP_TAC THENL
       [USE_THEN "nb" MATCH_MP_TAC THEN
        EXISTS_TAC `e:A->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(e:A->bool) SUBSET t2` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(c:(A->bool)->bool) SUBSET (s DELETE t) DIFF y` THEN
        UNDISCH_TAC `(t1:A->bool) IN y` THEN
        REWRITE_TAC[SUBSET; IN_DIFF] THEN MESON_TAC[]];
      USE_THEN "ycl" (MP_TAC o GEN_REWRITE_RULE I [moi_fsa_dclosed]) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`t1:A->bool`; `e:A->bool`] THEN
      ASM_REWRITE_TAC[IN_DELETE]];
    DISCH_TAC THEN UNDISCH_TAC `y SUBSET s DELETE (t:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(t:A->bool) IN s` THEN
    REWRITE_TAC[SUBSET; IN_DELETE] THEN MESON_TAC[]]);;

let MOI_FSA_DCONN_DELETE = prove
 (`!s (t:A->bool) t0.
        moi_fsa_dconn s /\ t IN s /\ t0 IN s /\ ~(t0 = t) /\
        (!n e. n IN s /\ ~(n = t) /\ e HAS_SIZE 2 /\ e SUBSET n /\
               e SUBSET t
               ==> n IN moi_fsa_dcomp (s DELETE t) t0)
        ==> moi_fsa_dconn (s DELETE t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s DELETE (t:A->bool)`; `t0:A->bool`] MOI_FSA_DCOMP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  ABBREV_TAC `c = moi_fsa_dcomp (s DELETE t) (t0:A->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")))) THEN
  REWRITE_TAC[MOI_FSA_DCONN_ALT] THEN X_GEN_TAC `y:(A->bool)->bool` THEN
  STRIP_TAC THEN ASM_CASES_TAC `(t0:A->bool) IN y` THENL
   [MP_TAC(ISPECL [`s:(A->bool)->bool`; `t:A->bool`; `c:(A->bool)->bool`;
                   `y:(A->bool)->bool`] MOI_FSA_DCONN_DEL_A) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "min" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `y SUBSET s DELETE (t:A->bool)` THEN SET_TAC[]];
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC MOI_FSA_DCONN_DEL_B THEN
    MAP_EVERY EXISTS_TAC [`s:(A->bool)->bool`; `t:A->bool`;
                          `c:(A->bool)->bool`; `y:(A->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "min" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_DELETE] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FSA_DCLOSED_DIFF THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Un-pinching one vertex: give the triangles of a locally closed set y  *)
(* at w a fresh copy ws of w.  The relabelled complex has one more vertex,  *)
(* the same numbers of edges and triangles, and inherits dual connectivity, *)
(* so the counting theorem gives V + F <= E for a pinched piece.            *)
(* ------------------------------------------------------------------------- *)

let moi_fsa_relab = new_definition
 `moi_fsa_relab (y:(A->bool)->bool) (w:A) (ws:A) (t:A->bool) =
    if t IN y then ws INSERT (t DELETE w) else t`;;

let moi_fsa_relabe = new_definition
 `moi_fsa_relabe (y:(A->bool)->bool) (w:A) (ws:A) (e:A->bool) =
    if w IN e /\ (?t. t IN y /\ e SUBSET t) then ws INSERT (e DELETE w)
    else e`;;

let MOI_FSA_RELAB_INJ = prove
 (`!s y (w:A) ws t1 t2.
        y SUBSET s /\ (!t. t IN y ==> w IN t) /\ ~(ws IN UNIONS s) /\
        t1 IN s /\ t2 IN s /\
        moi_fsa_relab y w ws t1 = moi_fsa_relab y w ws t2
        ==> t1 = t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_relab] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((ws:A) IN t1) /\ ~(ws IN t2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_CASES_TAC `(t1:A->bool) IN y` THEN ASM_CASES_TAC `(t2:A->bool) IN y` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(w:A) IN t1 /\ w IN t2` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((ws:A) IN t1)` THEN UNDISCH_TAC `~((ws:A) IN t2)` THEN
    SET_TAC[];
    UNDISCH_TAC `~((ws:A) IN t2)` THEN SET_TAC[];
    UNDISCH_TAC `~((ws:A) IN t1)` THEN SET_TAC[]]);;

let MOI_FSA_RELAB_SIZE = prove
 (`!s y (w:A) ws t.
        y SUBSET s /\ (!t. t IN y ==> w IN t) /\ ~(ws IN UNIONS s) /\
        t IN s /\ t HAS_SIZE 3
        ==> moi_fsa_relab y w ws t HAS_SIZE 3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_relab] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((ws:A) IN t) /\ (w:A) IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  UNDISCH_TAC `(t:A->bool) HAS_SIZE 3` THEN REWRITE_TAC[HAS_SIZE] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; CARD_DELETE; IN_DELETE;
               FINITE_INSERT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The key equivalence: a relabelled edge lies in a relabelled triangle iff *)
(* the edge lies in the triangle.                                           *)

let MOI_FSA_RELAB_EDGE_IFF = prove
 (`!s y (w:A) ws e t.
        y SUBSET s /\ (!t. t IN y ==> w IN t) /\ moi_fsa_lclosed s w y /\
        ~(ws IN UNIONS s) /\
        e IN moi_fsa_edges s /\ t IN s
        ==> (moi_fsa_relabe y w ws e SUBSET moi_fsa_relab y w ws t <=>
             e SUBSET t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_relab; moi_fsa_relabe] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s` THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t0:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~((ws:A) IN t) /\ ~((ws:A) IN e)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS; SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `(w:A) IN e /\ (?t1:A->bool. t1 IN y /\ e SUBSET t1)` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t1:A->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`e:A->bool`; `w:A`] MOI_SCF_OTHER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(u:A = ws)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INSERT; IN_UNIONS; SUBSET]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(w:A) IN t` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(u:A = ws)` THEN UNDISCH_TAC `~(u:A = w)` THEN
      UNDISCH_TAC `(w:A) IN t` THEN SET_TAC[];
      ASM_REWRITE_TAC[INSERT_SUBSET] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((t:A->bool) IN y)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fsa_lclosed s (w:A) y` THEN
      REWRITE_TAC[moi_fsa_lclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`t1:A->bool`; `u:A`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((w:A) IN e)` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]]]);;

let MOI_FSA_RELABE_SIZE = prove
 (`!s y (w:A) ws e.
        ~(ws IN UNIONS s) /\ e IN moi_fsa_edges s
        ==> moi_fsa_relabe y w ws e HAS_SIZE 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_relabe; moi_fsa_edges; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t0:A->bool` STRIP_ASSUME_TAC))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((ws:A) IN e)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(e:A->bool) HAS_SIZE 2` THEN REWRITE_TAC[HAS_SIZE] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; CARD_DELETE; IN_DELETE;
               FINITE_INSERT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MOI_FSA_RELABE_INJ = prove
 (`!s y (w:A) ws e1 e2.
        ~(ws IN UNIONS s) /\ e1 IN moi_fsa_edges s /\ e2 IN moi_fsa_edges s /\
        moi_fsa_relabe y w ws e1 = moi_fsa_relabe y w ws e2
        ==> e1 = e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_relabe] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((ws:A) IN e1) /\ ~((ws:A) IN e2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(e1:A->bool) IN moi_fsa_edges s` THEN
    UNDISCH_TAC `(e2:A->bool) IN moi_fsa_edges s` THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IN_UNIONS; SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check
    (fun th -> is_conj(concl th) && not(is_eq(concl th))))) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]);;

let MOI_FSA_EDGES_RELAB_SUB = prove
 (`!s y (w:A) ws e2.
        y SUBSET s /\ (!t. t IN y ==> w IN t) /\ moi_fsa_lclosed s w y /\
        ~(ws IN UNIONS s) /\
        e2 IN moi_fsa_edges (IMAGE (moi_fsa_relab y w ws) s)
        ==> ?e. e2 = moi_fsa_relabe y w ws e /\ e IN moi_fsa_edges s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `~((ws:A) IN t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  ASM_CASES_TAC `(ws:A) IN e2` THENL
   [SUBGOAL_THEN `(t:A->bool) IN y` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `e2 SUBSET moi_fsa_relab y (w:A) ws t` THEN
      ASM_REWRITE_TAC[moi_fsa_relab] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:A) IN t /\ ~(w = ws)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`e2:A->bool`; `ws:A`] MOI_SCF_OTHER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:A) IN t /\ ~(u = w)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `e2 SUBSET moi_fsa_relab y (w:A) ws t` THEN
      ASM_REWRITE_TAC[moi_fsa_relab; INSERT_SUBSET; IN_INSERT; IN_DELETE] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `{w:A,u}` THEN REWRITE_TAC[moi_fsa_relabe; IN_INSERT] THEN
    COND_CASES_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(u:A = w)` THEN SET_TAC[];
        MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_MESON_TAC[];
        EXISTS_TAC `t:A->bool` THEN ASM SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `t:A->bool` o
        REWRITE_RULE[NOT_EXISTS_THM] o check (is_neg o concl)) THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e2:A->bool) SUBSET t` ASSUME_TAC THENL
   [UNDISCH_TAC `e2 SUBSET moi_fsa_relab y (w:A) ws t` THEN
    REWRITE_TAC[moi_fsa_relab] THEN COND_CASES_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `e2:A->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[moi_fsa_relabe] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t1:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(w:A = ws)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~((ws:A) IN UNIONS s)` THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `(t:A->bool) IN y` THENL
   [UNDISCH_TAC `e2 SUBSET moi_fsa_relab y (w:A) ws t` THEN
    ASM_REWRITE_TAC[moi_fsa_relab] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e2:A->bool`; `w:A`] MOI_SCF_OTHER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~((t:A->bool) IN y)` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  UNDISCH_TAC `moi_fsa_lclosed s (w:A) y` THEN
  REWRITE_TAC[moi_fsa_lclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1:A->bool`; `u:A`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FSA_EDGES_RELAB = prove
 (`!s y (w:A) ws.
        y SUBSET s /\ (!t. t IN y ==> w IN t) /\ moi_fsa_lclosed s w y /\
        ~(ws IN UNIONS s)
        ==> moi_fsa_edges (IMAGE (moi_fsa_relab y w ws) s) =
            IMAGE (moi_fsa_relabe y w ws) (moi_fsa_edges s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e2:A->bool` THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_FSA_EDGES_RELAB_SUB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:A->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?t:A->bool. t IN s /\ e SUBSET t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s` THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSA_RELABE_SIZE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `moi_fsa_relab y (w:A) ws t` THEN
  CONJ_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`; `ws:A`;
                 `e:A->bool`; `t:A->bool`] MOI_FSA_RELAB_EDGE_IFF) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FSA_UNIONS_RELAB = prove
 (`!s y (w:A) ws.
        y SUBSET s /\ ~(y = {}) /\ (!t. t IN y ==> w IN t) /\
        (?t. t IN s /\ w IN t /\ ~(t IN y))
        ==> UNIONS (IMAGE (moi_fsa_relab y w ws) s) = ws INSERT UNIONS s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_INSERT; moi_fsa_relab] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t1:A->bool` MP_TAC) THEN
    COND_CASES_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
    ASM_MESON_TAC[];
    STRIP_TAC THENL
     [UNDISCH_TAC `~(y:(A->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t1:A->bool`) THEN EXISTS_TAC `t1:A->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INSERT]];
      ASM_CASES_TAC `x:A = w` THENL
       [EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        EXISTS_TAC `t':A->bool` THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INSERT; IN_DELETE]]]]);;

let MOI_FSA_TRI_RELAB = prove
 (`!s y (w:A) ws e.
        y SUBSET s /\ (!t. t IN y ==> w IN t) /\ moi_fsa_lclosed s w y /\
        ~(ws IN UNIONS s) /\ e IN moi_fsa_edges s
        ==> {t | t IN IMAGE (moi_fsa_relab y w ws) s /\
                 moi_fsa_relabe y w ws e SUBSET t} =
            IMAGE (moi_fsa_relab y w ws) {t | t IN s /\ e SUBSET t}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t2:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`; `ws:A`;
                   `e:A->bool`; `t:A->bool`] MOI_FSA_RELAB_EDGE_IFF) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC
     `moi_fsa_relabe y (w:A) ws e SUBSET t2` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`; `ws:A`;
                   `e:A->bool`; `t:A->bool`] MOI_FSA_RELAB_EDGE_IFF) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FSA_DCONN_RELAB = prove
 (`!s y (w:A) ws.
        y SUBSET s /\ (!t. t IN y ==> w IN t) /\ moi_fsa_lclosed s w y /\
        ~(ws IN UNIONS s) /\ moi_fsa_dconn s
        ==> moi_fsa_dconn (IMAGE (moi_fsa_relab y w ws) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_FSA_DCONN_ALT] THEN X_GEN_TAC `x2:(A->bool)->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{t | t IN s /\ moi_fsa_relab y (w:A) ws t IN x2} = s` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_dconn (s:(A->bool)->bool)` THEN
    REWRITE_TAC[MOI_FSA_DCONN_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `~(x2:(A->bool)->bool = {})` THEN
      UNDISCH_TAC `x2 SUBSET IMAGE (moi_fsa_relab y (w:A) ws) s` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MESON_TAC[];
      REWRITE_TAC[moi_fsa_dclosed; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `e:A->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(e:A->bool) IN moi_fsa_edges s` ASSUME_TAC THENL
       [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `moi_fsa_dclosed (IMAGE (moi_fsa_relab y (w:A) ws) s) x2` THEN
      REWRITE_TAC[moi_fsa_dclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`moi_fsa_relab y (w:A) ws t1`;
                            `moi_fsa_relabe y (w:A) ws e`] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FSA_RELABE_SIZE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`; `ws:A`;
                     `e:A->bool`; `t1:A->bool`] MOI_FSA_RELAB_EDGE_IFF) THEN
      MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`; `ws:A`;
                     `e:A->bool`; `t2:A->bool`] MOI_FSA_RELAB_EDGE_IFF) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:A->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(t:A->bool) IN {t | t IN s /\ moi_fsa_relab y (w:A) ws t IN x2}`
  MP_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

(* The un-pinching inequality: a dual-connected piece with a boundary edge, *)
(* pinched at w (two local pieces y and the rest), has V + F <= E.          *)

let MOI_FSA_UNPINCH = prove
 (`!s y (w:A) ws.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> t HAS_SIZE 3) /\
        (!e. e IN moi_fsa_edges s ==> CARD {t | t IN s /\ e SUBSET t} <= 2) /\
        moi_fsa_dconn s /\
        (?e. e IN moi_fsa_edges s /\ CARD {t | t IN s /\ e SUBSET t} = 1) /\
        y SUBSET s /\ ~(y = {}) /\ (!t. t IN y ==> w IN t) /\
        moi_fsa_lclosed s w y /\
        (?t. t IN s /\ w IN t /\ ~(t IN y)) /\ ~(ws IN UNIONS s)
        ==> CARD(UNIONS s) + CARD s <= CARD(moi_fsa_edges s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `s2 = IMAGE (moi_fsa_relab y (w:A) ws) s` THEN
  SUBGOAL_THEN `!t1 t2:A->bool. t1 IN s /\ t2 IN s /\
                 moi_fsa_relab y w ws t1 = moi_fsa_relab y w ws t2 ==> t1 = t2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_RELAB_INJ THEN
    MAP_EVERY EXISTS_TAC [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`;
                          `ws:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e1 e2:A->bool. e1 IN moi_fsa_edges s /\ e2 IN moi_fsa_edges s /\
                    moi_fsa_relabe y w ws e1 = moi_fsa_relabe y w ws e2
                    ==> e1 = e2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_RELABE_INJ THEN
    MAP_EVERY EXISTS_TAC [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`;
                          `ws:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(moi_fsa_edges(s:(A->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN ASM_MESON_TAC[HAS_SIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_edges s2 = IMAGE (moi_fsa_relabe y (w:A) ws)
                                         (moi_fsa_edges s)`
  ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN MATCH_MP_TAC MOI_FSA_EDGES_RELAB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e1:A->bool. e1 IN moi_fsa_edges s
                ==> CARD {t | t IN s2 /\ moi_fsa_relabe y w ws e1 SUBSET t} =
                    CARD {t | t IN s /\ e1 SUBSET t}`
  ASSUME_TAC THENL
   [X_GEN_TAC `e1:A->bool` THEN DISCH_TAC THEN EXPAND_TAC "s2" THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`; `ws:A`;
                   `e1:A->bool`] MOI_FSA_TRI_RELAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s2:(A->bool)->bool` MOI_FSA_COUNT) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s2" THEN ASM_SIMP_TAC[FINITE_IMAGE];
      EXPAND_TAC "s2" THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      EXPAND_TAC "s2" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `t1:A->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_FSA_RELAB_SIZE THEN
      EXISTS_TAC `s:(A->bool)->bool` THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      EXPAND_TAC "s2" THEN MATCH_MP_TAC MOI_FSA_DCONN_RELAB THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
   [EXISTS_TAC `moi_fsa_relabe y (w:A) ws e` THEN
    ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(s2:(A->bool)->bool) = CARD(s:(A->bool)->bool) /\
                CARD(moi_fsa_edges s2) = CARD(moi_fsa_edges(s:(A->bool)->bool)) /\
                CARD(UNIONS s2) = CARD(UNIONS(s:(A->bool)->bool)) + 1`
  (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "s2" THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "s2" THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `w:A`; `ws:A`]
      MOI_FSA_UNIONS_RELAB) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `FINITE(UNIONS s:A->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. PL disks with a planar model and a prescribed boundary curve: d is the *)
(* PL image of a planar 2-simplex k, j the image of its relative frontier.  *)
(* Triangles are such disks; two of them meeting exactly in a common arc of *)
(* their boundaries glue to one (the planar triangles of PL_BALL_2_UNION).  *)
(* ------------------------------------------------------------------------- *)

let moi_fsa_disk = new_definition
 `moi_fsa_disk (d:real^N->bool) (j:real^N->bool) <=>
    ?k:real^2->bool f g. &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\
                         IMAGE f (relative_frontier k) = j`;;

(* Edges of a triangle meet only at the common vertex.                      *)

let MOI_FSA_TRI_EDGES = prove
 (`!a b c:real^N.
        ~collinear {a,b,c}
        ==> segment[a,b] INTER segment[b,c] = {b} /\
            segment[b,c] INTER segment[c,a] = {c} /\
            segment[c,a] INTER segment[a,b] = {a}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~affine_dependent {a:real^N,b,c} /\ ~(a = b) /\ ~(a = c) /\
                ~(b = c)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  REPEAT CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CONVEX_HULL_INTER o lhand o snd) THEN
  (ANTS_TAC THENL
    [UNDISCH_TAC `~affine_dependent {a:real^N,b,c}` THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_INDEPENDENT_SUBSET) THEN
     SET_TAC[];
     DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC(MESON[CONVEX_HULL_SING] `s = {x:real^N} ==> convex hull s = {x}`) THEN
  ASM SET_TAC[]);;

let MOI_FSA_TRI_RF_DIFF = prove
 (`!a b c:real^N.
        ~collinear {a,b,c}
        ==> relative_frontier(convex hull {a,b,c}) DIFF
            (segment[a,b] DIFF {a,b}) =
            segment[b,c] UNION segment[c,a]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSA_TRI_EDGES) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`b:real^N`; `c:real^N`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`c:real^N`; `a:real^N`] ENDS_IN_SEGMENT) THEN
  ASM SET_TAC[]);;

(* A triangle is a PL disk with its relative frontier as boundary.          *)

let MOI_FSA_DISK_TRI = prove
 (`!t:real^N->bool. &2 simplex t ==> moi_fsa_disk t (relative_frontier t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~collinear{b:real^N,b,c}` THEN
    REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `vec 0:real^2`; `basis 1:real^2`;
                 `basis 2:real^2`; `linepath(a:real^N,b)`]
    MOI_PL2_TRIANGLE_BOUNDARY_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_LINEPATH; MOI_PL2_PL_LINEPATH; MOI_PL2_STD_TRIANGLES;
                 MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    ASM_SIMP_TAC[PATH_IMAGE_LINEPATH; RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^N` (X_CHOOSE_THEN
    `g0:real^N->real^2` (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`convex hull {vec 0:real^2,basis 1,basis 2}`;
                 `t:real^N->bool`; `2`; `f0:real^2->real^N`;
                 `g0:real^N->real^2`] PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    MESON_TAC[MOI_PL2_STD_TRIANGLES];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN
    `g:real^N->real^2` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_fsa_disk] THEN
  MAP_EVERY EXISTS_TAC [`convex hull {vec 0:real^2,basis 1,basis 2}`;
                        `f:real^2->real^N`; `g:real^N->real^2`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN MESON_TAC[MOI_PL2_STD_TRIANGLES];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `IMAGE (f0:real^2->real^N)
      (relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^2. x IN s ==> (f:real^2->real^N) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `pl_homeomorphism
        (relative_frontier (convex hull {vec 0:real^2, basis 1, basis 2}),
         relative_frontier t) (f0:real^2->real^N,g0)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

(* Normalising a disk so that a given boundary arc is the edge e0 e1 of a   *)
(* planar model triangle.                                                   *)

let MOI_FSA_DISK_EDGE = prove
 (`!(d:real^N->bool) j (al:real^1->real^N) (e0:real^2) e1 e2.
        moi_fsa_disk d j /\ arc al /\ pl_map_on (interval[vec 0,vec 1]) al /\
        path_image al SUBSET j /\ ~collinear{e0,e1,e2}
        ==> ?f g. pl_homeomorphism (convex hull {e0,e1,e2},d) (f,g) /\
                  IMAGE f (relative_frontier(convex hull {e0,e1,e2})) = j /\
                  !x. x IN interval[vec 0,vec 1]
                      ==> f(linepath(e0,e1) x) = al x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_disk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^2->bool`
    (X_CHOOSE_THEN `f1:real^2->real^N` (X_CHOOSE_THEN `g1:real^N->real^2`
      STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_PL_HOMEO_IMAGE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_PL_HOMEO_CONTINUOUS) THEN
  SUBGOAL_THEN `!x:real^2. x IN k ==> (g1:real^N->real^2)(f1 x) = x`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_LINV]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN d ==> (f1:real^2->real^N)(g1 y) = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_RINV]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    SUBGOAL_THEN `closure k = (k:real^2->bool)` SUBST1_TAC THENL
     [REWRITE_TAC[CLOSURE_EQ] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (al:real^1->real^N) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (al:real^1->real^N) SUBSET j` THEN
    EXPAND_TAC "j" THEN UNDISCH_TAC `IMAGE (f1:real^2->real^N) k = d` THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier(k:real^2->bool) = relative_frontier k` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 simplex (k:real^2->bool)` THEN
    REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_PL2_FRONTIER_TRIANGLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `(g1:real^N->real^2) o (al:real^1->real^N)`;
                 `e0:real^2`; `e1:real^2`; `e2:real^2`]
    MOI_PL2_BALL_BOUNDARY_ARC) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_BALL_SIMPLEX] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `d:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[pl_homeomorphism];
        ASM_MESON_TAC[path_image]];
      REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN
      UNDISCH_TAC `path_image (al:real^1->real^N) SUBSET j` THEN
      EXPAND_TAC "j" THEN
      UNDISCH_TAC `relative_frontier k SUBSET (k:real^2->bool)` THEN
      UNDISCH_TAC `!x:real^2. x IN k ==> (g1:real^N->real^2)(f1 x) = x` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^2->real^2` (X_CHOOSE_THEN
    `psi:real^2->real^2` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(f1:real^2->real^N) o (phi:real^2->real^2)`;
                        `(psi:real^2->real^2) o (g1:real^N->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN EXPAND_TAC "j" THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `frontier(convex hull {e0:real^2,e1,e2}) =
      relative_frontier(convex hull {e0,e1,e2})`
    (SUBST1_TAC o SYM) THENL
     [ASM_SIMP_TAC[MOI_PL2_FRONTIER_TRIANGLE]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC MOI_PL2_HOMEOMORPHISM_FRONTIER THEN
    EXISTS_TAC `psi:real^2->real^2` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]];
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `path_image (al:real^1->real^N) SUBSET d` THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

(* Facts about the two standard planar triangles of PL_BALL_2_UNION.        *)

let MOI_FSA_STD_RF = prove
 (`relative_frontier(convex hull {basis 1:real^2,basis 2,--basis 2}) =
   (segment[basis 1,basis 2] UNION segment[basis 2,vec 0]) UNION
   (segment[basis 1,--basis 2] UNION segment[--basis 2,vec 0]) /\
   relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2}) DIFF
   (segment[vec 0,basis 1] DIFF {vec 0,basis 1}) =
   segment[basis 1,basis 2] UNION segment[basis 2,vec 0] /\
   relative_frontier(convex hull {vec 0:real^2,basis 1,--basis 2}) DIFF
   (segment[vec 0,basis 1] DIFF {vec 0,basis 1}) =
   segment[basis 1,--basis 2] UNION segment[--basis 2,vec 0]`,
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; MOI_PL2_STD_TRIANGLES] THEN
    SUBGOAL_THEN `segment[basis 2,--basis 2] =
                  segment[basis 2:real^2,vec 0] UNION segment[vec 0,--basis 2]`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC UNION_SEGMENT THEN
      REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&1 / &2` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    MATCH_MP_TAC MOI_FSA_TRI_RF_DIFF THEN REWRITE_TAC[MOI_PL2_STD_TRIANGLES];
    MATCH_MP_TAC MOI_FSA_TRI_RF_DIFF THEN REWRITE_TAC[MOI_PL2_STD_TRIANGLES]]);;

(* Gluing two disks along a common boundary arc.                            *)

let MOI_FSA_GLUE = prove
 (`!(d1:real^N->bool) j1 d2 j2 (al:real^1->real^N).
        moi_fsa_disk d1 j1 /\ moi_fsa_disk d2 j2 /\
        arc al /\ pl_map_on (interval[vec 0,vec 1]) al /\
        d1 INTER d2 = path_image al /\
        path_image al SUBSET j1 /\ path_image al SUBSET j2
        ==> moi_fsa_disk (d1 UNION d2)
              ((j1 UNION j2) DIFF
               (path_image al DIFF {pathstart al,pathfinish al}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d1:real^N->bool`; `j1:real^N->bool`; `al:real^1->real^N`;
                 `vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`]
    MOI_FSA_DISK_EDGE) THEN
  ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^2->real^N` (X_CHOOSE_THEN
    `q1:real^N->real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d2:real^N->bool`; `j2:real^N->bool`; `al:real^1->real^N`;
                 `vec 0:real^2`; `basis 1:real^2`; `--basis 2:real^2`]
    MOI_FSA_DISK_EDGE) THEN
  ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^2->real^N` (X_CHOOSE_THEN
    `q2:real^N->real^2` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `T1 = convex hull {vec 0:real^2,basis 1,basis 2}` THEN
  ABBREV_TAC `T2 = convex hull {vec 0:real^2,basis 1,--basis 2}` THEN
  SUBGOAL_THEN `compact(T1:real^2->bool) /\ compact(T2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(d1:real^N->bool) /\ compact(d2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[vec 0:real^2,basis 1] SUBSET T1 /\
                segment[vec 0:real^2,basis 1] SUBSET T2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^2. z IN segment[vec 0,basis 1]
               ==> ?x. x IN interval[vec 0,vec 1] /\ z = linepath(vec 0,basis 1) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p1:real^2->real^N) (segment[vec 0,basis 1]) =
                path_image al /\
                IMAGE (p2:real^2->real^N) (segment[vec 0,basis 1]) =
                path_image al`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image; GSYM IMAGE_o] THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x:real^1. x IN s ==> (f:real^1->real^N) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`T1:real^2->bool`; `T2:real^2->bool`; `d1:real^N->bool`;
                 `d2:real^N->bool`; `p1:real^2->real^N`; `q1:real^N->real^2`;
                 `p2:real^2->real^N`; `q2:real^N->real^2`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    SUBGOAL_THEN `(T1:real^2->bool) INTER T2 = segment[vec 0,basis 1]`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN REWRITE_TAC[MOI_PL2_STD_TRIANGLES];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `linepath(vec 0:real^2,basis 1)`))
                           (concl th) && not(can (find_term ((=) `p1:real^2->real^N`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = \x:real^2. if x IN T1 then (p1:real^2->real^N) x else p2 x` THEN
  ABBREV_TAC `Q = \y:real^N. if y IN d1 then (q1:real^N->real^2) y else q2 y` THEN
  DISCH_TAC THEN
  REWRITE_TAC[moi_fsa_disk] THEN
  MAP_EVERY EXISTS_TAC [`convex hull {basis 1:real^2,basis 2,--basis 2}`;
                        `P:real^2->real^N`; `Q:real^N->real^2`] THEN
  SUBGOAL_THEN `(T1:real^2->bool) UNION T2 =
                convex hull {basis 1,basis 2,--basis 2}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN REWRITE_TAC[MOI_PL2_STD_TRIANGLES];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN MESON_TAC[MOI_PL2_STD_TRIANGLES];
    UNDISCH_TAC `pl_homeomorphism (T1 UNION T2,d1 UNION d2)
                  (P:real^2->real^N,Q)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(T1:real^2->bool) INTER T2 = segment[vec 0,basis 1]`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN REWRITE_TAC[MOI_PL2_STD_TRIANGLES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^2. x IN T1 /\ x IN T2 ==> (p1:real^2->real^N) x = p2 x`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN segment[vec 0,basis 1]` MP_TAC THENL
     [SUBGOAL_THEN `(z:real^2) IN T1 INTER T2` MP_TAC THENL
       [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x y:real^2. x IN T1 /\ y IN T1 /\ (p1:real^2->real^N) x = p1 y ==> x = y) /\
    (!x y:real^2. x IN T2 /\ y IN T2 /\ (p2:real^2->real^N) x = p2 y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `(q1:real^N->real^2)(p1 x) = x /\ q1(p1 y) = y` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC MOI_PL2_PL_HOMEO_LINV THEN
        MAP_EVERY EXISTS_TAC [`T1:real^2->bool`; `d1:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC];
      SUBGOAL_THEN `(q2:real^N->real^2)(p2 x) = x /\ q2(p2 y) = y` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC MOI_PL2_PL_HOMEO_LINV THEN
        MAP_EVERY EXISTS_TAC [`T2:real^2->bool`; `d2:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p1:real^2->real^N) (vec 0) = pathstart al /\
    p1 (basis 1) = pathfinish al /\
    (p2:real^2->real^N) (vec 0) = pathstart al /\
    p2 (basis 1) = pathfinish al`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[pathstart; pathfinish] THEN
    MP_TAC(SPEC `vec 0:real^1` (ASSUME
     `!x. x IN interval[vec 0,vec 1]
          ==> (p1:real^2->real^N)(linepath(vec 0,basis 1) x) = al x`)) THEN
    MP_TAC(SPEC `vec 1:real^1` (ASSUME
     `!x. x IN interval[vec 0,vec 1]
          ==> (p1:real^2->real^N)(linepath(vec 0,basis 1) x) = al x`)) THEN
    MP_TAC(SPEC `vec 0:real^1` (ASSUME
     `!x. x IN interval[vec 0,vec 1]
          ==> (p2:real^2->real^N)(linepath(vec 0,basis 1) x) = al x`)) THEN
    MP_TAC(SPEC `vec 1:real^1` (ASSUME
     `!x. x IN interval[vec 0,vec 1]
          ==> (p2:real^2->real^N)(linepath(vec 0,basis 1) x) = al x`)) THEN
    REWRITE_TAC[REWRITE_RULE[pathstart] PATHSTART_LINEPATH;
                REWRITE_RULE[pathfinish] PATHFINISH_LINEPATH;
                ENDS_IN_UNIT_INTERVAL] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p1:real^2->real^N) (segment[vec 0,basis 1] DIFF {vec 0,basis 1}) =
    path_image al DIFF {pathstart al,pathfinish al} /\
    IMAGE (p2:real^2->real^N) (segment[vec 0,basis 1] DIFF {vec 0,basis 1}) =
    path_image al DIFF {pathstart al,pathfinish al}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!s a b c d (f:real^2->real^N).
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        a SUBSET s /\ b SUBSET a /\ IMAGE f a = c /\ IMAGE f b = d
        ==> IMAGE f (a DIFF b) = c DIFF d`) THEN
    REWRITE_TAC[IMAGE_CLAUSES] THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `T1:real^2->bool`; EXISTS_TAC `T2:real^2->bool`] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier T1 SUBSET (T1:real^2->bool) /\
    relative_frontier T2 SUBSET (T2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC MOI_FSA_STD_RF THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC
   (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM))) THEN
  REWRITE_TAC[IMAGE_UNION] THEN
  SUBGOAL_THEN
   `IMAGE (P:real^2->real^N)
      (relative_frontier T1 DIFF (segment[vec 0,basis 1] DIFF {vec 0,basis 1})) =
    IMAGE p1
      (relative_frontier T1 DIFF (segment[vec 0,basis 1] DIFF {vec 0,basis 1})) /\
    IMAGE (P:real^2->real^N)
      (relative_frontier T2 DIFF (segment[vec 0,basis 1] DIFF {vec 0,basis 1})) =
    IMAGE p2
      (relative_frontier T2 DIFF (segment[vec 0,basis 1] DIFF {vec 0,basis 1}))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x:real^2. x IN s ==> (f:real^2->real^N) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [UNDISCH_TAC `~((z:real^2) IN T1)` THEN
      UNDISCH_TAC `relative_frontier T1 SUBSET (T1:real^2->bool)` THEN
      UNDISCH_TAC `(z:real^2) IN relative_frontier T1` THEN SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check
        (fun th -> can (find_term ((=) `p2:real^2->real^N`)) (concl th) &&
                   is_forall(concl th) &&
                   can (find_term ((=) `p1:real^2->real^N`)) (concl th) &&
                   is_eq(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `relative_frontier T2 SUBSET (T2:real^2->bool)` THEN
      UNDISCH_TAC `(z:real^2) IN relative_frontier T2` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[vec 0:real^2,basis 1] DIFF {vec 0,basis 1} SUBSET T1 /\
    segment[vec 0:real^2,basis 1] DIFF {vec 0,basis 1} SUBSET T2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> s DIFF u SUBSET (t:real^2->bool)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(f:real^2->real^N) s a b.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        a SUBSET s /\ b SUBSET s
        ==> IMAGE f (a DIFF b) = IMAGE f a DIFF IMAGE f b`
  (fun th -> MP_TAC(ISPECL [`p1:real^2->real^N`; `T1:real^2->bool`;
                            `relative_frontier T1:real^2->bool`;
                            `segment[vec 0:real^2,basis 1] DIFF {vec 0,basis 1}`] th) THEN
             MP_TAC(ISPECL [`p2:real^2->real^N`; `T2:real^2->bool`;
                            `relative_frontier T2:real^2->bool`;
                            `segment[vec 0:real^2,basis 1] DIFF {vec 0,basis 1}`] th))
  THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN SET_TAC[]);;

(* Attaching a triangle along one edge, or along a path of two edges.       *)

let MOI_FSA_ATTACH1 = prove
 (`!(d:real^N->bool) j a b c.
        moi_fsa_disk d j /\ ~collinear{a,b,c} /\
        d INTER convex hull {a,b,c} = segment[a,b] /\ segment[a,b] SUBSET j
        ==> moi_fsa_disk (d UNION convex hull {a,b,c})
              ((j UNION relative_frontier(convex hull {a,b,c})) DIFF
               (segment[a,b] DIFF {a,b}))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~collinear{b:real^N,b,c}` THEN
    REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `j:real^N->bool`;
                 `convex hull {a:real^N,b,c}`;
                 `relative_frontier(convex hull {a:real^N,b,c})`;
                 `linepath(a:real^N,b)`] MOI_FSA_GLUE) THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARC_LINEPATH; MOI_PL2_PL_LINEPATH;
               MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSA_DISK_TRI THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN SET_TAC[]]);;

let MOI_FSA_ATTACH2 = prove
 (`!(d:real^N->bool) j a b c.
        moi_fsa_disk d j /\ ~collinear{a,b,c} /\
        d INTER convex hull {a,b,c} = segment[a,c] UNION segment[c,b] /\
        segment[a,c] UNION segment[c,b] SUBSET j
        ==> moi_fsa_disk (d UNION convex hull {a,b,c})
              ((j UNION relative_frontier(convex hull {a,b,c})) DIFF
               ((segment[a,c] UNION segment[c,b]) DIFF {a,b}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `j:real^N->bool`;
                 `convex hull {a:real^N,b,c}`;
                 `relative_frontier(convex hull {a:real^N,b,c})`;
                 `linepath(a:real^N,c) ++ linepath(c,b)`] MOI_FSA_GLUE) THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
           PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSA_DISK_TRI THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC ARC_JOIN THEN
    ASM_SIMP_TAC[ARC_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                 PATH_IMAGE_LINEPATH] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FSA_TRI_EDGES) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Pieces of a triangulated surface.  The surface is given abstractly by *)
(* its vertex triples d (moi_fsa_surf) together with the geometric          *)
(* condition that hulls of subsets of triples meet in the hull of the       *)
(* common vertices (moi_fsa_geom).  A good piece is a dual-connected,       *)
(* locally connected, nonempty set of triples with boundary and V + F =     *)
(* E + 1; it will be shown to be a PL disk whose boundary is the union of   *)
(* its boundary edges (by induction on the number of triangles).           *)
(* ------------------------------------------------------------------------- *)

let moi_fsa_poly = new_definition
 `moi_fsa_poly (s:(real^N->bool)->bool) = UNIONS {convex hull t | t IN s}`;;

let moi_fsa_bd = new_definition
 `moi_fsa_bd (s:(A->bool)->bool) =
    {e | e IN moi_fsa_edges s /\ CARD {t | t IN s /\ e SUBSET t} = 1}`;;

let moi_fsa_geom = new_definition
 `moi_fsa_geom (d:(real^N->bool)->bool) <=>
    (!t. t IN d ==> ~affine_dependent t) /\
    (!s s'. (?t. t IN d /\ s SUBSET t) /\ (?t'. t' IN d /\ s' SUBSET t')
            ==> convex hull s INTER convex hull s' = convex hull (s INTER s'))`;;

let moi_fsa_good = new_definition
 `moi_fsa_good (d:(A->bool)->bool) (s:(A->bool)->bool) <=>
    s SUBSET d /\ ~(s = {}) /\ moi_fsa_dconn s /\ (!x. moi_fsa_lconn s x) /\
    ~(moi_fsa_bd s = {}) /\
    CARD(UNIONS s) + CARD s = CARD(moi_fsa_edges s) + 1`;;

(* The edges of one triangle.                                               *)

let MOI_FSA_EDGES_OF_TRI = prove
 (`!a b c:A.
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> {e | e HAS_SIZE 2 /\ e SUBSET {a,b,c}} = {{a,b},{a,c},{b,c}}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `e:A->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  EQ_TAC THENL
   [REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `y:A`
      STRIP_ASSUME_TAC)) MP_TAC) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_MESON_TAC[INSERT_AC];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN SET_TAC[]]);;

let MOI_FSA_FRESH = prove
 (`!s:real^N->bool. FINITE s ==> ?x. ~(x IN s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `s:real^N->bool`] INFINITE_DIFF_FINITE) THEN
  ASM_REWRITE_TAC[EUCLIDEAN_SPACE_INFINITE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_UNIV] THEN MESON_TAC[]);;

(* Hulls of subsets of triples: intersections and open edges.               *)

let MOI_FSA_POLY_INTER_TRI = prove
 (`!d x (t:real^N->bool).
        moi_fsa_geom d /\ x SUBSET d /\ t IN d
        ==> moi_fsa_poly x INTER convex hull t =
            UNIONS {convex hull (u INTER t) | u IN x}`,
  REWRITE_TAC[moi_fsa_geom; moi_fsa_poly] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[INTER_UNIONS] THEN AP_TERM_TAC THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC IMAGE_EQ THEN
  X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `u:real^N->bool` THEN ASM SET_TAC[];
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FSA_HULL_SMALL = prove
 (`!s:real^N->bool. FINITE s /\ CARD s <= 1 ==> convex hull s = s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s:real^N->bool = {} \/ ?a. s = {a}` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MOI_FSA_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `CARD(s:real^N->bool) <= 1` THEN
    UNDISCH_TAC `~(s:real^N->bool = {})` THEN ASM_SIMP_TAC[GSYM CARD_EQ_0] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ASM_REWRITE_TAC[CONVEX_HULL_SING]]);;

(* The open part of an edge f meets no other edge.                          *)

let MOI_FSA_OPEN_EDGE = prove
 (`!d (e:real^N->bool) f.
        moi_fsa_geom d /\ e HAS_SIZE 2 /\ f HAS_SIZE 2 /\ ~(e = f) /\
        (?t. t IN d /\ e SUBSET t) /\ (?t. t IN d /\ f SUBSET t)
        ==> convex hull e INTER (convex hull f DIFF f) = {}`,
  REWRITE_TAC[moi_fsa_geom] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!u. (s INTER t = u) /\ u SUBSET (f:real^N->bool)
        ==> s INTER (t DIFF f) = {}`) THEN
  EXISTS_TAC `convex hull (e INTER f:real^N->bool)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (e INTER f:real^N->bool) = e INTER f`
  (fun th -> REWRITE_TAC[th; INTER_SUBSET]) THEN
  MATCH_MP_TAC MOI_FSA_HULL_SMALL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[FINITE_INTER] THEN
  MATCH_MP_TAC(ARITH_RULE `~(n = 2) /\ n <= 2 ==> n <= 1`) THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(e:real^N->bool = f)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `e INTER f:real^N->bool` THEN
    CONJ_TAC THENL [CONV_TAC SYM_CONV; ALL_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[INTER_SUBSET];
    TRANS_TAC LE_TRANS `CARD(e:real^N->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[INTER_SUBSET];
      ASM_REWRITE_TAC[LE_REFL]]]);;

(* A vertex of the complex lies in the hull of a subset of a triple only    *)
(* if it is one of its points.                                              *)

let MOI_FSA_VERTEX_IN_HULL = prove
 (`!d (e:real^N->bool) x.
        moi_fsa_geom d /\ (?t. t IN d /\ e SUBSET t) /\
        (?t. t IN d /\ x IN t) /\ x IN convex hull e
        ==> x IN e`,
  REWRITE_TAC[moi_fsa_geom] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull e INTER convex hull {x:real^N} =
                convex hull (e INTER {x})` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SING_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_SING] THEN
  ASM_CASES_TAC `(x:real^N) IN e` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e INTER {x:real^N} = {}` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[CONVEX_HULL_EMPTY] THEN ASM SET_TAC[]]);;

(* Polyhedra of sets of simplices (vertex sets): unions and open edges.     *)

let MOI_FSA_POLY_UNION = prove
 (`!s t:(real^N->bool)->bool.
        moi_fsa_poly (s UNION t) = moi_fsa_poly s UNION moi_fsa_poly t`,
  REWRITE_TAC[moi_fsa_poly] THEN SET_TAC[]);;

let MOI_FSA_POLY_INSERT = prove
 (`!x s:(real^N->bool)->bool.
        moi_fsa_poly (x INSERT s) = convex hull x UNION moi_fsa_poly s`,
  REWRITE_TAC[moi_fsa_poly] THEN SET_TAC[]);;

let MOI_FSA_POLY_EMPTY = prove
 (`moi_fsa_poly ({}:(real^N->bool)->bool) = {}`,
  REWRITE_TAC[moi_fsa_poly] THEN SET_TAC[]);;

let MOI_FSA_POLY_SING = prove
 (`!x:real^N->bool. moi_fsa_poly {x} = convex hull x`,
  REWRITE_TAC[MOI_FSA_POLY_INSERT; MOI_FSA_POLY_EMPTY; UNION_EMPTY]);;

let MOI_FSA_POLY_DIFF_OPEN = prove
 (`!d E (f:real^N->bool).
        moi_fsa_geom d /\ f HAS_SIZE 2 /\ (?t. t IN d /\ f SUBSET t) /\
        (!e. e IN E ==> e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t)
        ==> moi_fsa_poly E DIFF (convex hull f DIFF f) =
            moi_fsa_poly (E DELETE f) UNION (if f IN E then f else {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_fsa_poly (E DELETE f) INTER (convex hull f DIFF f) =
                ({}:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_poly; INTER_UNIONS; EMPTY_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `u:real^N->bool` THEN
    X_GEN_TAC `e:real^N->bool` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_OPEN_EDGE THEN
    EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) SUBSET convex hull f` ASSUME_TAC THENL
   [REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `E = (f:real^N->bool) INSERT (E DELETE f)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MOI_FSA_POLY_INSERT; DELETE_INSERT; DELETE_DELETE] THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `E DELETE (f:real^N->bool) = E` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[]]);;

(* Removing a vertex that lies on none of the edges.                        *)

let MOI_FSA_POLY_DIFF_VERTEX = prove
 (`!d E (w:real^N).
        moi_fsa_geom d /\ (?t. t IN d /\ w IN t) /\
        (!e. e IN E ==> (?t. t IN d /\ e SUBSET t) /\ ~(w IN e))
        ==> moi_fsa_poly E DIFF {w} = moi_fsa_poly E`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `~((w:real^N) IN s) ==> s DIFF {w} = s`) THEN
  REWRITE_TAC[moi_fsa_poly; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN e` MP_TAC THENL
   [MATCH_MP_TAC MOI_FSA_VERTEX_IN_HULL THEN
    EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* A triangle whose three edges are boundary edges is the whole piece.      *)

let MOI_FSA_CARD1_EQ = prove
 (`!s e (t1:A->bool) t2.
        FINITE s /\ CARD {tt | tt IN s /\ e SUBSET tt} = 1 /\
        t1 IN s /\ e SUBSET t1 /\ t2 IN s /\ e SUBSET t2
        ==> t1 = t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{tt:A->bool | tt IN s /\ e SUBSET tt}` MOI_FSA_CARD_EQ_1) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:A->bool` MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN ASM_MESON_TAC[]);;

let MOI_FSA_CARD2_OTHER = prove
 (`!s e (t:A->bool).
        FINITE s /\ CARD {tt | tt IN s /\ e SUBSET tt} = 2 /\
        t IN s /\ e SUBSET t
        ==> ?t'. t' IN s /\ ~(t' = t) /\ e SUBSET t' /\
                 {tt | tt IN s /\ e SUBSET tt} = {t,t'}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{tt:A->bool | tt IN s /\ e SUBSET tt} HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT]; ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A->bool` (X_CHOOSE_THEN `q:A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq")))) THEN
  SUBGOAL_THEN `!tt:A->bool. tt IN s /\ e SUBSET tt <=> tt = p \/ tt = q`
  (LABEL_TAC "mem") THENL
   [USE_THEN "eq" (MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:A->bool) IN s /\ e SUBSET p /\ (q:A->bool) IN s /\ e SUBSET q`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "mem" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `t:A->bool = p \/ t = q` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [USE_THEN "mem" (fun th -> ASM_MESON_TAC[th]);
    EXISTS_TAC `q:A->bool` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `p:A->bool` THEN ASM_REWRITE_TAC[INSERT_AC]]);;

(* Removing one triangle t: edges, edge counts and vertices.                *)

let MOI_FSA_NTRI_DELETE = prove
 (`!s (t:A->bool) e.
        {tt | tt IN s DELETE t /\ e SUBSET tt} =
        {tt | tt IN s /\ e SUBSET tt} DELETE t`,
  SET_TAC[]);;

let MOI_FSA_EDGES_DELETE = prove
 (`!s (t:A->bool) e.
        FINITE s /\ t IN s
        ==> (e IN moi_fsa_edges (s DELETE t) <=>
             e IN moi_fsa_edges s /\
             ~(e SUBSET t /\ CARD {tt | tt IN s /\ e SUBSET tt} = 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; IN_DELETE] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(u:A->bool = t)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FSA_CARD1_EQ THEN
    MAP_EVERY EXISTS_TAC [`s:(A->bool)->bool`; `e:A->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `u:A->bool = t` THENL
     [ALL_TAC; EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC
     `~((e:A->bool) SUBSET t /\ CARD {tt | tt IN s /\ e SUBSET tt} = 1)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{tt:A->bool | tt IN s /\ e SUBSET tt} = {t}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[CARD_SING]]]);;

let MOI_FSA_UNIONS_DELETE = prove
 (`!s (t:A->bool) x.
        t IN s
        ==> (x IN UNIONS (s DELETE t) <=>
             x IN UNIONS s /\ ~(x IN t /\ !tt. tt IN s /\ x IN tt ==> tt = t))`,
  REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN MESON_TAC[]);;

(* Basic facts about good pieces.                                           *)

let MOI_FSA_GOOD_BASIC = prove
 (`!d s:(A->bool)->bool.
        moi_fsa_surf d /\ moi_fsa_good d s
        ==> FINITE s /\ (!t. t IN s ==> t HAS_SIZE 3) /\
            (!e. e IN moi_fsa_edges s
                 ==> CARD {t | t IN s /\ e SUBSET t} <= 2) /\
            FINITE (moi_fsa_edges s) /\ FINITE (UNIONS s)`,
  REWRITE_TAC[moi_fsa_surf; moi_fsa_good] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:A->bool. t IN s ==> t HAS_SIZE 3` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `e:A->bool`]
      MOI_FSA_SURF_SUB_NTRI) THEN
    ASM_REWRITE_TAC[moi_fsa_surf] THEN SIMP_TAC[];
    MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN ASM_MESON_TAC[HAS_SIZE];
    REWRITE_TAC[FINITE_UNIONS] THEN ASM_MESON_TAC[HAS_SIZE]]);;

(* Non-collinearity of the vertices of a triple of a geometric surface.     *)

let MOI_FSA_GEOM_NONCOL = prove
 (`!d (t:real^N->bool) a b c.
        moi_fsa_geom d /\ t IN d /\ t = {a,b,c} /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> ~collinear{a,b,c}`,
  REWRITE_TAC[moi_fsa_geom] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent {a:real^N,b,c}` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `collinear {a:real^N,b,c}` THEN
  ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]);;

(* Case A: all three edges of t are boundary edges; the piece is t.         *)

let MOI_FSA_CASE_A = prove
 (`!d s (t:real^N->bool) a b w.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_good d s /\
        t IN s /\ t = {a,b,w} /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        CARD {tt | tt IN s /\ {a,w} SUBSET tt} = 1 /\
        CARD {tt | tt IN s /\ {b,w} SUBSET tt} = 1
        ==> moi_fsa_disk (moi_fsa_poly s) (moi_fsa_poly (moi_fsa_bd s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
               lhs(concl th) = `t:real^N->bool`)) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e HAS_SIZE 2 /\ e SUBSET {a,b,w}
                ==> CARD {tt | tt IN s /\ e SUBSET tt} = 1`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `w:real^N`] MOI_FSA_EDGES_OF_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o
      GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s = {{a:real^N,b,w}}` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `moi_fsa_good d (s:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_fsa_good; MOI_FSA_DCONN_ALT] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SING_SUBSET; NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[moi_fsa_dclosed; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`t1:real^N->bool`; `t2:real^N->bool`;
                         `e:real^N->bool`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check
      (fun th -> is_eq(concl th) && lhs(concl th) = `t1:real^N->bool`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FSA_CARD1_EQ THEN
    MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `e:real^N->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_bd {{a:real^N,b,w}} = {{a,b},{a,w},{b,w}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_fsa_bd; moi_fsa_edges; IN_SING] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; UNWIND_THM2] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `w:real^N`] MOI_FSA_EDGES_OF_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o
      GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(TAUT `(p ==> q) ==> (p /\ q <=> p)`) THEN
    DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_SING]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_FSA_POLY_INSERT; MOI_FSA_POLY_SING; GSYM SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `~collinear{a:real^N,b,w}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_GEOM_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `{a:real^N,b,w}`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_fsa_good d {{a:real^N,b,w}}` THEN
    SIMP_TAC[moi_fsa_good; SING_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {a:real^N,b,w}`] MOI_FSA_DISK_TRI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC[SEGMENT_SYM; UNION_ACI]]);;

(* Helpers for removing a triangle.                                         *)

let MOI_FSA_SING_OF_CARD1 = prove
 (`!s e (t:A->bool).
        FINITE s /\ t IN s /\ e SUBSET t /\
        CARD {tt | tt IN s /\ e SUBSET tt} = 1
        ==> {tt | tt IN s /\ e SUBSET tt} = {t}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `u:A->bool` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_CARD1_EQ THEN
    MAP_EVERY EXISTS_TAC [`s:(A->bool)->bool`; `e:A->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_FSA_ONLY_TRI = prove
 (`!s (x:A) p q.
        FINITE s /\ moi_fsa_lconn s x /\ {x,p,q} IN s /\
        CARD {tt | tt IN s /\ {x,p} SUBSET tt} = 1 /\
        CARD {tt | tt IN s /\ {x,q} SUBSET tt} = 1
        ==> !tt. tt IN s /\ x IN tt ==> tt = {x,p,q}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{{x:A,p,q}} = {tt | tt IN s /\ x IN tt}` MP_TAC THENL
   [UNDISCH_TAC `moi_fsa_lconn s (x:A)` THEN REWRITE_TAC[moi_fsa_lconn] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    REWRITE_TAC[moi_fsa_lclosed; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `u:A`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check
      (fun th -> is_eq(concl th) && lhs(concl th) = `t1:A->bool`)) THEN
    UNDISCH_TAC `(u:A) IN {x,p,q}` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FSA_CARD1_EQ THEN
      MAP_EVERY EXISTS_TAC [`s:(A->bool)->bool`; `{x:A,p}`] THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FSA_CARD1_EQ THEN
      MAP_EVERY EXISTS_TAC [`s:(A->bool)->bool`; `{x:A,q}`] THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT]];
    REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* An empty vertex star is locally connected.                               *)

let MOI_FSA_LCONN_EMPTY = prove
 (`!s (x:A). (!t. t IN s ==> ~(x IN t)) ==> moi_fsa_lconn s x`,
  REWRITE_TAC[moi_fsa_lconn] THEN SET_TAC[]);;

(* The edges of a triangle {a,b,w} in a set of triples.                     *)

let MOI_FSA_TRI_EDGE_CASES = prove
 (`!(a:A) b w e.
        ~(a = b) /\ ~(a = w) /\ ~(b = w) /\ e HAS_SIZE 2 /\ e SUBSET {a,b,w}
        ==> e = {a,b} \/ e = {a,w} \/ e = {b,w}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`] MOI_FSA_EDGES_OF_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY]);;

(* Case B (an ear at b): the combinatorics of removing the triangle.        *)

let MOI_FSA_PAIR_NEQ = prove
 (`!(a:A) b w.
        ~(a = b) /\ ~(a = w) /\ ~(b = w)
        ==> ~({a,b} = {a,w}) /\ ~({a,b} = {b,w}) /\ ~({a,w} = {b,w}) /\
            ~({a,w} = {a,b}) /\ ~({b,w} = {a,b}) /\ ~({b,w} = {a,w})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let MOI_FSA_CASE_B_COMB = prove
 (`!d s (a:A) b w.
        moi_fsa_surf d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        CARD {tt | tt IN s /\ {a,w} SUBSET tt} = 2 /\
        CARD {tt | tt IN s /\ {b,w} SUBSET tt} = 1
        ==> moi_fsa_good d (s DELETE {a,b,w}) /\
            (!tt. tt IN s DELETE {a,b,w} ==> ~(b IN tt)) /\
            (?ta. ta IN s DELETE {a,b,w} /\ {a,w} SUBSET ta) /\
            {a,w} IN moi_fsa_bd (s DELETE {a,b,w}) /\
            moi_fsa_bd s =
            (moi_fsa_bd (s DELETE {a,b,w}) DELETE {a,w}) UNION {{a,b},{b,w}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  ABBREV_TAC `s' = (s:(A->bool)->bool) DELETE {a,b,w}` THEN
  (* b lies only in the removed triangle *)
  SUBGOAL_THEN `!tt:A->bool. tt IN s /\ b IN tt ==> tt = {a,b,w}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:(A->bool)->bool`; `b:A`; `a:A`; `w:A`]
      MOI_FSA_ONLY_TRI) THEN
    REWRITE_TAC[SET_RULE `{b:A,a,w} = {a,b,w}`;
                SET_RULE `{b:A,a} = {a,b}`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tt:A->bool. tt IN s' ==> ~(b IN tt)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the other triangle at the edge aw *)
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `{a:A,w}`; `{a:A,b,w}`]
    MOI_FSA_CARD2_OTHER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ta:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD {{a:A,b,w},ta} = 2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_CARD_PAIR THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ta:A->bool) IN s'` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  (* edges, vertices, counts *)
  SUBGOAL_THEN
   `!e:A->bool. e IN moi_fsa_edges s' <=>
                e IN moi_fsa_edges s /\ ~(e = {a,b}) /\ ~(e = {b,w})`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:A->bool` THEN EXPAND_TAC "s'" THEN
    ASM_SIMP_TAC[MOI_FSA_EDGES_DELETE] THEN
    ASM_CASES_TAC `(e:A->bool) IN moi_fsa_edges s` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` ASSUME_TAC THENL
     [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s` THEN
      SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
      ALL_TAC] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`]
        MOI_FSA_TRI_EDGE_CASES) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS s' = (UNIONS s:A->bool) DELETE b` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(u:A->bool) IN s'` THEN EXPAND_TAC "s'" THEN
        SIMP_TAC[IN_DELETE];
        DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      ASM_CASES_TAC `u:A->bool = {a,b,w}` THENL
       [EXISTS_TAC `ta:A->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(x:A) IN u` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        UNDISCH_TAC `{a:A,w} SUBSET ta` THEN REWRITE_TAC[INSERT_SUBSET] THEN
        STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "s'" THEN
        ASM_REWRITE_TAC[IN_DELETE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta}` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[MOI_FSA_NTRI_DELETE] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:A,w} IN moi_fsa_bd s'` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[CARD_SING] THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE; MOI_FSA_PAIR_NEQ] THEN
    EXISTS_TAC `ta:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':(A->bool)->bool) SUBSET s` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{tt | tt IN s /\ {a:A,b} SUBSET tt} = {{a,b,w}} /\
    {tt | tt IN s /\ {b:A,w} SUBSET tt} = {{a,b,w}}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FSA_SING_OF_CARD1 THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b:A = a) /\ ~(w:A = a) /\ ~(w:A = b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_bd s =
    (moi_fsa_bd s' DELETE {a:A,w}) UNION {{a,b},{b,w}}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:A->bool` THEN
    REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM; IN_UNION; IN_DELETE; IN_INSERT;
                NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `e = {a:A,b}` THENL
     [ASM_REWRITE_TAC[CARD_SING] THEN
      REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN EXISTS_TAC `{a:A,b,w}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
      ALL_TAC] THEN
    ASM_CASES_TAC `e = {b:A,w}` THENL
     [ASM_REWRITE_TAC[CARD_SING] THEN
      REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN EXISTS_TAC `{a:A,b,w}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `e = {a:A,w}` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(e:A->bool) IN moi_fsa_edges s` THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "s'" THEN REWRITE_TAC[MOI_FSA_NTRI_DELETE] THEN
    MATCH_MP_TAC(SET_RULE `!s (t:A->bool). ~(t IN s) ==> s = s DELETE t`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` ASSUME_TAC THENL
     [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s` THEN
      SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`] MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_dconn (s':(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC MOI_FSA_DCONN_DELETE THEN
    EXISTS_TAC `ta:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:A->bool`; `e:A->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`] MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [UNDISCH_TAC `{tt | tt IN s /\ {a:A,b} SUBSET tt} = {{a,b,w}}` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING];
      SUBGOAL_THEN `n:A->bool = ta` SUBST1_TAC THENL
       [UNDISCH_TAC `{tt | tt IN s /\ {a:A,w} SUBSET tt} = {{a,b,w},ta}` THEN
        DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
        MP_TAC(ISPECL [`s':(A->bool)->bool`; `ta:A->bool`] MOI_FSA_DCOMP) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      UNDISCH_TAC `{tt | tt IN s /\ {b:A,w} SUBSET tt} = {{a,b,w}}` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. moi_fsa_lconn s' x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `x:A = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_FSA_LCONN_EMPTY THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:A = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXPAND_TAC "s'" THEN
      MATCH_MP_TAC MOI_FSA_LEAF THEN
      MAP_EVERY EXISTS_TAC [`b:A`; `w:A`] THEN ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:A = w` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXPAND_TAC "s'" THEN
      MATCH_MP_TAC MOI_FSA_LEAF THEN
      MAP_EVERY EXISTS_TAC [`b:A`; `a:A`] THEN
      SUBGOAL_THEN `{w:A,b} = {b,w} /\ {w:A,a} = {a,w}`
       (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[LE_REFL] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `s':(A->bool)->bool`; `x:A`]
      MOI_FSA_LCONN_LOCAL) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "s'" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
      X_GEN_TAC `u:A->bool` THEN ASM_CASES_TAC `u = {a:A,b,w}` THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(moi_fsa_edges(s':(A->bool)->bool)) + 2 =
                CARD(moi_fsa_edges(s:(A->bool)->bool))` ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_fsa_edges s' =
                  moi_fsa_edges s DIFF {{a:A,b},{b,w}}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{{a:A,b},{b,w}} SUBSET moi_fsa_edges s /\
                  CARD {{a:A,b},{b,w}} = 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; moi_fsa_edges; IN_ELIM_THM] THEN
        ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN CONJ_TAC THEN
        EXISTS_TAC `{a:A,b,w}` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
        MATCH_MP_TAC MOI_FSA_CARD_PAIR THEN ASM_SIMP_TAC[MOI_FSA_PAIR_NEQ]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{{a:A,b},{b,w}}`; `moi_fsa_edges(s:(A->bool)->bool)`]
      CARD_SUBSET) THEN
    ASM_SIMP_TAC[CARD_DIFF] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(s':(A->bool)->bool) + 1 = CARD(s:(A->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{a:A,b,w}`; `s:(A->bool)->bool`] CARD_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(CARD(s:(A->bool)->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0]; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(UNIONS s':A->bool) + 1 = CARD(UNIONS s:A->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(b:A) IN UNIONS s` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{a:A,b,w}` THEN
      ASM_REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`b:A`; `UNIONS s:A->bool`] CARD_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(CARD(UNIONS s:A->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_good d (s':(A->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_good] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:(A->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `ta:A->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `{a:A,w}` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `CARD(UNIONS s:A->bool) + CARD s = CARD(moi_fsa_edges s) + 1` THEN
      UNDISCH_TAC `CARD(UNIONS s':A->bool) + 1 = CARD(UNIONS s:A->bool)` THEN
      UNDISCH_TAC `CARD(s':(A->bool)->bool) + 1 = CARD(s:(A->bool)->bool)` THEN
      UNDISCH_TAC `CARD(moi_fsa_edges(s':(A->bool)->bool)) + 2 =
                   CARD(moi_fsa_edges(s:(A->bool)->bool))` THEN
      ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `ta:A->bool` THEN ASM_REWRITE_TAC[]);;

(* Case B, geometric part: attach the ear triangle along the edge aw.      *)

let MOI_FSA_CASEB_SETS = prove
 (`!P P' Sab Sbw Swa Saw (a:real^N) w.
        Swa = Saw /\ P DIFF (Saw DIFF {a,w}) = P' UNION {a,w} /\
        Sbw INTER (Saw DIFF {a,w}) = {} /\ Sab INTER (Saw DIFF {a,w}) = {} /\
        a IN Sab /\ w IN Sbw
        ==> (P UNION (Sab UNION Sbw UNION Swa)) DIFF (Saw DIFF {a,w}) =
            P' UNION Sab UNION Sbw`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM SET_TAC[]);;

let MOI_FSA_CASE_B = prove
 (`!d s (a:real^N) b w.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        CARD {tt | tt IN s /\ {a,w} SUBSET tt} = 2 /\
        CARD {tt | tt IN s /\ {b,w} SUBSET tt} = 1 /\
        moi_fsa_disk (moi_fsa_poly (s DELETE {a,b,w}))
                     (moi_fsa_poly (moi_fsa_bd (s DELETE {a,b,w})))
        ==> moi_fsa_disk (moi_fsa_poly s) (moi_fsa_poly (moi_fsa_bd s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `w:real^N`] MOI_FSA_CASE_B_COMB) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s' = (s:(real^N->bool)->bool) DELETE {a,b,w}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `ta:real^N->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN
  SUBGOAL_THEN `~(b:real^N = a) /\ ~(w:real^N = a) /\ ~(w:real^N = b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:(real^N->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_good d (s:(real^N->bool)->bool)` THEN
    SIMP_TAC[moi_fsa_good];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':(real^N->bool)->bool) SUBSET s` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(s':(real^N->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,w} INSERT s' = s` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC INSERT_DELETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,w} IN d` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:(real^N->bool)->bool) SUBSET d` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^N,b,w}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_GEOM_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `{a:real^N,b,w}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,w,b} = {a,b,w}` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_poly s' INTER convex hull {a:real^N,b,w} = segment[a,w]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s':(real^N->bool)->bool`;
                   `{a:real^N,b,w}`] MOI_FSA_POLY_INTER_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC HULL_MONO THEN
      SUBGOAL_THEN `~((b:real^N) IN u)` MP_TAC THENL
       [ASM_SIMP_TAC[]; SET_TAC[]];
      SUBGOAL_THEN `ta INTER {a:real^N,b,w} = {a,w}` ASSUME_TAC THENL
       [SUBGOAL_THEN `~((b:real^N) IN ta)` MP_TAC THENL
         [ASM_SIMP_TAC[];
          UNDISCH_TAC `{a:real^N,w} SUBSET ta` THEN SET_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `convex hull {a:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `ta:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,w] SUBSET moi_fsa_poly(moi_fsa_bd s')`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_poly; SEGMENT_CONVEX_HULL; SUBSET; IN_UNIONS;
                IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `convex hull {a:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{a:real^N,w}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN moi_fsa_bd s'
                ==> e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[moi_fsa_bd; moi_fsa_edges; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`;
                 `moi_fsa_bd (s':(real^N->bool)->bool)`;
                 `{a:real^N,w}`] MOI_FSA_POLY_DIFF_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `segment[b:real^N,w] INTER (segment[a,w] DIFF {a,w}) = {} /\
    segment[a:real^N,b] INTER (segment[a,w] DIFF {a,w}) = {}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_FSA_OPEN_EDGE THEN
    EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE; MOI_FSA_PAIR_NEQ] THEN
    REPEAT CONJ_TAC THEN EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fsa_poly (s':(real^N->bool)->bool)`;
                 `moi_fsa_poly (moi_fsa_bd (s':(real^N->bool)->bool))`;
                 `a:real^N`; `w:real^N`; `b:real^N`] MOI_FSA_ATTACH1) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [UNDISCH_TAC `{a:real^N,b,w} INSERT s' = s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[MOI_FSA_POLY_INSERT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[MOI_FSA_POLY_UNION; MOI_FSA_POLY_INSERT; MOI_FSA_POLY_SING;
              GSYM SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC MOI_FSA_CASEB_SETS THEN
  CONJ_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

(* ------------------------------------------------------------------------- *)
(* 5. Case C: the apex w of the boundary triangle has both other edges      *)
(* interior.  Common bookkeeping, then the interior-apex case C1 and the    *)
(* boundary-apex case C2.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_FSA_LCONN_DCOMP = prove
 (`!s (x:A) t0.
        moi_fsa_lconn s x /\ t0 IN s /\ x IN t0
        ==> {t | t IN s /\ x IN t} SUBSET moi_fsa_dcomp s t0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `t0:A->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_fsa_lconn s (x:A)` THEN REWRITE_TAC[moi_fsa_lconn] THEN
  DISCH_THEN(MP_TAC o SPEC `{t | t IN moi_fsa_dcomp s t0 /\ (x:A) IN t}`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `t0:A->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_fsa_lclosed; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `u:A`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fsa_dclosed s (moi_fsa_dcomp s (t0:A->bool))` THEN
      REWRITE_TAC[moi_fsa_dclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`t:A->bool`; `{u:A,x}`] THEN
      ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE; INSERT_SUBSET; EMPTY_SUBSET]];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_FSA_STAR_FULL = prove
 (`!d s (w:A).
        moi_fsa_surf d /\ s SUBSET d /\ (?t. t IN s /\ w IN t) /\
        (!u. ~(u = w) /\ {w,u} IN moi_fsa_edges s
             ==> CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 2)
        ==> {tt | tt IN s /\ w IN tt} = {tt | tt IN d /\ w IN tt}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_surf]) THEN
  SUBGOAL_THEN `moi_fsa_lconn d (w:A)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_lconn] THEN
  DISCH_THEN(MP_TAC o SPEC `{tt | tt IN s /\ (w:A) IN tt}`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[moi_fsa_lclosed; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `u:A`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(w:A = u)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `{w:A,u} IN moi_fsa_edges s` ASSUME_TAC THENL
       [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
        ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN EXISTS_TAC `t1:A->bool` THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN `{w:A,u} IN moi_fsa_edges d` ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_FSA_EDGES_MONO; SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `{tt | tt IN s /\ {w:A,u} SUBSET tt} =
                    {tt | tt IN d /\ {w,u} SUBSET tt}` MP_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET_EQ THEN
        ASM_SIMP_TAC[FINITE_RESTRICT] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `t2:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; INSERT_SUBSET; EMPTY_SUBSET]];
    DISCH_THEN ACCEPT_TAC]);;

let MOI_FSA_PAIR_DELETE = prove
 (`!x y:A. ~(y = x) ==> {x,y} DELETE x = {y}`,
  SET_TAC[]);;

let MOI_FSA_CASE_C_BASIC = prove
 (`!d s (a:A) b w ta tb.
        moi_fsa_surf d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w})
        ==> ta IN s DELETE {a,b,w} /\ tb IN s DELETE {a,b,w} /\
            (!tt. tt IN s DELETE {a,b,w} ==> ~({a,b} SUBSET tt)) /\
            (!e. e IN moi_fsa_edges (s DELETE {a,b,w}) <=>
                 e IN moi_fsa_edges s /\ ~(e = {a,b})) /\
            UNIONS (s DELETE {a,b,w}) = UNIONS s /\
            CARD(UNIONS (s DELETE {a,b,w})) + CARD (s DELETE {a,b,w}) =
            CARD(moi_fsa_edges (s DELETE {a,b,w})) + 1 /\
            {tt | tt IN s DELETE {a,b,w} /\ {a,w} SUBSET tt} = {ta} /\
            {tt | tt IN s DELETE {a,b,w} /\ {b,w} SUBSET tt} = {tb} /\
            {a,w} IN moi_fsa_bd (s DELETE {a,b,w}) /\
            {b,w} IN moi_fsa_bd (s DELETE {a,b,w}) /\
            moi_fsa_bd s =
            ((moi_fsa_bd (s DELETE {a,b,w}) DELETE {a,w}) DELETE {b,w}) UNION
            {{a,b}} /\
            (!x. ~(x = w) ==> moi_fsa_lconn (s DELETE {a,b,w}) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  ABBREV_TAC `s' = (s:(A->bool)->bool) DELETE {a,b,w}` THEN
  SUBGOAL_THEN `~(b:A = a) /\ ~(w:A = a) /\ ~(w:A = b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`] MOI_FSA_PAIR_NEQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(ta:A->bool) IN s /\ {a:A,w} SUBSET ta` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s /\ {a:A,w} SUBSET tt} = {{a,b,w},ta}` THEN
    DISCH_THEN(MP_TAC o SPEC `ta:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tb:A->bool) IN s /\ {b:A,w} SUBSET tb` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s /\ {b:A,w} SUBSET tt} = {{a,b,w},tb}` THEN
    DISCH_THEN(MP_TAC o SPEC `tb:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN ta /\ (w:A) IN ta /\ (b:A) IN tb /\ (w:A) IN tb`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`{a:A,w} SUBSET ta`; `{b:A,w} SUBSET tb`] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{tt | tt IN s /\ {a:A,b} SUBSET tt} = {{a,b,w}}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_SING_OF_CARD1 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {{a:A,b,w},ta} = 2 /\ CARD {{a:A,b,w},tb} = 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FSA_CARD_PAIR THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {tt | tt IN s /\ {a:A,w} SUBSET tt} = 2 /\
                CARD {tt | tt IN s /\ {b:A,w} SUBSET tt} = 2`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ta:A->bool) IN s' /\ (tb:A->bool) IN s'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `!tt:A->bool. tt IN s' ==> ~({a,b} SUBSET tt)` ASSUME_TAC THENL
   [X_GEN_TAC `tt:A->bool` THEN EXPAND_TAC "s'" THEN REWRITE_TAC[IN_DELETE] THEN
    STRIP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `{tt | tt IN s /\ {a:A,b} SUBSET tt} = {{a,b,w}}` THEN
    DISCH_THEN(MP_TAC o SPEC `tt:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:A->bool. e IN moi_fsa_edges s' <=>
                e IN moi_fsa_edges s /\ ~(e = {a,b})` ASSUME_TAC THENL
   [X_GEN_TAC `e:A->bool` THEN EXPAND_TAC "s'" THEN
    ASM_SIMP_TAC[MOI_FSA_EDGES_DELETE] THEN
    ASM_CASES_TAC `(e:A->bool) IN moi_fsa_edges s` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `e = {a:A,b}` THENL
     [ASM_REWRITE_TAC[CARD_SING] THEN
      REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
      ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` ASSUME_TAC THENL
     [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s` THEN
      SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`] MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS s' = UNIONS (s:(A->bool)->bool)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(u:A->bool) IN s'` THEN EXPAND_TAC "s'" THEN
      SIMP_TAC[IN_DELETE];
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `u:A->bool = {a,b,w}` THENL
       [UNDISCH_TAC `(x:A) IN u` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        STRIP_TAC THENL
         [EXISTS_TAC `ta:A->bool`; EXISTS_TAC `tb:A->bool`;
          EXISTS_TAC `ta:A->bool`] THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "s'" THEN
        ASM_REWRITE_TAC[IN_DELETE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:A,b} IN moi_fsa_edges s` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN
    EXISTS_TAC `{a:A,b,w}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(UNIONS s':A->bool) + CARD(s':(A->bool)->bool) =
                CARD(moi_fsa_edges(s':(A->bool)->bool)) + 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_fsa_edges s' = moi_fsa_edges s DELETE {a:A,b}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN ASM_REWRITE_TAC[IN_DELETE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`{a:A,b,w}`; `s:(A->bool)->bool`] CARD_DELETE) THEN
    MP_TAC(ISPECL [`{a:A,b}`; `moi_fsa_edges(s:(A->bool)->bool)`]
      CARD_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(CARD(s:(A->bool)->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `~(CARD(moi_fsa_edges(s:(A->bool)->bool)) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `{a:A,b}` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `CARD(UNIONS s:A->bool) + CARD s = CARD(moi_fsa_edges s) + 1` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta} /\
                {tt | tt IN s' /\ {b:A,w} SUBSET tt} = {tb}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[MOI_FSA_NTRI_DELETE] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FSA_PAIR_DELETE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:A,w} IN moi_fsa_bd s' /\ {b:A,w} IN moi_fsa_bd s'`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[CARD_SING] THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN
    REPEAT CONJ_TAC THEN EXISTS_TAC `{a:A,b,w}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_bd s =
    ((moi_fsa_bd s' DELETE {a:A,w}) DELETE {b,w}) UNION {{a,b}}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:A->bool` THEN
    REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM; IN_UNION; IN_DELETE; IN_SING] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `e = {a:A,b}` THENL
     [ASM_REWRITE_TAC[CARD_SING]; ALL_TAC] THEN
    ASM_CASES_TAC `e = {a:A,w}` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `e = {b:A,w}` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(e:A->bool) IN moi_fsa_edges s` THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "s'" THEN REWRITE_TAC[MOI_FSA_NTRI_DELETE] THEN
    MATCH_MP_TAC(SET_RULE `!s (t:A->bool). ~(t IN s) ==> s = s DELETE t`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` ASSUME_TAC THENL
     [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s` THEN
      SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`] MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. ~(x = w) ==> moi_fsa_lconn s' x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:A = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXPAND_TAC "s'" THEN
      MATCH_MP_TAC MOI_FSA_LEAF THEN
      MAP_EVERY EXISTS_TAC [`b:A`; `w:A`] THEN ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:A = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXPAND_TAC "s'" THEN
      MATCH_MP_TAC MOI_FSA_LEAF THEN
      MAP_EVERY EXISTS_TAC [`a:A`; `w:A`] THEN
      SUBGOAL_THEN `{b:A,a} = {a,b}` (fun th -> REWRITE_TAC[th]) THENL
       [SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[LE_REFL] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `s':(A->bool)->bool`; `x:A`]
      MOI_FSA_LCONN_LOCAL) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "s'" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
      X_GEN_TAC `u:A->bool` THEN ASM_CASES_TAC `u = {a:A,b,w}` THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Case C1: the apex w is an interior vertex.                               *)

let MOI_FSA_CASE_C1_COMB = prove
 (`!d s (a:A) b w ta tb.
        moi_fsa_surf d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w}) /\
        (!u. ~(u = w) /\ {w,u} IN moi_fsa_edges s
             ==> CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 2)
        ==> moi_fsa_good d (s DELETE {a,b,w}) /\
            (!e. e IN moi_fsa_bd (s DELETE {a,b,w}) /\ w IN e
                 ==> e = {a,w} \/ e = {b,w})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`] MOI_FSA_CASE_C_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s' = (s:(A->bool)->bool) DELETE {a,b,w}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  SUBGOAL_THEN `~(b:A = a) /\ ~(w:A = a) /\ ~(w:A = b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:A,w} SUBSET ta` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta}` THEN
    DISCH_THEN(MP_TAC o SPEC `ta:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{b:A,w} SUBSET tb` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {b:A,w} SUBSET tt} = {tb}` THEN
    DISCH_THEN(MP_TAC o SPEC `tb:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN ta /\ (w:A) IN tb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`{a:A,w} SUBSET ta`; `{b:A,w} SUBSET tb`] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ta:A->bool) IN s /\ (tb:A->bool) IN s` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(ta:A->bool) IN s'`; `(tb:A->bool) IN s'`] THEN
    EXPAND_TAC "s'" THEN SIMP_TAC[IN_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:A,b,w} IN d` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:(A->bool)->bool) SUBSET d` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{tt | tt IN s /\ (w:A) IN tt} = {tt | tt IN d /\ w IN tt}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_STAR_FULL THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{a:A,b,w}` THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_lconn s' (w:A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:(A->bool)->bool`; `{a:A,b,w}`; `w:A`] MOI_FSA_CYC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MOI_FSA_LCONN_LOCAL THEN
    EXPAND_TAC "s'" THEN
    REWRITE_TAC[SET_RULE `!s (u:A->bool) (w:A).
      {t | t IN s DELETE u /\ w IN t} = {t | t IN s /\ w IN t} DELETE u`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_dconn (s':(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC MOI_FSA_DCONN_DELETE THEN
    EXISTS_TAC `ta:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:A->bool`; `e:A->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(n:A->bool) IN s'` ASSUME_TAC THENL
     [EXPAND_TAC "s'" THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`] MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `n:A->bool = ta` SUBST1_TAC THENL
       [UNDISCH_TAC `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta}` THEN
        DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING];
        MP_TAC(ISPECL [`s':(A->bool)->bool`; `ta:A->bool`] MOI_FSA_DCOMP) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      SUBGOAL_THEN `n:A->bool = tb` SUBST1_TAC THENL
       [UNDISCH_TAC `{tt | tt IN s' /\ {b:A,w} SUBSET tt} = {tb}` THEN
        DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING];
        MP_TAC(ISPECL [`s':(A->bool)->bool`; `w:A`; `ta:A->bool`]
          MOI_FSA_LCONN_DCOMP) THEN
        ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. moi_fsa_lconn s' x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x:A = w` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_fsa_good] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:(A->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s'" THEN REWRITE_TAC[DELETE_SUBSET];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `ta:A->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `{a:A,w}` THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `e:A->bool` THEN REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(e:A->bool) IN moi_fsa_edges s /\ e HAS_SIZE 2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges s'` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `(e:A->bool) SUBSET {a,b,w}` THENL
   [MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`] MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:A) IN e` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:A->bool`; `w:A`] MOI_SCF_OTHER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `CARD {t | t IN s' /\ {w:A,u} SUBSET t} = 1` THEN
  EXPAND_TAC "s'" THEN REWRITE_TAC[MOI_FSA_NTRI_DELETE] THEN
  SUBGOAL_THEN `~({a:A,b,w} IN {t | t IN s /\ {w,u} SUBSET t})`
   (fun th -> REWRITE_TAC[MATCH_MP (SET_RULE
      `!s (t:A->bool). ~(t IN s) ==> s DELETE t = s`) th]) THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_SIMP_TAC[] THEN ARITH_TAC);;

let MOI_FSA_CASEC1_SETS = prove
 (`!P P1 P2 Sab Sbw Swa Saw Swb (a:real^N) b w.
        Swa = Saw /\ Swb = Sbw /\
        P DIFF (Saw DIFF {a,w}) = P1 UNION {a,w} /\
        P1 DIFF (Sbw DIFF {b,w}) = P2 UNION {b,w} /\
        P2 DIFF {w} = P2 /\
        Sab INTER (Saw DIFF {a,w}) = {} /\ Sab INTER (Sbw DIFF {b,w}) = {} /\
        a IN Sab /\ b IN Sab /\ ~(w IN Sab) /\ w IN Saw /\
        ~(a = w) /\ ~(b = w) /\ ~(a = b)
        ==> (P UNION (Sab UNION Sbw UNION Swa)) DIFF
            ((Saw UNION Swb) DIFF {a,b}) = P2 UNION Sab`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM SET_TAC[]);;

let MOI_FSA_CASE_C1 = prove
 (`!d s (a:real^N) b w ta tb.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w}) /\
        (!u. ~(u = w) /\ {w,u} IN moi_fsa_edges s
             ==> CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 2) /\
        moi_fsa_disk (moi_fsa_poly (s DELETE {a,b,w}))
                     (moi_fsa_poly (moi_fsa_bd (s DELETE {a,b,w})))
        ==> moi_fsa_disk (moi_fsa_poly s) (moi_fsa_poly (moi_fsa_bd s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `w:real^N`; `ta:real^N->bool`;
                 `tb:real^N->bool`] MOI_FSA_CASE_C_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `w:real^N`; `ta:real^N->bool`;
                 `tb:real^N->bool`] MOI_FSA_CASE_C1_COMB) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s' = (s:(real^N->bool)->bool) DELETE {a,b,w}` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_fsa_bd (s:(real^N->bool)->bool)`)) THEN
  SUBGOAL_THEN `~(b:real^N = a) /\ ~(w:real^N = a) /\ ~(w:real^N = b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:(real^N->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_good d (s:(real^N->bool)->bool)` THEN
    SIMP_TAC[moi_fsa_good];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':(real^N->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_good d (s':(real^N->bool)->bool)` THEN
    SIMP_TAC[moi_fsa_good];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,w} INSERT s' = s` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC INSERT_DELETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,w} IN d` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:(real^N->bool)->bool) SUBSET d` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^N,b,w}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_GEOM_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `{a:real^N,b,w}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,w} SUBSET ta` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {a:real^N,w} SUBSET tt} = {ta}` THEN
    DISCH_THEN(MP_TAC o SPEC `ta:real^N->bool` o
      GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{b:real^N,w} SUBSET tb` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {b:real^N,w} SUBSET tt} = {tb}` THEN
    DISCH_THEN(MP_TAC o SPEC `tb:real^N->bool` o
      GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ta INTER {a:real^N,b,w} = {a,w} /\
                tb INTER {a:real^N,b,w} = {w,b}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~({a:real^N,b} SUBSET ta) /\ ~({a:real^N,b} SUBSET tb)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`{a:real^N,w} SUBSET ta`; `{b:real^N,w} SUBSET tb`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_poly s' INTER convex hull {a:real^N,b,w} =
    segment[a,w] UNION segment[w,b]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s':(real^N->bool)->bool`;
                   `{a:real^N,b,w}`] MOI_FSA_POLY_INTER_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~({a:real^N,b} SUBSET u)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; DE_MORGAN_THM] THEN
      STRIP_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!s t u:real^N->bool. s SUBSET u ==> s SUBSET t UNION u`) THEN
        MATCH_MP_TAC HULL_MONO THEN UNDISCH_TAC `~((a:real^N) IN u)` THEN
        SET_TAC[];
        MATCH_MP_TAC(SET_RULE
         `!s t u:real^N->bool. s SUBSET t ==> s SUBSET t UNION u`) THEN
        MATCH_MP_TAC HULL_MONO THEN UNDISCH_TAC `~((b:real^N) IN u)` THEN
        SET_TAC[]];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THENL
       [EXISTS_TAC `convex hull {a:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `ta:real^N->bool` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `convex hull {w:real^N,b}` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `tb:real^N->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[a:real^N,w] UNION segment[w,b] SUBSET moi_fsa_poly(moi_fsa_bd s')`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; moi_fsa_poly; SEGMENT_CONVEX_HULL] THEN
    CONJ_TAC THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THENL
     [EXISTS_TAC `convex hull {a:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `{a:real^N,w}` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `convex hull {w:real^N,b}` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `{b:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
      AP_TERM_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN moi_fsa_bd s'
                ==> e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[moi_fsa_bd; moi_fsa_edges; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`;
                 `moi_fsa_bd (s':(real^N->bool)->bool)`;
                 `{a:real^N,w}`] MOI_FSA_POLY_DIFF_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`;
                 `moi_fsa_bd (s':(real^N->bool)->bool) DELETE {a,w}`;
                 `{b:real^N,w}`] MOI_FSA_POLY_DIFF_OPEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IN_DELETE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{b:real^N,w} IN moi_fsa_bd s' DELETE {a,w}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_DELETE; MOI_FSA_PAIR_NEQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`;
                 `(moi_fsa_bd (s':(real^N->bool)->bool) DELETE {a,w})
                  DELETE {b,w}`;
                 `w:real^N`] MOI_FSA_POLY_DIFF_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    X_GEN_TAC `e:real^N->bool` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `!e:real^N->bool. e IN moi_fsa_bd s' /\ w IN e
                 ==> e = {a,w} \/ e = {b,w}` THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `segment[a:real^N,b] INTER (segment[a,w] DIFF {a,w}) = {} /\
    segment[a:real^N,b] INTER (segment[b,w] DIFF {b,w}) = {}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_FSA_OPEN_EDGE THEN
    EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE; MOI_FSA_PAIR_NEQ] THEN
    REPEAT CONJ_TAC THEN EXISTS_TAC `{a:real^N,b,w}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^N) IN segment[a,b])` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `{a:real^N,b}`; `w:real^N`]
      MOI_FSA_VERTEX_IN_HULL) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fsa_poly (s':(real^N->bool)->bool)`;
                 `moi_fsa_poly (moi_fsa_bd (s':(real^N->bool)->bool))`;
                 `a:real^N`; `b:real^N`; `w:real^N`] MOI_FSA_ATTACH2) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [UNDISCH_TAC `{a:real^N,b,w} INSERT s' = s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[MOI_FSA_POLY_INSERT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[MOI_FSA_POLY_UNION; MOI_FSA_POLY_SING;
              GSYM SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC MOI_FSA_CASEC1_SETS THEN
  MAP_EVERY EXISTS_TAC
   [`moi_fsa_poly (moi_fsa_bd (s':(real^N->bool)->bool) DELETE {a,w})`;
    `w:real^N`] THEN
  CONJ_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

(* Generic facts about dual components used in case C2.                    *)

let MOI_FSA_DCLOSED_UNION = prove
 (`!s y1 y2:(A->bool)->bool.
        moi_fsa_dclosed s y1 /\ moi_fsa_dclosed s y2
        ==> moi_fsa_dclosed s (y1 UNION y2)`,
  REWRITE_TAC[moi_fsa_dclosed; IN_UNION] THEN MESON_TAC[]);;

let MOI_FSA_LCLOSED_UNION = prove
 (`!s (x:A) y1 y2.
        moi_fsa_lclosed s x y1 /\ moi_fsa_lclosed s x y2
        ==> moi_fsa_lclosed s x (y1 UNION y2)`,
  REWRITE_TAC[moi_fsa_lclosed; IN_UNION] THEN MESON_TAC[]);;

let MOI_FSA_DCOMP_SUB = prove
 (`!s t0 t1:A->bool.
        t0 IN s /\ t1 IN moi_fsa_dcomp s t0
        ==> moi_fsa_dcomp s t1 SUBSET moi_fsa_dcomp s t0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `t0:A->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t1:A->bool) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `t1:A->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FSA_DCOMP_LCLOSED = prove
 (`!s (x:A) t0.
        t0 IN s
        ==> moi_fsa_lclosed s x {t | t IN moi_fsa_dcomp s t0 /\ x IN t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `t0:A->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_fsa_lclosed; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `u:A`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_fsa_dclosed s (moi_fsa_dcomp s (t0:A->bool))` THEN
  REWRITE_TAC[moi_fsa_dclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:A->bool`; `{u:A,x}`] THEN
  ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE; INSERT_SUBSET; EMPTY_SUBSET]);;

let MOI_FSA_LCOMP_SUB_DCOMP = prove
 (`!s (x:A) t0.
        t0 IN s /\ x IN t0
        ==> moi_fsa_lcomp s x t0 SUBSET moi_fsa_dcomp s t0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `t0:A->bool`] MOI_FSA_DCOMP) THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `x:A`; `t0:A->bool`] MOI_FSA_LCOMP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_fsa_lcomp s (x:A) t0 SUBSET {t | t IN moi_fsa_dcomp s t0 /\ x IN t}`
  MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MOI_FSA_DCOMP_LCLOSED; IN_ELIM_THM] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_FSA_LCONN_DCOMP_SUB = prove
 (`!s (x:A) t0.
        moi_fsa_lconn s x /\ t0 IN s
        ==> moi_fsa_lconn (moi_fsa_dcomp s t0) x`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?t1:A->bool. t1 IN moi_fsa_dcomp s t0 /\ x IN t1` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t1:A->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `t0:A->bool`] MOI_FSA_DCOMP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t1:A->bool) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `x:A`; `t1:A->bool`]
      MOI_FSA_LCONN_DCOMP) THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `t0:A->bool`; `t1:A->bool`]
      MOI_FSA_DCOMP_SUB) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`moi_fsa_dcomp s (t0:A->bool)`; `s:(A->bool)->bool`; `x:A`]
      MOI_FSA_LCONN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_FSA_LCONN_EMPTY THEN ASM_MESON_TAC[]]);;

let MOI_FSA_DCLOSED_NTRI = prove
 (`!s y (e:A->bool).
        y SUBSET s /\ moi_fsa_dclosed s y /\ e IN moi_fsa_edges y
        ==> {t | t IN s /\ e SUBSET t} = {t | t IN y /\ e SUBSET t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_edges; moi_fsa_dclosed; IN_ELIM_THM] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `t':A->bool` THEN ASM_MESON_TAC[SUBSET]);;

let MOI_FSA_EDGES_UNION = prove
 (`!s t:(A->bool)->bool.
        moi_fsa_edges (s UNION t) = moi_fsa_edges s UNION moi_fsa_edges t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]);;

let MOI_FSA_BD_SPLIT = prove
 (`!s y:(A->bool)->bool.
        y SUBSET s /\ moi_fsa_dclosed s y
        ==> moi_fsa_bd s = moi_fsa_bd y UNION moi_fsa_bd (s DIFF y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_fsa_dclosed s (s DIFF y:(A->bool)->bool) /\
                s DIFF y SUBSET s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_DCLOSED_DIFF] THEN SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:A->bool` THEN
  REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM; IN_UNION] THEN
  ASM_CASES_TAC `(e:A->bool) IN moi_fsa_edges y` THENL
   [SUBGOAL_THEN `~((e:A->bool) IN moi_fsa_edges (s DIFF y))` ASSUME_TAC THENL
     [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; IN_DIFF] THEN
      UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges y` THEN
      REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
      UNDISCH_TAC `moi_fsa_dclosed s (y:(A->bool)->bool)` THEN
      REWRITE_TAC[moi_fsa_dclosed] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `y:(A->bool)->bool`; `e:A->bool`]
      MOI_FSA_DCLOSED_NTRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(e:A->bool) IN moi_fsa_edges s`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[MOI_FSA_EDGES_MONO; SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `(e:A->bool) IN moi_fsa_edges (s DIFF y)` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `s DIFF y:(A->bool)->bool`;
                   `e:A->bool`] MOI_FSA_DCLOSED_NTRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(e:A->bool) IN moi_fsa_edges s`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[MOI_FSA_EDGES_MONO; SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((e:A->bool) IN moi_fsa_edges s)`
   (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `~((e:A->bool) IN moi_fsa_edges y)` THEN
  UNDISCH_TAC `~((e:A->bool) IN moi_fsa_edges (s DIFF y))` THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[]);;

let MOI_FSA_SPLIT_COUNT = prove
 (`!s y:(A->bool)->bool.
        FINITE s /\ (!t. t IN s ==> FINITE t) /\
        y SUBSET s /\ moi_fsa_dclosed s y
        ==> CARD s = CARD y + CARD (s DIFF y) /\
            CARD (moi_fsa_edges s) =
            CARD (moi_fsa_edges y) + CARD (moi_fsa_edges (s DIFF y)) /\
            CARD (UNIONS s) =
            (CARD (UNIONS y) + CARD (UNIONS (s DIFF y))) -
            CARD (UNIONS y INTER UNIONS (s DIFF y))`,
  REPEAT STRIP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `e:A->bool` THEN
      REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; IN_DIFF] THEN
      UNDISCH_TAC `moi_fsa_dclosed s (y:(A->bool)->bool)` THEN
      REWRITE_TAC[moi_fsa_dclosed] THEN MESON_TAC[];
      REWRITE_TAC[GSYM MOI_FSA_EDGES_UNION] THEN AP_TERM_TAC THEN
      ASM SET_TAC[]];
    SUBGOAL_THEN `UNIONS s = UNIONS y UNION UNIONS (s DIFF y:(A->bool)->bool)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM UNIONS_UNION] THEN AP_TERM_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_UNION_GEN THEN CONJ_TAC THEN
    REWRITE_TAC[FINITE_UNIONS] THEN
    ASM_MESON_TAC[FINITE_SUBSET; SUBSET_DIFF; IN_DIFF; SUBSET]]);;

(* Case C2: the apex w is a boundary vertex.                               *)

let MOI_FSA_C2_NOTDCONN = prove
 (`!d s (a:A) b w ta tb u.
        moi_fsa_surf d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w}) /\
        ~(u = w) /\ {w,u} IN moi_fsa_edges s /\
        CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 1 /\
        (?ws:A. ~(ws IN UNIONS s))
        ==> ~(tb IN moi_fsa_lcomp (s DELETE {a,b,w}) w ta) /\
            ~moi_fsa_dconn (s DELETE {a,b,w})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`] MOI_FSA_CASE_C_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s' = (s:(A->bool)->bool) DELETE {a,b,w}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  SUBGOAL_THEN `{a:A,w} SUBSET ta` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta}` THEN
    DISCH_THEN(MP_TAC o SPEC `ta:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{b:A,w} SUBSET tb` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {b:A,w} SUBSET tt} = {tb}` THEN
    DISCH_THEN(MP_TAC o SPEC `tb:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN ta /\ (a:A) IN ta /\ (w:A) IN tb /\ (b:A) IN tb`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`{a:A,w} SUBSET ta`; `{b:A,w} SUBSET tb`] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ta:A->bool) IN s /\ (tb:A->bool) IN s` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(ta:A->bool) IN s'`; `(tb:A->bool) IN s'`] THEN
    EXPAND_TAC "s'" THEN SIMP_TAC[IN_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:A. v IN {a,b,w} <=> v = w \/ v = a \/ v = b`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~moi_fsa_lconn s' (w:A)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `{a:A,b,w}`;
                   `w:A`; `a:A`; `b:A`; `ta:A->bool`; `tb:A->bool`; `u:A`]
      MOI_FSA_NOTLOC_COUNT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((tb:A->bool) IN moi_fsa_lcomp s' w ta)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~moi_fsa_lconn s' (w:A)` THEN
    REWRITE_TAC[] THEN EXPAND_TAC "s'" THEN
    MATCH_MP_TAC MOI_FSA_NOTLOC_CONN THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `b:A`; `ta:A->bool`; `tb:A->bool`] THEN
    SUBGOAL_THEN `{w:A,a} = {a,w} /\ {w:A,b} = {b,w}`
     (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(s':(A->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:(A->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s'" THEN REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s':(A->bool)->bool`; `w:A`; `ta:A->bool`] MOI_FSA_LCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s':(A->bool)->bool`; `moi_fsa_lcomp s' (w:A) ta`;
                 `w:A`; `ws:A`] MOI_FSA_UNPINCH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s'" THEN ASM_SIMP_TAC[FINITE_DELETE];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `ta:A->bool` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(t:A->bool) IN s'` THEN EXPAND_TAC "s'" THEN
      SIMP_TAC[IN_DELETE];
      X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`d:(A->bool)->bool`; `s':(A->bool)->bool`; `e:A->bool`]
        MOI_FSA_SURF_SUB_NTRI) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      EXISTS_TAC `{a:A,w}` THEN
      UNDISCH_TAC `{a:A,w} IN moi_fsa_bd s'` THEN
      SIMP_TAC[moi_fsa_bd; IN_ELIM_THM];
      UNDISCH_TAC `moi_fsa_lcomp s' (w:A) ta SUBSET {t | t IN s' /\ w IN t}` THEN
      SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `ta:A->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_fsa_lcomp s' (w:A) ta SUBSET {t | t IN s' /\ w IN t}` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[];
      EXISTS_TAC `tb:A->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    UNDISCH_TAC `CARD(UNIONS s':A->bool) + CARD s' =
                 CARD(moi_fsa_edges s') + 1` THEN ARITH_TAC]);;

let MOI_FSA_C2_PARTS = prove
 (`!d s (a:A) b w ta tb u sa sb.
        moi_fsa_surf d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w}) /\
        ~(u = w) /\ {w,u} IN moi_fsa_edges s /\
        CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 1 /\
        (?ws:A. ~(ws IN UNIONS s)) /\
        moi_fsa_dcomp (s DELETE {a,b,w}) ta = sa /\
        (s DELETE {a,b,w}) DIFF sa = sb
        ==> sa UNION sb = s DELETE {a,b,w} /\ sa INTER sb = {} /\
            ta IN sa /\ tb IN sb /\
            moi_fsa_dclosed (s DELETE {a,b,w}) sa /\
            moi_fsa_dclosed (s DELETE {a,b,w}) sb /\
            moi_fsa_dcomp (s DELETE {a,b,w}) tb = sb /\
            moi_fsa_dconn sa /\ moi_fsa_dconn sb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`] MOI_FSA_CASE_C_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`; `u:A`]
    MOI_FSA_C2_NOTDCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ws:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s' = (s:(A->bool)->bool) DELETE {a,b,w}` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  MP_TAC(ISPECL [`s':(A->bool)->bool`; `ta:A->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fsa_dclosed s' (sb:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN MATCH_MP_TAC MOI_FSA_DCLOSED_DIFF THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sb:(A->bool)->bool) SUBSET s'` ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN REWRITE_TAC[SUBSET_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n e. n IN s /\ ~(n = {a:A,b,w}) /\ e HAS_SIZE 2 /\ e SUBSET n /\
          e SUBSET {a,b,w} ==> n IN {ta,tb}`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:A->bool`; `e:A->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(n:A->bool) IN s'` ASSUME_TAC THENL
     [EXPAND_TAC "s'" THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:A`; `b:A`; `w:A`; `e:A->bool`]
      MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [UNDISCH_TAC `!tt:A->bool. tt IN s' ==> ~({a,b} SUBSET tt)` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool`) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta}` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING; IN_INSERT] THEN MESON_TAC[];
      UNDISCH_TAC `{tt | tt IN s' /\ {b:A,w} SUBSET tt} = {tb}` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING; IN_INSERT] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((tb:A->bool) IN sa)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    ASM_CASES_TAC `sb:(A->bool)->bool = {}` THENL
     [UNDISCH_TAC `~moi_fsa_dconn (s':(A->bool)->bool)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `s':(A->bool)->bool = sa` SUBST1_TAC THENL
       [UNDISCH_TAC `s' DIFF sa = (sb:(A->bool)->bool)` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(sa:(A->bool)->bool) SUBSET s'` THEN SET_TAC[];
        EXPAND_TAC "sa" THEN MATCH_MP_TAC MOI_FSA_DCOMP_DCONN THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `{ta:A->bool,tb} SUBSET s' DIFF sb` ASSUME_TAC THENL
     [EXPAND_TAC "sb" THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_DIFF] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `{a:A,b,w}`; `{ta:A->bool,tb}`;
                   `sb:(A->bool)->bool`] MOI_FSA_DCONN_DEL_B) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tb:A->bool) IN sb` ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s':(A->bool)->bool`; `tb:A->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fsa_dcomp s' (tb:A->bool) SUBSET sb` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sb SUBSET moi_fsa_dcomp s' (tb:A->bool)` ASSUME_TAC THENL
   [ABBREV_TAC `y = s' DIFF (sa UNION moi_fsa_dcomp s' (tb:A->bool))` THEN
    ASM_CASES_TAC `y:(A->bool)->bool = {}` THENL
     [UNDISCH_TAC `y:(A->bool)->bool = {}` THEN EXPAND_TAC "y" THEN
      EXPAND_TAC "sb" THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{ta:A->bool,tb} SUBSET s' DIFF y` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_DIFF; IN_UNION] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:(A->bool)->bool) SUBSET s'` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[SUBSET_DIFF]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fsa_dclosed s' (y:(A->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN MATCH_MP_TAC MOI_FSA_DCLOSED_DIFF THEN
      MATCH_MP_TAC MOI_FSA_DCLOSED_UNION THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(A->bool)->bool`; `{a:A,b,w}`; `{ta:A->bool,tb}`;
                   `y:(A->bool)->bool`] MOI_FSA_DCONN_DEL_B) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_dcomp s' (tb:A->bool) = sb` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_dconn (moi_fsa_dcomp s' (ta:A->bool)) /\
                moi_fsa_dconn (moi_fsa_dcomp s' (tb:A->bool))` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FSA_DCOMP_DCONN THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `sa UNION sb = (s':(A->bool)->bool) /\ sa INTER sb = {}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s' DIFF sa = (sb:(A->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(sa:(A->bool)->bool) SUBSET s'` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_FSA_DISJ_MEM = prove
 (`!s t (x:B). s INTER t = {} /\ x IN s /\ x IN t ==> F`,
  SET_TAC[]);;

let MOI_FSA_C2_LOCAL = prove
 (`!d s (a:A) b w ta tb u sa sb.
        moi_fsa_surf d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w}) /\
        ~(u = w) /\ {w,u} IN moi_fsa_edges s /\
        CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 1 /\
        (?ws:A. ~(ws IN UNIONS s)) /\
        moi_fsa_dcomp (s DELETE {a,b,w}) ta = sa /\
        (s DELETE {a,b,w}) DIFF sa = sb
        ==> (!x. moi_fsa_lconn sa x) /\ (!x. moi_fsa_lconn sb x) /\
            (!x. x IN sa ==> ~(b IN x)) /\ (!x. x IN sb ==> ~(a IN x)) /\
            UNIONS sa INTER UNIONS sb = {w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`] MOI_FSA_CASE_C_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`; `u:A`;
                 `sa:(A->bool)->bool`; `sb:(A->bool)->bool`]
    MOI_FSA_C2_PARTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ws:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s' = (s:(A->bool)->bool) DELETE {a,b,w}` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  SUBGOAL_THEN `{a:A,w} SUBSET ta` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta}` THEN
    DISCH_THEN(MP_TAC o SPEC `ta:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{b:A,w} SUBSET tb` ASSUME_TAC THENL
   [UNDISCH_TAC `{tt | tt IN s' /\ {b:A,w} SUBSET tt} = {tb}` THEN
    DISCH_THEN(MP_TAC o SPEC `tb:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN ta /\ (a:A) IN ta /\ (w:A) IN tb /\ (b:A) IN tb`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`{a:A,w} SUBSET ta`; `{b:A,w} SUBSET tb`] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b:A = w) /\ ~(a:A = w)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:A->bool. t IN sa ==> t IN s'` ASSUME_TAC THENL
   [UNDISCH_TAC `sa UNION sb = (s':(A->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:A->bool. t IN sb ==> t IN s'` ASSUME_TAC THENL
   [UNDISCH_TAC `sa UNION sb = (s':(A->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* triangles of sa avoid b, triangles of sb avoid a *)
  SUBGOAL_THEN `!x:A->bool. x IN sa ==> ~(b IN x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:A->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A->bool) IN moi_fsa_dcomp s' tb` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s':(A->bool)->bool`; `b:A`; `tb:A->bool`]
        MOI_FSA_LCONN_DCOMP) THEN
      ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`sa:(A->bool)->bool`; `sb:(A->bool)->bool`; `x:A->bool`]
      MOI_FSA_DISJ_MEM) THEN
    UNDISCH_TAC `(x:A->bool) IN moi_fsa_dcomp s' tb` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A->bool. x IN sb ==> ~(a IN x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:A->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A->bool) IN moi_fsa_dcomp s' ta` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s':(A->bool)->bool`; `a:A`; `ta:A->bool`]
        MOI_FSA_LCONN_DCOMP) THEN
      ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`sa:(A->bool)->bool`; `sb:(A->bool)->bool`; `x:A->bool`]
      MOI_FSA_DISJ_MEM) THEN
    UNDISCH_TAC `(x:A->bool) IN moi_fsa_dcomp s' ta` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the two local components at w *)
  MP_TAC(ISPECL [`s':(A->bool)->bool`; `w:A`; `ta:A->bool`] MOI_FSA_LCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s':(A->bool)->bool`; `w:A`; `tb:A->bool`] MOI_FSA_LCOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fsa_lcomp s' (w:A) ta SUBSET sa /\
                moi_fsa_lcomp s' (w:A) tb SUBSET sb` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s':(A->bool)->bool`; `w:A`; `ta:A->bool`]
      MOI_FSA_LCOMP_SUB_DCOMP) THEN
    MP_TAC(ISPECL [`s':(A->bool)->bool`; `w:A`; `tb:A->bool`]
      MOI_FSA_LCOMP_SUB_DCOMP) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_lcomp s' (w:A) ta UNION moi_fsa_lcomp s' w tb SUBSET
    {tt | tt IN s' /\ w IN tt} /\
    moi_fsa_lclosed s' w (moi_fsa_lcomp s' (w:A) ta UNION
                          moi_fsa_lcomp s' w tb) /\
    ta IN moi_fsa_lcomp s' (w:A) ta UNION moi_fsa_lcomp s' w tb /\
    tb IN moi_fsa_lcomp s' (w:A) ta UNION moi_fsa_lcomp s' w tb`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET; IN_UNION] THEN
    MATCH_MP_TAC MOI_FSA_LCLOSED_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(A->bool)->bool`; `{a:A,b,w}`; `w:A`; `a:A`; `b:A`;
                 `ta:A->bool`; `tb:A->bool`;
                 `moi_fsa_lcomp s' (w:A) ta UNION moi_fsa_lcomp s' w tb`]
    MOI_FSA_SPLIT) THEN
  SUBGOAL_THEN `{w:A,a} = {a,w} /\ {w:A,b} = {b,w}`
   (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (* local connectivity at w *)
  SUBGOAL_THEN `!t:A->bool. t IN s' /\ w IN t
                ==> t IN moi_fsa_lcomp s' w ta \/ t IN moi_fsa_lcomp s' w tb`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `moi_fsa_lcomp s' (w:A) ta UNION moi_fsa_lcomp s' w tb =
                 {tt | tt IN s' /\ w IN tt}` THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `t:A->bool`) THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_lconn sa (w:A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sa:(A->bool)->bool`; `moi_fsa_lcomp s' (w:A) ta`;
                   `w:A`] MOI_FSA_LCONN_LOCAL) THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:A->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(t:A->bool) IN moi_fsa_lcomp s' w ta \/
                      t IN moi_fsa_lcomp s' w tb` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(t:A->bool) IN sb` ASSUME_TAC THENL
         [UNDISCH_TAC `moi_fsa_lcomp s' (w:A) tb SUBSET sb` THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`sa:(A->bool)->bool`; `sb:(A->bool)->bool`;
                       `t:A->bool`] MOI_FSA_DISJ_MEM) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `moi_fsa_lcomp s' (w:A) ta SUBSET sa` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOI_FSA_LCOMP_LCONN THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_lconn sb (w:A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sb:(A->bool)->bool`; `moi_fsa_lcomp s' (w:A) tb`;
                   `w:A`] MOI_FSA_LCONN_LOCAL) THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:A->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(t:A->bool) IN moi_fsa_lcomp s' w ta \/
                      t IN moi_fsa_lcomp s' w tb` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(t:A->bool) IN sa` ASSUME_TAC THENL
         [UNDISCH_TAC `moi_fsa_lcomp s' (w:A) ta SUBSET sa` THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`sa:(A->bool)->bool`; `sb:(A->bool)->bool`;
                       `t:A->bool`] MOI_FSA_DISJ_MEM) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `moi_fsa_lcomp s' (w:A) tb SUBSET sb` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOI_FSA_LCOMP_LCONN THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. moi_fsa_lconn sa x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x:A = w` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "sa" THEN MATCH_MP_TAC MOI_FSA_LCONN_DCOMP_SUB THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. moi_fsa_lconn sb x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x:A = w` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_fsa_lconn (moi_fsa_dcomp s' (tb:A->bool)) x` MP_TAC THENL
     [MATCH_MP_TAC MOI_FSA_LCONN_DCOMP_SUB THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS sa INTER UNIONS sb = {w:A}` ASSUME_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS; IN_SING] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t1:A->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `t2:A->bool` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `x:A = w` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t1:A->bool) IN s' /\ (t2:A->bool) IN s'` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t2:A->bool) IN moi_fsa_dcomp s' t1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s':(A->bool)->bool`; `x:A`; `t1:A->bool`]
        MOI_FSA_LCONN_DCOMP) THEN
      ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t2:A->bool) IN sa` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s':(A->bool)->bool`; `ta:A->bool`; `t1:A->bool`]
        MOI_FSA_DCOMP_SUB) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`sa:(A->bool)->bool`; `sb:(A->bool)->bool`; `t2:A->bool`]
      MOI_FSA_DISJ_MEM) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `ta:A->bool`; EXISTS_TAC `tb:A->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FSA_SUB_FACTS = prove
 (`!d y:(A->bool)->bool.
        moi_fsa_surf d /\ y SUBSET d
        ==> FINITE y /\ (!t. t IN y ==> t HAS_SIZE 3) /\
            (!t. t IN y ==> FINITE t) /\
            (!e. e IN moi_fsa_edges y
                 ==> CARD {t | t IN y /\ e SUBSET t} <= 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_surf]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET];
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET; HAS_SIZE];
    X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d:(A->bool)->bool`; `y:(A->bool)->bool`; `e:A->bool`]
      MOI_FSA_SURF_SUB_NTRI) THEN
    ASM_SIMP_TAC[]]);;

let MOI_FSA_DELETE2_UNION = prove
 (`!s1 s2 (x:B) y.
        ~(y IN s1) /\ ~(x IN s2)
        ==> ((s1 UNION s2) DELETE x) DELETE y = (s1 DELETE x) UNION (s2 DELETE y)`,
  SET_TAC[]);;

let MOI_FSA_CASE_C2_COMB = prove
 (`!d s (a:A) b w ta tb u sa sb.
        moi_fsa_surf d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w}) /\
        ~(u = w) /\ {w,u} IN moi_fsa_edges s /\
        CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 1 /\
        (?ws:A. ~(ws IN UNIONS s)) /\
        moi_fsa_dcomp (s DELETE {a,b,w}) ta = sa /\
        (s DELETE {a,b,w}) DIFF sa = sb
        ==> moi_fsa_good d sa /\ moi_fsa_good d sb /\
            sa UNION sb = s DELETE {a,b,w} /\ sa INTER sb = {} /\
            ta IN sa /\ tb IN sb /\
            (!x. x IN sa ==> ~(b IN x)) /\ (!x. x IN sb ==> ~(a IN x)) /\
            UNIONS sa INTER UNIONS sb = {w} /\
            {a,w} IN moi_fsa_bd sa /\ {b,w} IN moi_fsa_bd sb /\
            moi_fsa_bd s =
            ((moi_fsa_bd sa DELETE {a,w}) UNION (moi_fsa_bd sb DELETE {b,w}))
            UNION {{a,b}} /\
            (?e. e IN (moi_fsa_bd sa DELETE {a,w}) UNION
                      (moi_fsa_bd sb DELETE {b,w}) /\ w IN e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`] MOI_FSA_CASE_C_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`; `u:A`;
                 `sa:(A->bool)->bool`; `sb:(A->bool)->bool`]
    MOI_FSA_C2_PARTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ws:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `a:A`; `b:A`;
                 `w:A`; `ta:A->bool`; `tb:A->bool`; `u:A`;
                 `sa:(A->bool)->bool`; `sb:(A->bool)->bool`]
    MOI_FSA_C2_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ws:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s' = (s:(A->bool)->bool) DELETE {a,b,w}` THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  SUBGOAL_THEN `(s':(A->bool)->bool) SUBSET s` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s':(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[FINITE_DELETE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':(A->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:(A->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{a:A,w} SUBSET ta /\ {b:A,w} SUBSET tb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `{tt | tt IN s' /\ {a:A,w} SUBSET tt} = {ta}` THEN
      DISCH_THEN(MP_TAC o SPEC `ta:A->bool` o GEN_REWRITE_RULE I [EXTENSION]);
      UNDISCH_TAC `{tt | tt IN s' /\ {b:A,w} SUBSET tt} = {tb}` THEN
      DISCH_THEN(MP_TAC o SPEC `tb:A->bool` o GEN_REWRITE_RULE I [EXTENSION])] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN ta /\ (a:A) IN ta /\ (w:A) IN tb /\ (b:A) IN tb`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`{a:A,w} SUBSET ta`; `{b:A,w} SUBSET tb`] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sa:(A->bool)->bool) SUBSET s' /\ sb SUBSET s'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sa UNION sb = (s':(A->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sa:(A->bool)->bool) SUBSET d /\ sb SUBSET d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s':(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sa:(A->bool)->bool) SUBSET s /\ sb SUBSET s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s':(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the special boundary edges of the two pieces *)
  SUBGOAL_THEN `{a:A,w} IN moi_fsa_bd sa` ASSUME_TAC THENL
   [SUBGOAL_THEN `{a:A,w} IN moi_fsa_edges sa` ASSUME_TAC THENL
     [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN
      EXISTS_TAC `ta:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s':(A->bool)->bool`; `sa:(A->bool)->bool`; `{a:A,w}`]
      MOI_FSA_DCLOSED_NTRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CARD_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `{b:A,w} IN moi_fsa_bd sb` ASSUME_TAC THENL
   [SUBGOAL_THEN `{b:A,w} IN moi_fsa_edges sb` ASSUME_TAC THENL
     [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN
      EXISTS_TAC `tb:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s':(A->bool)->bool`; `sb:(A->bool)->bool`; `{b:A,w}`]
      MOI_FSA_DCLOSED_NTRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CARD_SING];
    ALL_TAC] THEN
  (* counting for both pieces *)
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `sa:(A->bool)->bool`]
    MOI_FSA_SUB_FACTS) THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `sb:(A->bool)->bool`]
    MOI_FSA_SUB_FACTS) THEN
  MP_TAC(ISPECL [`d:(A->bool)->bool`; `s':(A->bool)->bool`]
    MOI_FSA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `CARD(UNIONS sa:A->bool) + CARD sa <= CARD(moi_fsa_edges sa) + 1`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `sa:(A->bool)->bool` MOI_FSA_COUNT) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `ta:A->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `{a:A,w}` THEN UNDISCH_TAC `{a:A,w} IN moi_fsa_bd sa` THEN
      SIMP_TAC[moi_fsa_bd; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(UNIONS sb:A->bool) + CARD sb <= CARD(moi_fsa_edges sb) + 1`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `sb:(A->bool)->bool` MOI_FSA_COUNT) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `tb:A->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `{b:A,w}` THEN UNDISCH_TAC `{b:A,w} IN moi_fsa_bd sb` THEN
      SIMP_TAC[moi_fsa_bd; IN_ELIM_THM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s':(A->bool)->bool`; `sa:(A->bool)->bool`]
    MOI_FSA_SPLIT_COUNT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `s' DIFF sa = (sb:(A->bool)->bool)`;
              ASSUME `UNIONS sa INTER UNIONS sb = {w:A}`; CARD_SING] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `1 <= CARD(UNIONS sa:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    SUBGOAL_THEN `FINITE(UNIONS sa:A->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    MAP_EVERY EXISTS_TAC [`w:A`; `ta:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(UNIONS sa:A->bool) + CARD sa = CARD(moi_fsa_edges sa) + 1 /\
    CARD(UNIONS sb:A->bool) + CARD sb = CARD(moi_fsa_edges sb) + 1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD(UNIONS s':A->bool) + CARD s' = CARD(moi_fsa_edges s') + 1` THEN
    UNDISCH_TAC `CARD(UNIONS s':A->bool) =
                 (CARD(UNIONS sa:A->bool) + CARD(UNIONS sb:A->bool)) - 1` THEN
    UNDISCH_TAC `CARD(s':(A->bool)->bool) = CARD(sa:(A->bool)->bool) +
                 CARD(sb:(A->bool)->bool)` THEN
    UNDISCH_TAC `CARD(moi_fsa_edges(s':(A->bool)->bool)) =
                 CARD(moi_fsa_edges(sa:(A->bool)->bool)) +
                 CARD(moi_fsa_edges(sb:(A->bool)->bool))` THEN
    UNDISCH_TAC `1 <= CARD(UNIONS sa:A->bool)` THEN
    UNDISCH_TAC `CARD(UNIONS sa:A->bool) + CARD sa <= CARD(moi_fsa_edges sa) + 1` THEN
    UNDISCH_TAC `CARD(UNIONS sb:A->bool) + CARD sb <= CARD(moi_fsa_edges sb) + 1` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (* goodness of the pieces *)
  SUBGOAL_THEN `~(sa:(A->bool)->bool = {}) /\ ~(sb:(A->bool)->bool = {}) /\
                ~(moi_fsa_bd (sa:(A->bool)->bool) = {}) /\
                ~(moi_fsa_bd (sb:(A->bool)->bool) = {})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `ta:A->bool`; EXISTS_TAC `tb:A->bool`;
      EXISTS_TAC `{a:A,w}`; EXISTS_TAC `{b:A,w}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_good d (sa:(A->bool)->bool) /\
                moi_fsa_good d (sb:(A->bool)->bool)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_good] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* boundary bookkeeping *)
  SUBGOAL_THEN `~({b:A,w} IN moi_fsa_bd sa)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_bd; moi_fsa_edges; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    UNDISCH_TAC `!x:A->bool. x IN sa ==> ~(b IN x)` THEN
    DISCH_THEN(MP_TAC o SPEC `t:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{b:A,w} SUBSET t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({a:A,w} IN moi_fsa_bd sb)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_bd; moi_fsa_edges; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    UNDISCH_TAC `!x:A->bool. x IN sb ==> ~(a IN x)` THEN
    DISCH_THEN(MP_TAC o SPEC `t:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{a:A,w} SUBSET t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_bd s' = moi_fsa_bd sa UNION moi_fsa_bd (sb:(A->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s':(A->bool)->bool`; `sa:(A->bool)->bool`]
      MOI_FSA_BD_SPLIT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_bd s =
    ((moi_fsa_bd sa DELETE {a:A,w}) UNION (moi_fsa_bd sb DELETE {b,w}))
    UNION {{a,b}}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOI_FSA_DELETE2_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w:A = a) /\ ~(w:A = b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~({w:A,u} = {a,b})` ASSUME_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `(w:A) IN {a,b}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INSERT];
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. e IN (moi_fsa_bd sa DELETE {a:A,w}) UNION
             (moi_fsa_bd sb DELETE {b,w}) /\ w IN e`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `{w:A,u} IN moi_fsa_bd s` MP_TAC THENL
     [REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `moi_fsa_bd s =
      ((moi_fsa_bd sa DELETE {a:A,w}) UNION (moi_fsa_bd sb DELETE {b,w}))
      UNION {{a,b}}` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNION; IN_SING] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXISTS_TAC `{w:A,u}` THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOI_FSA_DELETE2_UNION THEN
  ASM_REWRITE_TAC[]);;

(* Case C2, geometric part: attach the triangle to one piece, then glue.   *)

let MOI_FSA_HULL_SUB_POLY = prove
 (`!E (e:real^N->bool). e IN E ==> convex hull e SUBSET moi_fsa_poly E`,
  REWRITE_TAC[moi_fsa_poly] THEN SET_TAC[]);;

let MOI_FSA_POLY_INTER_SING = prove
 (`!d x y (w:real^N).
        moi_fsa_geom d /\ x SUBSET d /\ y SUBSET d /\
        UNIONS x INTER UNIONS y SUBSET {w}
        ==> moi_fsa_poly x INTER moi_fsa_poly y SUBSET {w}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_geom; moi_fsa_poly] THEN
  STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `p:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c1:real^N->bool` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
    (X_CHOOSE_THEN `c2:real^N->bool` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `convex hull u INTER convex hull v = convex hull (u INTER v:real^N->bool)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `u:real^N->bool`; EXISTS_TAC `v:real^N->bool`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u INTER v:real^N->bool) SUBSET {w}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN convex hull {w}` MP_TAC THENL
   [SUBGOAL_THEN `convex hull (u INTER v) SUBSET convex hull {w:real^N}`
    MP_TAC THENL [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[CONVEX_HULL_SING; IN_SING]]);;

let MOI_FSA_CASEC2_SETS = prove
 (`!Pa Pa' Pb Pb' Sab Sbw Swa Saw (a:real^N) b w.
        Swa = Saw /\
        Pa DIFF (Saw DIFF {a,w}) = Pa' UNION {a,w} /\
        Pa' DIFF (Sbw DIFF {b,w}) = Pa' /\
        Pb DIFF (Sbw DIFF {b,w}) = Pb' UNION {b,w} /\
        Sab INTER (Saw DIFF {a,w}) = {} /\
        Sab INTER (Sbw DIFF {b,w}) = {} /\
        a IN Sab /\ b IN Sab /\ w IN Pa' UNION Pb'
        ==> (((Pa UNION (Sab UNION Sbw UNION Swa)) DIFF (Saw DIFF {a,w}))
             UNION Pb) DIFF (Sbw DIFF {b,w}) =
            (Pa' UNION Pb') UNION Sab`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM SET_TAC[]);;

let MOI_FSA_BD_EDGE = prove
 (`!d y (e:A->bool).
        y SUBSET d /\ e IN moi_fsa_bd y
        ==> e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t`,
  REWRITE_TAC[moi_fsa_bd; moi_fsa_edges; IN_ELIM_THM; SUBSET] THEN
  MESON_TAC[]);;

let MOI_FSA_POLY_MEM = prove
 (`!E e (x:real^N). e IN E /\ x IN e ==> x IN moi_fsa_poly E`,
  REWRITE_TAC[moi_fsa_poly; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[HULL_INC]);;

let MOI_FSA_CASE_C2 = prove
 (`!d s (a:real^N) b w ta tb u sa sb.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        {tt | tt IN s /\ {a,w} SUBSET tt} = {{a,b,w},ta} /\
        ~(ta = {a,b,w}) /\
        {tt | tt IN s /\ {b,w} SUBSET tt} = {{a,b,w},tb} /\
        ~(tb = {a,b,w}) /\
        ~(u = w) /\ {w,u} IN moi_fsa_edges s /\
        CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 1 /\
        moi_fsa_dcomp (s DELETE {a,b,w}) ta = sa /\
        (s DELETE {a,b,w}) DIFF sa = sb /\
        moi_fsa_disk (moi_fsa_poly sa) (moi_fsa_poly (moi_fsa_bd sa)) /\
        moi_fsa_disk (moi_fsa_poly sb) (moi_fsa_poly (moi_fsa_bd sb))
        ==> moi_fsa_disk (moi_fsa_poly s) (moi_fsa_poly (moi_fsa_bd s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  SUBGOAL_THEN `?ws:real^N. ~(ws IN UNIONS s)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_FRESH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `w:real^N`; `ta:real^N->bool`;
                 `tb:real^N->bool`; `u:real^N`; `sa:(real^N->bool)->bool`;
                 `sb:(real^N->bool)->bool`] MOI_FSA_CASE_C2_COMB) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s' = (s:(real^N->bool)->bool) DELETE {a,b,w}` THEN
  SUBGOAL_THEN `(s':(real^N->bool)->bool) SUBSET s` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,w} INSERT s' = s` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC INSERT_DELETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_fsa_bd (s:(real^N->bool)->bool)`)) THEN
  SUBGOAL_THEN `~(b:real^N = a) /\ ~(w:real^N = a) /\ ~(w:real^N = b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,w} SUBSET ta /\ {b:real^N,w} SUBSET tb`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `{tt | tt IN s /\ {a:real^N,w} SUBSET tt} = {{a,b,w},ta}` THEN
      DISCH_THEN(MP_TAC o SPEC `ta:real^N->bool` o
        GEN_REWRITE_RULE I [EXTENSION]);
      UNDISCH_TAC `{tt | tt IN s /\ {b:real^N,w} SUBSET tt} = {{a,b,w},tb}` THEN
      DISCH_THEN(MP_TAC o SPEC `tb:real^N->bool` o
        GEN_REWRITE_RULE I [EXTENSION])] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sa SUBSET s' /\ sb SUBSET (s':(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sa UNION sb = (s':(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sa SUBSET d /\ sb SUBSET (d:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s':(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,w} IN d` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:(real^N->bool)->bool) SUBSET d` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^N,b,w}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_GEOM_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `{a:real^N,b,w}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ta INTER {a:real^N,b,w} = {a,w} /\
                tb INTER {a:real^N,b,w} = {b,w}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((b:real^N) IN ta) /\ ~((a:real^N) IN tb)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`{a:real^N,w} SUBSET ta`; `{b:real^N,w} SUBSET tb`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* intersections with the removed triangle *)
  SUBGOAL_THEN
   `moi_fsa_poly sa INTER convex hull {a:real^N,b,w} = segment[a,w]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `sa:(real^N->bool)->bool`;
                   `{a:real^N,b,w}`] MOI_FSA_POLY_INTER_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `v:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC HULL_MONO THEN
      SUBGOAL_THEN `~((b:real^N) IN v)` MP_TAC THENL
       [ASM_SIMP_TAC[]; SET_TAC[]];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `convex hull {a:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `ta:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a:real^N,b,w} INTER moi_fsa_poly sb = segment[b,w]`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `sb:(real^N->bool)->bool`;
                   `{a:real^N,b,w}`] MOI_FSA_POLY_INTER_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `v:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC HULL_MONO THEN
      SUBGOAL_THEN `~((a:real^N) IN v)` MP_TAC THENL
       [ASM_SIMP_TAC[]; SET_TAC[]];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `convex hull {b:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `tb:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_poly sa INTER moi_fsa_poly sb SUBSET {w:real^N}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_POLY_INTER_SING THEN
    EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(moi_fsa_poly sa UNION convex hull {a:real^N,b,w}) INTER moi_fsa_poly sb =
    segment[b,w]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `!s t u:real^N->bool.
      (s UNION t) INTER u = (s INTER u) UNION (t INTER u)`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `!s t (w:real^N). s SUBSET {w} /\ w IN t ==> s UNION t = t`) THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  (* boundary facts *)
  SUBGOAL_THEN `segment[a:real^N,w] SUBSET moi_fsa_poly(moi_fsa_bd sa) /\
                segment[b:real^N,w] SUBSET moi_fsa_poly(moi_fsa_bd sb)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_FSA_HULL_SUB_POLY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!e:real^N->bool. e IN moi_fsa_bd sa ==> e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t) /\
    (!e:real^N->bool. e IN moi_fsa_bd sa DELETE {a,w}
         ==> e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t) /\
    (!e:real^N->bool. e IN moi_fsa_bd sb ==> e HAS_SIZE 2 /\ ?t. t IN d /\ e SUBSET t)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSA_BD_EDGE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{a:real^N,w} HAS_SIZE 2 /\ {b:real^N,w} HAS_SIZE 2 /\
    {a:real^N,b} HAS_SIZE 2 /\
    (?t. t IN d /\ {a:real^N,w} SUBSET t) /\
    (?t. t IN d /\ {b:real^N,w} SUBSET t) /\
    (?t. t IN d /\ {a:real^N,b} SUBSET t)`
  (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
   [ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN REPEAT CONJ_TAC THEN
    EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`;
                 `moi_fsa_bd (sa:(real^N->bool)->bool)`;
                 `{a:real^N,w}`] MOI_FSA_POLY_DIFF_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~({b:real^N,w} IN moi_fsa_bd sa)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_bd; moi_fsa_edges; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    UNDISCH_TAC `!x:real^N->bool. x IN sa ==> ~(b IN x)` THEN
    DISCH_THEN(MP_TAC o SPEC `t0:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{b:real^N,w} SUBSET t0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(moi_fsa_bd sa DELETE {a:real^N,w}) DELETE {b,w} =
                moi_fsa_bd sa DELETE {a,w}` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DELETE_NON_ELEMENT; IN_DELETE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`;
                 `moi_fsa_bd (sa:(real^N->bool)->bool) DELETE {a,w}`;
                 `{b:real^N,w}`] MOI_FSA_POLY_DIFF_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_DELETE; UNION_EMPTY] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`;
                 `moi_fsa_bd (sb:(real^N->bool)->bool)`;
                 `{b:real^N,w}`] MOI_FSA_POLY_DIFF_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `segment[a:real^N,b] INTER (segment[a,w] DIFF {a,w}) = {} /\
    segment[a:real^N,b] INTER (segment[b,w] DIFF {b,w}) = {} /\
    segment[b:real^N,w] INTER (segment[a,w] DIFF {a,w}) = {}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_FSA_OPEN_EDGE THEN
    EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FSA_PAIR_NEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^N) IN moi_fsa_poly(moi_fsa_bd sa DELETE {a,w}) UNION
                  moi_fsa_poly(moi_fsa_bd sb DELETE {b,w})`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FSA_POLY_UNION] THEN
    MATCH_MP_TAC MOI_FSA_POLY_MEM THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* attach the triangle to sa along aw, then glue sb along bw *)
  MP_TAC(ISPECL [`moi_fsa_poly (sa:(real^N->bool)->bool)`;
                 `moi_fsa_poly (moi_fsa_bd (sa:(real^N->bool)->bool))`;
                 `a:real^N`; `w:real^N`; `b:real^N`] MOI_FSA_ATTACH1) THEN
  SUBGOAL_THEN `{a:real^N,w,b} = {a,b,w}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_fsa_poly sa UNION convex hull {a:real^N,b,w}`;
                 `(moi_fsa_poly (moi_fsa_bd sa) UNION
                   relative_frontier(convex hull {a:real^N,b,w})) DIFF
                  (segment[a,w] DIFF {a,w})`;
                 `moi_fsa_poly (sb:(real^N->bool)->bool)`;
                 `moi_fsa_poly (moi_fsa_bd (sb:(real^N->bool)->bool))`;
                 `linepath(b:real^N,w)`] MOI_FSA_GLUE) THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_LINEPATH; MOI_PL2_PL_LINEPATH;
                 MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    UNDISCH_TAC
     `segment[b:real^N,w] INTER (segment[a,w] DIFF {a,w}) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [UNDISCH_TAC `{a:real^N,b,w} INSERT s' = s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `sa UNION sb = (s':(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MOI_FSA_POLY_INSERT; MOI_FSA_POLY_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[MOI_FSA_POLY_UNION; MOI_FSA_POLY_SING;
              GSYM SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC MOI_FSA_CASEC2_SETS THEN
  CONJ_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

(* ------------------------------------------------------------------------- *)
(* 6. The disk theorem for good pieces, by induction on the number of       *)
(* triangles, choosing a boundary edge and its triangle.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FSA_CARD_LT = prove
 (`!s y (t:B). FINITE s /\ t IN s /\ y SUBSET s DELETE t ==> CARD y < CARD s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_PSUBSET THEN
  ASM_REWRITE_TAC[PSUBSET] THEN ASM SET_TAC[]);;

let MOI_FSA_DISK_STEP = prove
 (`!d s (a:real^N) b w.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_good d s /\
        {a,b,w} IN s /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
        CARD {tt | tt IN s /\ {a,b} SUBSET tt} = 1 /\
        (!y. CARD y < CARD s /\ moi_fsa_good d y
             ==> moi_fsa_disk (moi_fsa_poly y) (moi_fsa_poly (moi_fsa_bd y)))
        ==> moi_fsa_disk (moi_fsa_poly s) (moi_fsa_poly (moi_fsa_bd s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  SUBGOAL_THEN `~(b:real^N = a) /\ ~(w:real^N = a) /\ ~(w:real^N = b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (s DELETE {a:real^N,b,w}) < CARD s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_CARD_LT THEN EXISTS_TAC `{a:real^N,b,w}` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e SUBSET {a,b,w} /\ e HAS_SIZE 2
        ==> CARD {tt | tt IN s /\ e SUBSET tt} = 1 \/
            CARD {tt | tt IN s /\ e SUBSET tt} = 2`
  (LABEL_TAC "E") THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `e:real^N->bool`] MOI_FSA_SURF_SUB_NTRI) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
      EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[];
      MESON_TAC[ARITH_RULE `!n. 1 <= n /\ n <= 2 ==> n = 1 \/ n = 2`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,w} SUBSET {a,b,w} /\ {b:real^N,w} SUBSET {a,b,w} /\
                {a:real^N,w} HAS_SIZE 2 /\ {b:real^N,w} HAS_SIZE 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "E" (fun th ->
    MP_TAC(SPEC `{a:real^N,w}` th) THEN MP_TAC(SPEC `{b:real^N,w}` th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `CARD {tt | tt IN s /\ {a:real^N,w} SUBSET tt} = 1` THEN
  ASM_CASES_TAC `CARD {tt | tt IN s /\ {b:real^N,w} SUBSET tt} = 1` THENL
   [(* a single triangle *)
    MATCH_MP_TAC MOI_FSA_CASE_A THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `{a:real^N,b,w}`;
                          `a:real^N`; `b:real^N`; `w:real^N`] THEN
    ASM_REWRITE_TAC[];
    (* an ear with tip a *)
    SUBGOAL_THEN `CARD {tt | tt IN s /\ {b:real^N,w} SUBSET tt} = 2`
    ASSUME_TAC THENL
     [UNDISCH_TAC `CARD {tt | tt IN s /\ {b:real^N,w} SUBSET tt} = 1 \/
                   CARD {tt | tt IN s /\ {b:real^N,w} SUBSET tt} = 2` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{b:real^N,a,w} = {a,b,w} /\ {b:real^N,a} = {a,b}`
    STRIP_ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `b:real^N`; `a:real^N`; `w:real^N`] MOI_FSA_CASE_B) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `b:real^N`; `a:real^N`; `w:real^N`] MOI_FSA_CASE_B_COMB) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* an ear with tip b *)
    SUBGOAL_THEN `CARD {tt | tt IN s /\ {a:real^N,w} SUBSET tt} = 2`
    ASSUME_TAC THENL
     [UNDISCH_TAC `CARD {tt | tt IN s /\ {a:real^N,w} SUBSET tt} = 1 \/
                   CARD {tt | tt IN s /\ {a:real^N,w} SUBSET tt} = 2` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `a:real^N`; `b:real^N`; `w:real^N`] MOI_FSA_CASE_B) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `a:real^N`; `b:real^N`; `w:real^N`] MOI_FSA_CASE_B_COMB) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the apex w has both other edges interior *)
  SUBGOAL_THEN `CARD {tt | tt IN s /\ {a:real^N,w} SUBSET tt} = 2 /\
                CARD {tt | tt IN s /\ {b:real^N,w} SUBSET tt} = 2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD {tt | tt IN s /\ {a:real^N,w} SUBSET tt} = 1 \/
                 CARD {tt | tt IN s /\ {a:real^N,w} SUBSET tt} = 2` THEN
    UNDISCH_TAC `CARD {tt | tt IN s /\ {b:real^N,w} SUBSET tt} = 1 \/
                 CARD {tt | tt IN s /\ {b:real^N,w} SUBSET tt} = 2` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `{a:real^N,w}`; `{a:real^N,b,w}`]
    MOI_FSA_CARD2_OTHER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ta:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `{b:real^N,w}`; `{a:real^N,b,w}`]
    MOI_FSA_CARD2_OTHER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC
   `!u:real^N. ~(u = w) /\ {w,u} IN moi_fsa_edges s
               ==> CARD {tt | tt IN s /\ {w,u} SUBSET tt} = 2` THENL
   [(* interior apex *)
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `a:real^N`; `b:real^N`; `w:real^N`; `ta:real^N->bool`;
                   `tb:real^N->bool`] MOI_FSA_CASE_C1_COMB) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSA_CASE_C1 THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                          `w:real^N`; `ta:real^N->bool`; `tb:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* boundary apex *)
  FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN `CARD {tt | tt IN s /\ {w:real^N,u} SUBSET tt} = 1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `{w:real^N,u}`] MOI_FSA_SURF_SUB_NTRI) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(CARD {tt | tt IN s /\ {w:real^N,u} SUBSET tt} = 2)` THEN
    MESON_TAC[ARITH_RULE `!n. 1 <= n /\ n <= 2 /\ ~(n = 2) ==> n = 1`];
    ALL_TAC] THEN
  ABBREV_TAC `sa = moi_fsa_dcomp (s DELETE {a:real^N,b,w}) ta` THEN
  ABBREV_TAC `sb = (s DELETE {a:real^N,b,w}) DIFF sa` THEN
  SUBGOAL_THEN `?ws:real^N. ~(ws IN UNIONS s)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_FRESH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `w:real^N`; `ta:real^N->bool`;
                 `tb:real^N->bool`; `u:real^N`; `sa:(real^N->bool)->bool`;
                 `sb:(real^N->bool)->bool`] MOI_FSA_CASE_C2_COMB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sa SUBSET s DELETE {a:real^N,b,w} /\
                sb SUBSET s DELETE {a:real^N,b,w}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sa UNION sb = s DELETE {a:real^N,b,w}` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSA_CASE_C2 THEN
  MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                        `w:real^N`; `ta:real^N->bool`; `tb:real^N->bool`;
                        `u:real^N`; `sa:(real^N->bool)->bool`;
                        `sb:(real^N->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_CARD_LT THEN
  EXISTS_TAC `{a:real^N,b,w}` THEN ASM_REWRITE_TAC[]);;

let MOI_FSA_DISK_PIECE = prove
 (`!d s:(real^N->bool)->bool.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_good d s
        ==> moi_fsa_disk (moi_fsa_poly s) (moi_fsa_poly (moi_fsa_bd s))`,
  GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND; MEASURE]
    (ISPEC `CARD:((real^N->bool)->bool)->num` WF_MEASURE)) THEN
  X_GEN_TAC `s:(real^N->bool)->bool` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_good]) THEN
  SUBGOAL_THEN
   `?e0:real^N->bool. e0 HAS_SIZE 2 /\ (?t. t IN s /\ e0 SUBSET t) /\
                      CARD {t | t IN s /\ e0 SUBSET t} = 1`
  MP_TAC THENL
   [UNDISCH_TAC `~(moi_fsa_bd (s:(real^N->bool)->bool) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; moi_fsa_bd; IN_ELIM_THM;
                moi_fsa_edges] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC))) THEN
  UNDISCH_TAC `(e0:real^N->bool) HAS_SIZE 2` THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `e0:real^N->bool`)) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FSA_GOOD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t0:real^N->bool`; `a:real^N`; `b:real^N`] MOI_SCF_THIRD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN UNDISCH_TAC `{a:real^N,b} SUBSET t0` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `t0:real^N->bool`)) THEN
  MATCH_MP_TAC MOI_FSA_DISK_STEP THEN
  MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                        `w:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `y:(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. The closed case: a closed connected surface with chi = 2 minus one    *)
(* triangle is a good piece; two disks with a common boundary form a       *)
(* PL 2-sphere.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FSA_CLOSED_GOOD = prove
 (`!d (a:A) b c.
        moi_fsa_surf d /\ moi_fsa_dconn d /\ {a,b,c} IN d /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        CARD(UNIONS d) + CARD d = CARD(moi_fsa_edges d) + 2
        ==> moi_fsa_good d (d DELETE {a,b,c}) /\
            moi_fsa_bd (d DELETE {a,b,c}) = {{a,b},{a,c},{b,c}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_surf]) THEN
  ABBREV_TAC `s = (d:(A->bool)->bool) DELETE {a,b,c}` THEN
  SUBGOAL_THEN `(s:(A->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (moi_fsa_edges (d:(A->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN ASM_MESON_TAC[HAS_SIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (UNIONS d:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  (* the edges of the removed triangle and their other triangles *)
  SUBGOAL_THEN
   `!e:A->bool. e HAS_SIZE 2 /\ e SUBSET {a,b,c}
        ==> e IN moi_fsa_edges d /\
            ?u. u IN s /\ e SUBSET u /\
                {tt | tt IN s /\ e SUBSET tt} = {u}`
  (LABEL_TAC "OTHER") THENL
   [X_GEN_TAC `e:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:A->bool) IN moi_fsa_edges d` ASSUME_TAC THENL
     [REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `{a:A,b,c}` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`d:(A->bool)->bool`; `{a:A,b,c}`; `e:A->bool`]
      MOI_FSA_OTHER_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u:A->bool` THEN
    SUBGOAL_THEN `(u:A->bool) IN s` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[MOI_FSA_NTRI_DELETE] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_PAIR_DELETE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:A->bool. e IN moi_fsa_edges s <=> e IN moi_fsa_edges d`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:A->bool` THEN EQ_TAC THENL
     [ASM_MESON_TAC[MOI_FSA_EDGES_MONO; SUBSET]; ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `(e:A->bool) SUBSET {a,b,c}` THENL
     [SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` ASSUME_TAC THENL
       [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges d` THEN
        SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
        ALL_TAC] THEN
      REMOVE_THEN "OTHER" (MP_TAC o SPEC `e:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges d` THEN
      REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:A->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
      REWRITE_TAC[IN_DELETE] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_edges s = moi_fsa_edges (d:(A->bool)->bool)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the boundary *)
  SUBGOAL_THEN `moi_fsa_bd s = {{a:A,b},{a,c},{b,c}}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:A`; `b:A`; `c:A`] MOI_FSA_EDGES_OF_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:A->bool` THEN
    REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(e:A->bool) IN moi_fsa_edges d` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      DISCH_TAC THEN UNDISCH_TAC `~((e:A->bool) IN moi_fsa_edges d)` THEN
      REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `{a:A,b,c}` THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` ASSUME_TAC THENL
     [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges d` THEN
      SIMP_TAC[moi_fsa_edges; IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(e:A->bool) SUBSET {a,b,c}` THEN ASM_REWRITE_TAC[] THENL
     [REMOVE_THEN "OTHER" (MP_TAC o SPEC `e:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[CARD_SING];
      EXPAND_TAC "s" THEN REWRITE_TAC[MOI_FSA_NTRI_DELETE] THEN
      SUBGOAL_THEN `~({a:A,b,c} IN {tt | tt IN d /\ e SUBSET tt})`
       (fun th -> REWRITE_TAC[MATCH_MP (SET_RULE
          `!s (t:A->bool). ~(t IN s) ==> s DELETE t = s`) th]) THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* local connectivity *)
  SUBGOAL_THEN `!x:A. moi_fsa_lconn s x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN {a,b,c}` THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC MOI_FSA_CYC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`d:(A->bool)->bool`; `s:(A->bool)->bool`; `x:A`]
        MOI_FSA_LCONN_LOCAL) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "s" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
        REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
        X_GEN_TAC `u:A->bool` THEN ASM_CASES_TAC `u = {a:A,b,c}` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:A,b} HAS_SIZE 2 /\ {a:A,c} HAS_SIZE 2 /\ {b:A,c} HAS_SIZE 2 /\
                {a:A,b} SUBSET {a,b,c} /\ {a:A,c} SUBSET {a,b,c} /\
                {b:A,c} SUBSET {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_PAIR_SIZE] THEN SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "OTHER" (fun th ->
    MP_TAC(SPEC `{a:A,b}` th) THEN MP_TAC(SPEC `{a:A,c}` th) THEN
    MP_TAC(SPEC `{b:A,c}` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ubc:A->bool` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `uac:A->bool` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `uab:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(a:A) IN uab /\ (b:A) IN uab /\ (a:A) IN uac /\ (c:A) IN uac /\
                (b:A) IN ubc /\ (c:A) IN ubc`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`{a:A,b} SUBSET uab`; `{a:A,c} SUBSET uac`;
                           `{b:A,c} SUBSET ubc`] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_dconn (s:(A->bool)->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(uab:A->bool) IN moi_fsa_dcomp s uab /\
                  (uac:A->bool) IN moi_fsa_dcomp s uab /\
                  (ubc:A->bool) IN moi_fsa_dcomp s uab`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s:(A->bool)->bool`; `uab:A->bool`] MOI_FSA_DCOMP) THEN
      MP_TAC(ISPECL [`s:(A->bool)->bool`; `a:A`; `uab:A->bool`]
        MOI_FSA_LCONN_DCOMP) THEN
      MP_TAC(ISPECL [`s:(A->bool)->bool`; `b:A`; `uab:A->bool`]
        MOI_FSA_LCONN_DCOMP) THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `ubc:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `uac:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN MATCH_MP_TAC MOI_FSA_DCONN_DELETE THEN
    EXISTS_TAC `uab:A->bool` THEN
    SUBGOAL_THEN `(uab:A->bool) IN d /\ ~(uab = {a,b,c})` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(uab:A->bool) IN s` THEN EXPAND_TAC "s" THEN
      SIMP_TAC[IN_DELETE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:A->bool`; `e:A->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(n:A->bool) IN s` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:A`; `b:A`; `c:A`; `e:A->bool`] MOI_FSA_TRI_EDGE_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `n:A->bool = uab` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `{tt | tt IN s /\ {a:A,b} SUBSET tt} = {uab}` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING];
      SUBGOAL_THEN `n:A->bool = uac` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `{tt | tt IN s /\ {a:A,c} SUBSET tt} = {uac}` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING];
      SUBGOAL_THEN `n:A->bool = ubc` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `{tt | tt IN s /\ {b:A,c} SUBSET tt} = {ubc}` THEN
      DISCH_THEN(MP_TAC o SPEC `n:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS s = UNIONS (d:(A->bool)->bool)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS] THEN EQ_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `u = {a:A,b,c}` THENL
     [UNDISCH_TAC `(x:A) IN u` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THENL
       [EXISTS_TAC `uab:A->bool`; EXISTS_TAC `uab:A->bool`;
        EXISTS_TAC `uac:A->bool`] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
      ASM_REWRITE_TAC[IN_DELETE]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_good] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `uab:A->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[NOT_INSERT_EMPTY];
    MP_TAC(ISPECL [`{a:A,b,c}`; `d:(A->bool)->bool`] CARD_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(CARD(d:(A->bool)->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `{a:A,b,c}` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `CARD(UNIONS d:A->bool) + CARD d = CARD(moi_fsa_edges d) + 2` THEN
      ARITH_TAC]]);;

let MOI_FSA_RF_TETRA = prove
 (`!(a:real^M) b c v.
        ~affine_dependent {v,a,b,c} /\
        ~(v = a) /\ ~(v = b) /\ ~(v = c) /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> relative_frontier(convex hull {v,a,b,c}) =
            convex hull {a,b,c} UNION
            UNIONS {segment[v,x] | x IN relative_frontier(convex hull {a,b,c})} /\
            convex hull {a,b,c} INTER
            UNIONS {segment[v,x] | x IN relative_frontier(convex hull {a,b,c})} =
            relative_frontier(convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~collinear{a:real^M,b,c}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~affine_dependent {v:real^M,a,b,c}` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  SUBGOAL_THEN
   `UNIONS {segment[v,x] | x IN segment[a,b] UNION segment[b,c] UNION
                                segment[c,a]} =
    convex hull {v:real^M,a,b} UNION convex hull {v,b,c} UNION
    convex hull {v,c,a}`
  SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    ONCE_REWRITE_TAC[SET_RULE `{v:real^M,x,y} = v INSERT {x,y}`] THEN
    REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS; NOT_INSERT_EMPTY] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t:real^M->bool. s SUBSET {v,a,b,c} /\ t SUBSET {v,a,b,c}
        ==> convex hull s INTER convex hull t = convex hull (s INTER t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_HULL_INTER THEN
    UNDISCH_TAC `~affine_dependent {v:real^M,a,b,c}` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON; POLYHEDRON_CONVEX_HULL;
             FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_SIMP_TAC[FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    SUBGOAL_THEN
     `{v:real^M,a,b,c} DELETE v = {a,b,c} /\
      {v:real^M,a,b,c} DELETE a = {v,b,c} /\
      {v:real^M,a,b,c} DELETE b = {v,c,a} /\
      {v:real^M,a,b,c} DELETE c = {v,a,b}`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; RIGHT_OR_DISTRIB; EXISTS_OR_THM;
                UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^M` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[UNION_OVER_INTER] THEN
    SUBGOAL_THEN
     `{a:real^M,b,c} SUBSET {v,a,b,c} /\ {v:real^M,a,b} SUBSET {v,a,b,c} /\
      {v:real^M,b,c} SUBSET {v,a,b,c} /\ {v:real^M,c,a} SUBSET {v,a,b,c}`
    STRIP_ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `{a:real^M,b,c} INTER {v,a,b} = {a,b} /\
      {a:real^M,b,c} INTER {v,b,c} = {b,c} /\
      {a:real^M,b,c} INTER {v,c,a} = {c,a}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL]]);;

let MOI_FSA_EMB = prove
 (`linear (\x:real^2. pastecart x (vec 0:real^1)) /\
   (!x y:real^2. pastecart x (vec 0:real^1) = pastecart y (vec 0) ==> x = y) /\
   (!x:real^2. fstcart(pastecart x (vec 0:real^1)) = x) /\
   (!x:real^2. sndcart(pastecart x (vec 0:real^1)) = vec 0)`,
  REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID;
              VECTOR_MUL_RZERO; PASTECART_INJ; FSTCART_PASTECART;
              SNDCART_PASTECART]);;

let MOI_FSA_SPHERE_MODEL = prove
 (`!k1:real^2->bool.
        &2 simplex k1
        ==> ?K:real^(2,1)finite_sum->bool F0 v0.
              &3 simplex K /\ &2 simplex F0 /\
              pl_homeomorphism (F0,k1)
                (fstcart,(\x:real^2. pastecart x (vec 0:real^1))) /\
              IMAGE fstcart (relative_frontier F0) = relative_frontier k1 /\
              ~(v0 IN relative_frontier F0) /\
              (!x y. x IN relative_frontier F0 /\ y IN relative_frontier F0 /\
                     y IN segment[v0,x] ==> y = x) /\
              relative_frontier K =
              F0 UNION UNIONS {segment[v0,x] | x IN relative_frontier F0} /\
              F0 INTER UNIONS {segment[v0,x] | x IN relative_frontier F0} =
              relative_frontier F0`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_FSA_EMB THEN
  ABBREV_TAC `E = \x:real^2. pastecart x (vec 0:real^1)` THEN
  SUBGOAL_THEN `!x:real^2. E x = pastecart x (vec 0:real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C1:real^2->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(C1:real^2->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^2` (X_CHOOSE_THEN `p1:real^2`
    (X_CHOOSE_THEN `p2:real^2` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `k1:real^2->bool`)) THEN
  SUBGOAL_THEN `!x y:real^2. (E:real^2->real^(2,1)finite_sum) x = E y ==> x = y`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. fstcart((E:real^2->real^(2,1)finite_sum) x) = x /\
                           sndcart(E x) = vec 0`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear (E:real^2->real^(2,1)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `!x:real^2. (E:real^2->real^(2,1)finite_sum) x =
                           pastecart x (vec 0:real^1)`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `!x y:real^2. pastecart x (vec 0:real^1) = pastecart y (vec 0)
                             ==> x = y`)) THEN
  ABBREV_TAC `v0 = pastecart (vec 0:real^2) (vec 1:real^1)` THEN
  SUBGOAL_THEN `&2 simplex (IMAGE (E:real^2->real^(2,1)finite_sum) k1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`E:real^2->real^(2,1)finite_sum`; `k1:real^2->bool`; `&2:int`]
      SIMPLEX_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (IMAGE (E:real^2->real^(2,1)finite_sum) k1) =
                IMAGE E (relative_frontier k1)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^(2,1)finite_sum.
                  y IN affine hull (IMAGE (E:real^2->real^(2,1)finite_sum) k1)
                  ==> sndcart y = vec 0`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((v0:real^(2,1)finite_sum) IN
      affine hull (IMAGE (E:real^2->real^(2,1)finite_sum) k1))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `!y:real^(2,1)finite_sum.
        y IN affine hull (IMAGE (E:real^2->real^(2,1)finite_sum) k1)
        ==> sndcart y = vec 0` THEN
    DISCH_THEN(MP_TAC o SPEC `v0:real^(2,1)finite_sum`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "v0" THEN
    REWRITE_TAC[SNDCART_PASTECART; VEC_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {(E:real^2->real^(2,1)finite_sum) p0, E p1, E p2} =
                IMAGE E k1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`E:real^2->real^(2,1)finite_sum`; `{p0:real^2,p1,p2}`]
      CONVEX_HULL_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(2,1)finite_sum.
                  z IN relative_frontier (IMAGE (E:real^2->real^(2,1)finite_sum) k1)
                  ==> sndcart z = vec 0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {v0:real^(2,1)finite_sum, E(p0:real^2), E p1, E p2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{(E:real^2->real^(2,1)finite_sum) p0, E p1, E p2} =
                    IMAGE E {p0,p1,p2}` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
      MP_TAC(ISPECL [`E:real^2->real^(2,1)finite_sum`; `{p0:real^2,p1,p2}`]
        AFFINE_DEPENDENT_LINEAR_IMAGE_EQ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[GSYM AFFINE_HULL_CONVEX_HULL] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v0:real^(2,1)finite_sum = E(p0:real^2)) /\ ~(v0 = E p1) /\
                ~(v0 = E p2) /\ ~(E p0 = E p1) /\ ~(E p0 = E p2) /\
                ~(E p1 = E p2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `sndcart:real^(2,1)finite_sum->real^1`);
      DISCH_THEN(MP_TAC o AP_TERM `sndcart:real^(2,1)finite_sum->real^1`);
      DISCH_THEN(MP_TAC o AP_TERM `sndcart:real^(2,1)finite_sum->real^1`);
      ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "v0" THEN
    REWRITE_TAC[SNDCART_PASTECART; VEC_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `!x y:real^2. (E:real^2->real^(2,1)finite_sum) x = E y
                             ==> x = y`)) THEN
  MP_TAC(ISPECL [`(E:real^2->real^(2,1)finite_sum) p0`; `(E:real^2->real^(2,1)finite_sum) p1`;
                 `(E:real^2->real^(2,1)finite_sum) p2`; `v0:real^(2,1)finite_sum`]
    MOI_FSA_RF_TETRA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {v0:real^(2,1)finite_sum, E(p0:real^2), E p1, E p2}`;
    `IMAGE (E:real^2->real^(2,1)finite_sum) k1`; `v0:real^(2,1)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplex] THEN
    EXISTS_TAC `{v0:real^(2,1)finite_sum, E(p0:real^2), E p1, E p2}` THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART;
               ASSUME `linear (E:real^2->real^(2,1)finite_sum)`] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `\x:real^(2,1)finite_sum. fstcart x + vec 0:real^2` THEN
      CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN REWRITE_TAC[LINEAR_FSTCART] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^2` (MP_TAC o
      AP_TERM `sndcart:real^(2,1)finite_sum->real^1` o CONJUNCT1)) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "v0" THEN
    REWRITE_TAC[SNDCART_PASTECART; VEC_EQ] THEN ARITH_TAC;
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    X_GEN_TAC `y0:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `sndcart:real^(2,1)finite_sum->real^1`) THEN
    ASM_REWRITE_TAC[SNDCART_ADD; SNDCART_CMUL] THEN EXPAND_TAC "v0" THEN
    REWRITE_TAC[SNDCART_PASTECART] THEN
    DISCH_THEN(MP_TAC o SPEC `1` o REWRITE_RULE[CART_EQ]) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `r = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&0 = (&1 - r) * &1 + r * &0` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

let MOI_FSA_PL_HOMEO_RESTRICT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g s'.
        pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ locally_polyhedral s'
        ==> pl_homeomorphism (s',IMAGE f s') (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_PL_HOMEO_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ASM SET_TAC[]];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_MESON_TAC[pl_homeomorphism]]);;

let MOI_FSA_TWO_DISKS = prove
 (`!(d1:real^N->bool) d2 j.
        moi_fsa_disk d1 j /\ moi_fsa_disk d2 j /\ d1 INTER d2 = j
        ==> ?K:real^(2,1)finite_sum->bool f g.
                &3 simplex K /\
                pl_homeomorphism (relative_frontier K,d1 UNION d2) (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_disk] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN `f1:real^2->real^N`
       (X_CHOOSE_THEN `g1:real^N->real^2` STRIP_ASSUME_TAC)))
    (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k2:real^2->bool` (X_CHOOSE_THEN `f2:real^2->real^N`
       (X_CHOOSE_THEN `g2:real^N->real^2` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  MP_TAC(ISPEC `k1:real^2->bool` MOI_FSA_SPHERE_MODEL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^(2,1)finite_sum->bool`
    (X_CHOOSE_THEN `F0:real^(2,1)finite_sum->bool`
      (X_CHOOSE_THEN `v0:real^(2,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `K:real^(2,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `C = UNIONS {segment[v0:real^(2,1)finite_sum,x] |
                          x IN relative_frontier F0}` THEN
  ABBREV_TAC `E = \x:real^2. pastecart x (vec 0:real^1)` THEN
  (* the first disk on the base face *)
  SUBGOAL_THEN `pl_homeomorphism (F0,d1)
                  ((f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2),(E:real^2->real^(2,1)finite_sum) o g1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`F0:real^(2,1)finite_sum->bool`; `k1:real^2->bool`;
                         `d1:real^N->bool`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2)) (relative_frontier F0) = j`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (relative_frontier (F0:real^(2,1)finite_sum->bool)) /\
                ~(relative_frontier F0 = {}) /\
                pl_polyhedron (relative_frontier (k2:real^2->bool)) /\
                ~(relative_frontier k2 = {}) /\
                ~(simplex_barycentre k2 IN relative_frontier k2) /\
                (!x y. x IN relative_frontier k2 /\ y IN relative_frontier k2 /\
                       y IN segment[simplex_barycentre k2,x] ==> y = x) /\
                UNIONS {segment[simplex_barycentre k2,x] | x |
                        x IN relative_frontier k2} = k2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`F0:real^(2,1)finite_sum->bool`; `&2:int`]
      MOI_CON_SIMPLEX_RF_FACTS) THEN
    MP_TAC(ISPECL [`k2:real^2->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (F0:real^(2,1)finite_sum->bool) /\
                compact (k1:real^2->bool) /\ compact (k2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (F0:real^(2,1)finite_sum->bool) SUBSET F0 /\
                relative_frontier (k2:real^2->bool) SUBSET k2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the boundary identification rf F0 -> j -> rf k2 *)
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier F0,j)
                  ((f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2),(E:real^2->real^(2,1)finite_sum) o g1)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE ((f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2))
                             (relative_frontier F0)`)) THEN
    MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`F0:real^(2,1)finite_sum->bool`; `d1:real^N->bool`] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (j,relative_frontier k2)
                  ((g2:real^N->real^2),(f2:real^2->real^N))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_homeomorphism (relative_frontier k2,
                                    IMAGE f2 (relative_frontier k2))
                    ((f2:real^2->real^N),(g2:real^N->real^2))` MP_TAC THENL
     [MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`k2:real^2->bool`; `d2:real^N->bool`] THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(ACCEPT_TAC o ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM])];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier F0,relative_frontier k2)
                  ((g2:real^N->real^2) o ((f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2)),
                   ((E:real^2->real^(2,1)finite_sum) o (g1:real^N->real^2)) o
                   (f2:real^2->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`relative_frontier (F0:real^(2,1)finite_sum->bool)`;
                         `j:real^N->bool`; `relative_frontier (k2:real^2->bool)`]
      PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* cone over the identification *)
  SUBGOAL_THEN
   `?h:real^(2,1)finite_sum->real^2 h'.
        pl_homeomorphism (C,k2) (h,h') /\
        !x. x IN relative_frontier F0
            ==> h x = (g2:real^N->real^2)((f1:real^2->real^N)(fstcart x))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`relative_frontier (F0:real^(2,1)finite_sum->bool)`;
                   `relative_frontier (k2:real^2->bool)`;
                   `v0:real^(2,1)finite_sum`; `simplex_barycentre (k2:real^2->bool)`;
                   `(g2:real^N->real^2) o ((f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2))`;
                   `((E:real^2->real^(2,1)finite_sum) o (g1:real^N->real^2)) o
                    (f2:real^2->real^N)`] MOI_CON_CONE_MAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (C,d2)
                  ((f2:real^2->real^N) o (h:real^(2,1)finite_sum->real^2),
                   (h':real^2->real^(2,1)finite_sum) o (g2:real^N->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`C:real^(2,1)finite_sum->bool`; `k2:real^2->bool`;
                         `d2:real^N->bool`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (C:real^(2,1)finite_sum->bool) /\ compact (d1:real^N->bool) /\
                compact (d2:real^N->bool)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`k2:real^2->bool`; `C:real^(2,1)finite_sum->bool`]
        MOI_PL2_PL_HOMEO_COMPACT) THEN
      MAP_EVERY EXISTS_TAC [`h':real^2->real^(2,1)finite_sum`;
                            `h:real^(2,1)finite_sum->real^2`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM] o
        check (fun th -> concl th = `pl_homeomorphism
          (C:real^(2,1)finite_sum->bool,k2:real^2->bool)
          (h:real^(2,1)finite_sum->real^2,h':real^2->real^(2,1)finite_sum)`));
      MATCH_MP_TAC(ISPECL [`k1:real^2->bool`; `d1:real^N->bool`]
        MOI_PL2_PL_HOMEO_COMPACT) THEN
      MAP_EVERY EXISTS_TAC [`f1:real^2->real^N`; `g1:real^N->real^2`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [`k2:real^2->bool`; `d2:real^N->bool`]
        MOI_PL2_PL_HOMEO_COMPACT) THEN
      MAP_EVERY EXISTS_TAC [`f2:real^2->real^N`; `g2:real^N->real^2`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`F0:real^(2,1)finite_sum->bool`; `C:real^(2,1)finite_sum->bool`;
                 `d1:real^N->bool`; `d2:real^N->bool`;
                 `(f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2)`;
                 `(E:real^2->real^(2,1)finite_sum) o (g1:real^N->real^2)`;
                 `(f2:real^2->real^N) o (h:real^(2,1)finite_sum->real^2)`;
                 `(h':real^2->real^(2,1)finite_sum) o (g2:real^N->real^2)`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    X_GEN_TAC `x:real^(2,1)finite_sum` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ISPECL [`k2:real^2->bool`; `d2:real^N->bool`]
      MOI_PL2_PL_HOMEO_RINV) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f1:real^2->real^N)(fstcart (x:real^(2,1)finite_sum)) IN j`
    MP_TAC THENL
     [UNDISCH_TAC `IMAGE ((f1:real^2->real^N) o (fstcart:real^(2,1)finite_sum->real^2))
                         (relative_frontier F0) = j` THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
      ASM SET_TAC[]];
    MESON_TAC[]]);;

let MOI_FSA_TRI_NOT_ALL = prove
 (`!u (a:A) b c.
        u HAS_SIZE 3 /\ ~(u = {a,b,c}) /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> ~(a IN u /\ b IN u /\ c IN u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(u = {a:A,b,c})` THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOI_FSA_EDGE_HULL_SUB = prove
 (`!s tri (a:real^N) b c.
        tri = {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        (!u. u IN s ==> u HAS_SIZE 3 /\ ~(u = tri)) /\
        {a,b} IN moi_fsa_edges s
        ==> convex hull {a,b} SUBSET UNIONS {convex hull (u INTER tri) | u IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `tri:real^N->bool`)) THEN
  UNDISCH_TAC `{a:real^N,b} IN moi_fsa_edges s` THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `~((c:real^N) IN u)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^N->bool`; `a:real^N`; `b:real^N`; `c:real^N`]
      MOI_FSA_TRI_NOT_ALL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `{a:real^N,b} SUBSET u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u INTER {a:real^N,b,c} = {a,b}` ASSUME_TAC THENL
   [UNDISCH_TAC `{a:real^N,b} SUBSET u` THEN
    UNDISCH_TAC `~((c:real^N) IN u)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_TAC THEN EXISTS_TAC `convex hull {a:real^N,b}` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FSA_CLOSED_SPHERE = prove
 (`!d:(real^N->bool)->bool.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_dconn d /\ ~(d = {}) /\
        CARD(UNIONS d) + CARD d = CARD(moi_fsa_edges d) + 2
        ==> ?K:real^(2,1)finite_sum->bool f g.
                &3 simplex K /\
                pl_homeomorphism (relative_frontier K,moi_fsa_poly d) (f,g)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fsa_surf]) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `t:real^N->bool` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(t:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `c:real^N`]
    MOI_FSA_CLOSED_GOOD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = (d:(real^N->bool)->bool) DELETE {a,b,c}` THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FSA_DISK_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_FSA_POLY_INSERT; MOI_FSA_POLY_SING; GSYM SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `~collinear{a:real^N,b,c}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_GEOM_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `{a:real^N,b,c}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] UNION segment[a,c] UNION segment[b,c] =
                relative_frontier(convex hull {a,b,c})` SUBST1_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `convex hull {a:real^N,b,c}` MOI_FSA_DISK_TRI) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_PL2_SIMPLEX_2]; DISCH_TAC] THEN
  SUBGOAL_THEN `(s:(real^N->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,c} INSERT s = d` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC INSERT_DELETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN s ==> u HAS_SIZE 3 /\ ~(u = {a,b,c})`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{a:real^N,b} IN moi_fsa_edges s /\ {b:real^N,c} IN moi_fsa_edges s /\
    {c:real^N,a} IN moi_fsa_edges s`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{c:real^N,a} = {a,c}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_fsa_bd s = {{a:real^N,b},{a,c},{b,c}}` THEN
    REWRITE_TAC[EXTENSION; moi_fsa_bd; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `{a:real^N,b}` th) THEN
      MP_TAC(SPEC `{b:real^N,c}` th) THEN MP_TAC(SPEC `{a:real^N,c}` th)) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a:real^N,b,c} INTER moi_fsa_poly s =
    relative_frontier(convex hull {a,b,c})` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `{a:real^N,b,c}`] MOI_FSA_POLY_INTER_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; ASSUME `~collinear{a:real^N,b,c}`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`u:real^N->bool`; `a:real^N`; `b:real^N`; `c:real^N`]
        MOI_FSA_TRI_NOT_ALL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!x y z w:real^N->bool. w SUBSET y ==> w SUBSET x UNION y UNION z`) THEN
        MATCH_MP_TAC HULL_MONO THEN UNDISCH_TAC `~((a:real^N) IN u)` THEN SET_TAC[];
        MATCH_MP_TAC(SET_RULE
         `!x y z w:real^N->bool. w SUBSET z ==> w SUBSET x UNION y UNION z`) THEN
        MATCH_MP_TAC HULL_MONO THEN UNDISCH_TAC `~((b:real^N) IN u)` THEN SET_TAC[];
        MATCH_MP_TAC(SET_RULE
         `!x y z w:real^N->bool. w SUBSET x ==> w SUBSET x UNION y UNION z`) THEN
        MATCH_MP_TAC HULL_MONO THEN UNDISCH_TAC `~((c:real^N) IN u)` THEN SET_TAC[]];
      REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC MOI_FSA_EDGE_HULL_SUB THENL
       [EXISTS_TAC `c:real^N`; EXISTS_TAC `a:real^N`; EXISTS_TAC `b:real^N`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(SET_TAC[]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {a:real^N,b,c}`; `moi_fsa_poly (s:(real^N->bool)->bool)`;
                 `relative_frontier(convex hull {a:real^N,b,c})`]
    MOI_FSA_TWO_DISKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^N,b,c} UNION moi_fsa_poly s = moi_fsa_poly d`
   (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `{a:real^N,b,c} INSERT s = d` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[MOI_FSA_POLY_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* 8. Links of a combinatorial 2-manifold: a finite complex whose          *)
(* polyhedron is homeomorphic to the frontier of a triangle is a cycle of  *)
(* edges (invariance of domain; no isolated or end vertices; chi = 0).     *)
(* ------------------------------------------------------------------------- *)

let MOI_FSA_LK_DIM = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g s.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ s IN L
        ==> aff_dim s <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool) /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&1 < aff_dim({}:real^N->bool)` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^N->real^N`; `affine hull (s:real^N->bool)`;
                 `affine hull (k:real^N->bool)`;
                 `relative_interior (s:real^N->bool)`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                OPEN_IN_RELATIVE_INTERIOR] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
      UNDISCH_TAC `&1 < aff_dim(s:real^N->bool)` THEN INT_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`] HULL_SUBSET) THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_FRONTIER_SUBSET) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`;
                 `IMAGE (g:real^N->real^N) (relative_interior s)`]
    RELATIVE_INTERIOR_MAXIMAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_FRONTIER_SUBSET) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (s:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `IMAGE (g:real^N->real^N) (UNIONS L) = relative_frontier k` THEN
  REWRITE_TAC[relative_frontier] THEN ASM SET_TAC[]);;

let MOI_FSA_LOCAL_STAR = prove
 (`!(L:(real^N->bool)->bool) u.
        FINITE L /\ (!s. s IN L ==> compact s)
        ==> ?r. &0 < r /\
                !y. y IN UNIONS L /\ dist(u,y) < r
                    ==> ?s. s IN L /\ u IN s /\ y IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS {s | s IN L /\ ~((u:real^N) IN s)}`; `u:real^N`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; COMPACT_IMP_CLOSED];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(u:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `dist(u:real^N,y) < r` THEN REAL_ARITH_TAC]);;

let MOI_FSA_RF_TWO_POINTS = prove
 (`!k:real^N->bool.
        &2 simplex k
        ==> ?a b. ~(a = b) /\ a IN relative_frontier k /\
                  b IN relative_frontier k`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(C:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~collinear{a:real^N,b,c}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; IN_UNION; ENDS_IN_SEGMENT]);;

let MOI_FSA_EDGE_SEG = prove
 (`!(L:(real^N->bool)->bool) u e.
        simplicial_complex L /\ {u} IN L /\ e IN L /\ aff_dim e = &1 /\
        u IN e
        ==> ?x. ~(x = u) /\ e = segment[u,x] /\ {x} IN L`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `&1 simplex (e:real^N->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `n:int` o C MATCH_MP
      (ASSUME `(e:real^N->bool) IN L`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(C:real^N->bool)):int = &1 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(u:real^N) extreme_point_of segment[p,q]` MP_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `{u:real^N} = {u} INTER e` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `e:real^N->bool`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p:real^N} IN L /\ {q:real^N} IN L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL;
                    EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN STRIP_TAC THENL
   [EXISTS_TAC `q:real^N`; EXISTS_TAC `p:real^N`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `u:real^N`)) THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REWRITE_TAC[INSERT_AC] THEN
  ASM_MESON_TAC[]);;

let MOI_FSA_LK_STAR_U = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u s.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L /\
        s IN L /\ u IN s
        ==> s = {u} \/ aff_dim s = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `s:real^N->bool`] MOI_FSA_LK_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= aff_dim(s:real^N->bool)` MP_TAC THENL
   [REWRITE_TAC[AFF_DIM_POS_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; INT_ARITH `&0 <= x:int /\ x <= &1 <=> x = &0 \/ x = &1`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `(u:real^N) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let MOI_FSA_LK_CONNECTED = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g.
        &2 simplex k /\ homeomorphism (relative_frontier k,UNIONS L) (f,g)
        ==> connected (UNIONS L) /\
            !p. p IN UNIONS L ==> connected (UNIONS L DELETE p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ bounded k /\ aff_dim k = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE;
                  POLYTOPE_IMP_BOUNDED; AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `UNIONS L:real^N->bool`)) THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `UNIONS L DELETE (p:real^N) =
                IMAGE (f:real^N->real^N) (relative_frontier k DELETE g p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DELETE; IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN
    ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^1)`; `(g:real^N->real^N) p`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_CONNECTEDNESS) THEN
  REWRITE_TAC[CONNECTED_UNIV]);;

let MOI_FSA_LK_EDGE = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L
        ==> ?e. e IN L /\ aff_dim e = &1 /\ u IN e`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN L /\ u IN s ==> s = {u}` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                   `s:real^N->bool`] MOI_FSA_LK_STAR_U) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N`] MOI_FSA_LOCAL_STAR) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FSA_LK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `{u:real^N}`) THEN
  SUBGOAL_THEN `(u:real^N) IN UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `ball(u:real^N,r)` THEN
      REWRITE_TAC[OPEN_BALL] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_BALL] THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DIST_REFL]; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `s = {u:real^N}` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `{u:real^N}` THEN
      REWRITE_TAC[CLOSED_SING] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_FSA_RF_TWO_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(f:real^N->real^N) a = u /\ f b = u` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~(a:real^N = b)` THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_FSA_SEG_DIST = prove
 (`!u x:real^N t. &0 <= t ==> dist(u,(&1 - t) % u + t % x) = t * dist(u,x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
  REWRITE_TAC[VECTOR_ARITH `u - ((&1 - t) % u + t % x):real^N = t % (u - x)`] THEN
  ASM_SIMP_TAC[NORM_MUL; real_abs]);;

let MOI_FSA_LK_NOT1 = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u e0.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L /\
        e0 IN L /\ aff_dim e0 = &1 /\ u IN e0 /\
        (!e. e IN L /\ aff_dim e = &1 /\ u IN e ==> e = e0)
        ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N`; `e0:real^N->bool`]
    MOI_FSA_EDGE_SEG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN L /\ u IN s ==> s SUBSET segment[u,x]`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                   `s:real^N->bool`] MOI_FSA_LK_STAR_U) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT];
      SUBGOAL_THEN `s:real^N->bool = e0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SUBSET_REFL]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N`] MOI_FSA_LOCAL_STAR) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < dist(u:real^N,x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `rho = min r (dist(u:real^N,x)) / &2` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < r /\ rho < dist(u:real^N,x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN UNDISCH_TAC `&0 < r` THEN
    UNDISCH_TAC `&0 < dist(u:real^N,x)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = (&1 - rho / dist(u,x)) % u + (rho / dist(u:real^N,x)) % x` THEN
  SUBGOAL_THEN `&0 <= rho / dist(u:real^N,x) /\ rho / dist(u,x) <= &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `rho < dist(u:real^N,x)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) IN segment[u,x] /\ dist(u,m) = rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `rho / dist(u:real^N,x)` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MOI_FSA_SEG_DIST] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN segment[u,x] /\ dist(u,y) = rho ==> y = m`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    UNDISCH_TAC `dist(u:real^N,y) = rho` THEN ASM_SIMP_TAC[MOI_FSA_SEG_DIST] THEN
    DISCH_TAC THEN EXPAND_TAC "m" THEN
    SUBGOAL_THEN `t = rho / dist(u:real^N,x)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) IN UNIONS L /\ (x:real^N) IN UNIONS L`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THEN
    EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FSA_LK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`(UNIONS L DELETE (m:real^N)) INTER ball(u,rho)`;
    `(UNIONS L DELETE (m:real^N)) INTER ((:real^N) DIFF cball(u,rho))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[GSYM closed; CLOSED_CBALL];
    REWRITE_TAC[SUBSET; IN_UNION; IN_INTER; IN_DELETE; IN_BALL; IN_CBALL;
                IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `dist(u:real^N,y) = rho` THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(y:real^N = m)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS L` THEN REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `y:real^N` (ASSUME `!y:real^N. y IN UNIONS L /\ dist(u,y) < r
                                  ==> ?s. s IN L /\ u IN s /\ y IN s`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN
        CONJ_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
                        ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[SUBSET];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DELETE; IN_BALL; IN_CBALL; IN_DIFF;
                IN_UNIV; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `u:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_DELETE; IN_BALL; DIST_REFL] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING];
      DISCH_THEN(ASSUME_TAC o SYM) THEN
      UNDISCH_TAC `dist(u:real^N,m) = rho` THEN ASM_REWRITE_TAC[DIST_REFL] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_DELETE; IN_CBALL; IN_DIFF; IN_UNIV] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    UNDISCH_TAC `dist(u:real^N,m) = rho` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_FSA_EDGE_VERTS = prove
 (`!(L:(real^N->bool)->bool) e.
        simplicial_complex L /\ e IN L /\ aff_dim e = &1
        ==> ?p q. ~(p = q) /\ e = segment[p,q] /\ {p} IN L /\ {q} IN L /\
                  {u | {u} IN L /\ u IN e} = {p,q}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `&1 simplex (e:real^N->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `n:int` o C MATCH_MP
      (ASSUME `(e:real^N->bool) IN L`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(C:real^N->bool)):int = &1 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `e = segment[p:real^N,q]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `{p:real^N} IN L /\ {q:real^N} IN L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL;
                    EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `{u:real^N} face_of e` MP_TAC THENL
     [SUBGOAL_THEN `{u:real^N} = {u} INTER e` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL;
                      EXTREME_POINT_OF_SEGMENT]];
    STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; ENDS_IN_SEGMENT]]);;

let MOI_FSA_LK_DEG_GE2 = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L
        ==> 2 <= CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {e:real^N->bool | e IN L /\ aff_dim e = &1 /\ u IN e}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `u:real^N`] MOI_FSA_LK_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    DISCH_TAC THEN
    MP_TAC(ISPEC `{e:real^N->bool | e IN L /\ aff_dim e = &1 /\ u IN e}`
      MOI_FSA_CARD_EQ_1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `e1:real^N->bool`) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                   `e0:real^N->bool`] MOI_FSA_LK_NOT1) THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) IN {e | e IN L /\ aff_dim e = &1 /\ u IN e} /\
                  (e0:real^N->bool) IN {e | e IN L /\ aff_dim e = &1 /\ u IN e}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]]);;

let MOI_FSA_LK_CHI = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g)
        ==> complex_euler L =
            &(CARD {u | {u} IN L}) - &(CARD {e | e IN L /\ aff_dim e = &1})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ ~(s = {})} =
    {s | s IN L /\ aff_dim s = &0} UNION {e | e IN L /\ aff_dim e = &1}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN L` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`]
      MOI_FSA_LK_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
     [CONV_TAC INT_REDUCE_CONV;
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {s:real^N->bool | s IN L /\ aff_dim s = &0}
             {e | e IN L /\ aff_dim e = &1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `sum {s:real^N->bool | s IN L /\ aff_dim s = &0}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {s:real^N->bool | s IN L /\ aff_dim s = &0} (\s. &1) /\
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1} (\s. -- &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ aff_dim s = &0} =
    IMAGE (\u:real^N. {u}) {u | {u} IN L}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N. {u}`; `{u:real^N | {u} IN L}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; GSYM real_sub]);;

let MOI_FSA_LK_HANDSHAKE = prove
 (`!L:(real^N->bool)->bool.
        simplicial_complex L
        ==> nsum {u | {u} IN L}
                 (\u. CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e}) =
            2 * CARD {e | e IN L /\ aff_dim e = &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(u:real^N) (e:real^N->bool). u IN e`; `{u:real^N | {u} IN L}`;
                 `{e:real^N->bool | e IN L /\ aff_dim e = &1}`]
    MOI_FSA_DOUBLE_COUNT) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `!u:real^N. {e | e IN {e:real^N->bool | e IN L /\ aff_dim e = &1} /\ u IN e} =
              {e | e IN L /\ aff_dim e = &1 /\ u IN e}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum {e:real^N->bool | e IN L /\ aff_dim e = &1} (\e. 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_CARD_PAIR THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT] THEN ARITH_TAC]);;

let MOI_FSA_LK_DEG2 = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\
        complex_euler L = &0 /\ {u} IN L
        ==> CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FSA_LK_CHI) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&0 = a - b <=> b = a`; REAL_OF_NUM_EQ] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_FSA_LK_HANDSHAKE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^N. v IN {u | {u} IN L}
                ==> 2 <= CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSA_LK_DEG_GE2 THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\v:real^N. 2`;
                 `\v:real^N. CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e}`;
                 `{u:real^N | {u} IN L}`] NSUM_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC);;

let MOI_FSA_SC_FACTS = prove
 (`!L:(real^N->bool)->bool.
        simplicial_complex L
        ==> FINITE L /\ (!s. s IN L ==> compact s /\ convex s)`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:int` o C MATCH_MP
    (ASSUME `(s:real^N->bool) IN L`)) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT; SIMPLEX_IMP_CONVEX]);;

let MOI_FSA_LK_EDGES_CONN = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g U.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\
        U SUBSET {e | e IN L /\ aff_dim e = &1} /\ ~(U = {}) /\
        (!e e'. e IN U /\ e' IN L /\ aff_dim e' = &1 /\ ~(e INTER e' = {})
                ==> e' IN U)
        ==> U = {e | e IN L /\ aff_dim e = &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool) /\
                (!s:real^N->bool. s IN L ==> compact s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_SC_FACTS]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `e1:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FSA_LK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS U:real^N->bool`;
    `UNIONS {e:real^N->bool | e IN L /\ aff_dim e = &1 /\ ~(e IN U)}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      SET_TAC[];
      X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      UNDISCH_TAC `(t:real^N->bool) IN U` THEN SET_TAC[]];
    MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; COMPACT_IMP_CLOSED];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?e:real^N->bool. e IN L /\ aff_dim e = &1 /\ y IN e`
    MP_TAC THENL
     [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                     `f:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`]
        MOI_FSA_LK_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN
      SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[INT_ARITH `&0 <= x:int /\ x <= &1 <=> x = &0 \/ x = &1`;
                  IMP_IMP] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN
        REWRITE_TAC[AFF_DIM_EQ_0] THEN
        DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
        UNDISCH_TAC `(y:real^N) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        MATCH_MP_TAC MOI_FSA_LK_EDGE THEN
        MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                              `g:real^N->real^N`] THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(e:real^N->bool) IN U` THENL
       [DISJ1_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC)
         ASSUME_TAC)) THEN
    UNDISCH_TAC `~((e':real^N->bool) IN U)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    UNDISCH_TAC `~(U:(real^N->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `e0:real^N->bool`) THEN
    SUBGOAL_THEN `(e0:real^N->bool) IN L /\ aff_dim e0 = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      UNDISCH_TAC `(e0:real^N->bool) IN U` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(e0:real^N->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
    CONJ_TAC THEN EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `~(e1:real^N->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `e1:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. Finite combinatorial 2-manifolds: vertex sets of simplices, pure      *)
(* dimension 2, every edge in exactly two triangles, triangles at a vertex *)
(* locally connected (from the vertex links being cycles).                  *)
(* ------------------------------------------------------------------------- *)

let moi_fsa_vs = new_definition
 `moi_fsa_vs (t:real^N->bool) = {x | x extreme_point_of t}`;;

let MOI_FSA_VS = prove
 (`!c t:real^N->bool.
        simplicial_complex c /\ t IN c
        ==> ~affine_dependent (moi_fsa_vs t) /\
            t = convex hull (moi_fsa_vs t) /\ FINITE (moi_fsa_vs t) /\
            &(CARD (moi_fsa_vs t)) = aff_dim t + &1 /\
            (!x. x IN moi_fsa_vs t ==> {x} IN c) /\
            (!s. s SUBSET moi_fsa_vs t
                 ==> convex hull s IN c /\ moi_fsa_vs (convex hull s) = s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:int` o C MATCH_MP
    (ASSUME `(t:real^N->bool) IN c`)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_fsa_vs (t:real^N->bool) = C` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_fsa_vs] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = n` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s SUBSET C
                ==> convex hull s IN c /\ moi_fsa_vs (convex hull s) = s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `t:real^N->bool`)) THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_fsa_vs] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      SUBGOAL_THEN `~affine_dependent (s:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[IN_ELIM_THM; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `(t:real^N->bool) = convex hull C` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N}` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[SING_SUBSET; CONVEX_HULL_SING] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_FSA_VS_MEM = prove
 (`!c t (x:real^N).
        simplicial_complex c /\ t IN c /\ {x} IN c
        ==> (x IN t <=> x IN moi_fsa_vs t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_vs; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; SIMP_TAC[extreme_point_of]] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{x:real^N} = {x} INTER t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]]);;

let MOI_FSA_CM_LINK = prove
 (`!c (v:real^N).
        FINITE c /\ combinatorial_manifold 2 c /\ {v} IN c
        ==> simplicial_complex c /\ simplicial_complex (simplicial_link c v) /\
            ?k:real^N->bool f:real^N->real^N g. &2 simplex k /\
                    homeomorphism (relative_frontier k,
                                   UNIONS (simplicial_link c v)) (f,g) /\
                    complex_euler (simplicial_link c v) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SCF_LINK_SC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[pl_sphere] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier (k:real^N->bool)`;
                 `&1 - (-- &1) pow 2`;
                 `simplicial_link c (v:real^N)`; `f:real^N->real^N`;
                 `g:real^N->real^N`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCF_LINK_SC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX_FRONTIER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED]];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MOI_FSA_CM_DIM = prove
 (`!c s:real^N->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ s IN c ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_MESON_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FSA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`; `s':real^N->bool`]
    MOI_FSA_LK_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s')) = aff_dim s' + &1` THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_FSA_CM_EDGE2 = prove
 (`!c e:real^N->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ e IN c /\ aff_dim e = &1
        ==> CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_MESON_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FSA_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `u:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FSA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `e:real^N->bool`)) THEN
  SUBGOAL_THEN `segment[v:real^N,u] = convex hull (v INSERT {u})` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `segment[v:real^N,u]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ segment[v,u] SUBSET t} =
    IMAGE (\s. convex hull (v INSERT s)) {s | s IN L /\ aff_dim s = &1 /\ u IN s}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
        MOI_SCF_LINK_OPP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `segment[v:real^N,u] SUBSET t` THEN
        MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s)) = aff_dim s + &1` THEN
        UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC;
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`;
                       `s:real^N->bool`] MOI_SCF_LINK_JOIN_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `segment[v:real^N,u] SUBSET t` THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[SING_SUBSET]];
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`;
                     `s:real^N->bool`] MOI_SCF_LINK_JOIN_SUBSET) THEN
      ASM_REWRITE_TAC[SING_SUBSET] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^N->bool. convex hull (v INSERT s)`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &1 /\ u IN s}`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`]
        MOI_SCF_LINK_JOIN_INJ) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN EXPAND_TAC "L" THEN
      ASM_MESON_TAC[simplicial_complex]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_FSA_LK_DEG2 THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FSA_CM_VTRI = prove
 (`!c v:real^N.
        FINITE c /\ combinatorial_manifold 2 c /\ {v} IN c
        ==> ?t. t IN c /\ aff_dim t = &2 /\ v IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FSA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN L /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` MOI_FSA_RF_TWO_POINTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN `(f:real^N->real^N) a IN UNIONS L` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `w:real^N`] MOI_FSA_LK_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `convex hull ((v:real^N) INSERT e)` THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let MOI_FSA_CM_LCONN = prove
 (`!c (v:real^N) Y.
        FINITE c /\ combinatorial_manifold 2 c /\ {v} IN c /\
        Y SUBSET {t | t IN c /\ aff_dim t = &2 /\ v IN t} /\ ~(Y = {}) /\
        (!t t' u. t IN Y /\ t' IN c /\ aff_dim t' = &2 /\ v IN t' /\
                  ~(u = v) /\ {u} IN c /\ u IN t /\ u IN t'
                  ==> t' IN Y)
        ==> Y = {t | t IN c /\ aff_dim t = &2 /\ v IN t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FSA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &1 /\
                                    convex hull (v INSERT s) IN Y}`]
    MOI_FSA_LK_EDGES_CONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `~(Y:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:real^N->bool`) THEN
      SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &2 /\ v IN t`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
        MOI_SCF_LINK_OPP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC;
        UNDISCH_TAC `(t:real^N->bool) IN Y` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?u:real^N. {u} IN L /\ u IN s1 /\ u IN s2` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s1 INTER s2:real^N->bool`]
          MOI_SCF_SC_VERTEX) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(s1 INTER s2:real^N->bool) face_of s1` MP_TAC THENL
           [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
          ASM_MESON_TAC[simplicial_complex];
          REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s1:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s2:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `~(u:real^N = v) /\ {u} IN c /\ u IN convex hull (v INSERT s1) /\
        u IN convex hull (v INSERT s2) /\
        aff_dim(convex hull ((v:real^N) INSERT s2)) = &2`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
          UNDISCH_TAC `{u:real^N} IN L` THEN EXPAND_TAC "L" THEN
          SIMP_TAC[simplicial_link; IN_ELIM_THM];
          MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `s2:real^N->bool` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT s1)`; `u:real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN
                {s | s IN L /\ aff_dim s = &1 /\ convex hull (v INSERT s) IN Y}`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10. The abstract surface of vertex sets of a finite combinatorial        *)
(* 2-manifold: its counts, Euler characteristic and dual connectivity.      *)
(* ------------------------------------------------------------------------- *)

let moi_fsa_abs = new_definition
 `moi_fsa_abs (c:(real^N->bool)->bool) =
    {moi_fsa_vs t | t IN c /\ aff_dim t = &2}`;;

let MOI_FSA_CM_SC = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c ==> simplicial_complex c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_LF_SC THEN
  ASM_MESON_TAC[combinatorial_manifold]);;

let MOI_FSA_VS_INJ = prove
 (`!c t t':real^N->bool.
        simplicial_complex c /\ t IN c /\ t' IN c /\
        moi_fsa_vs t = moi_fsa_vs t'
        ==> t = t'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t':real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let MOI_FSA_VS_SIZE = prove
 (`!c t:real^N->bool n.
        simplicial_complex c /\ t IN c /\ aff_dim t = &n
        ==> moi_fsa_vs t HAS_SIZE (n + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&(CARD(moi_fsa_vs (t:real^N->bool))):int = &n + &1` THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ]);;

let MOI_FSA_ABS_EDGE = prove
 (`!c e:real^N->bool.
        FINITE c /\ combinatorial_manifold 2 c
        ==> (e IN moi_fsa_edges (moi_fsa_abs c) <=>
             ?E. E IN c /\ aff_dim E = &1 /\ e = moi_fsa_vs E)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_edges; moi_fsa_abs; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t':real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `convex hull (e:real^N->bool)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    SUBGOAL_THEN `~affine_dependent (e:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    UNDISCH_TAC `(e:real^N->bool) HAS_SIZE 2` THEN SIMP_TAC[HAS_SIZE] THEN
    STRIP_TAC THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`; `1`]
        MOI_FSA_VS_SIZE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`] MOI_FSA_CM_EDGE2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?tr:real^N->bool. tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC
       `CARD {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ E SUBSET t} = 2` THEN
      SUBGOAL_THEN `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ E SUBSET t} = {}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `moi_fsa_vs (tr:real^N->bool)` THEN CONJ_TAC THENL
     [EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^N} IN c` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`; `x:real^N`]
      MOI_FSA_VS_MEM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(E:real^N->bool) SUBSET tr` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[extreme_point_of; moi_fsa_vs;
      IN_ELIM_THM]);;

let MOI_FSA_ABS_IMAGE = prove
 (`!c:(real^N->bool)->bool.
        moi_fsa_abs c = IMAGE moi_fsa_vs {t | t IN c /\ aff_dim t = &2}`,
  REWRITE_TAC[moi_fsa_abs; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  MESON_TAC[]);;

let MOI_FSA_ABS_SUB = prove
 (`!c (e:real^N->bool) tr.
        simplicial_complex c /\ e IN c /\ tr IN c
        ==> (moi_fsa_vs e SUBSET moi_fsa_vs tr <=> e SUBSET tr)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_VS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `convex hull (moi_fsa_vs (e:real^N->bool)) SUBSET
                  convex hull (moi_fsa_vs tr)` MP_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`; `x:real^N`]
      MOI_FSA_VS_MEM) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN moi_fsa_vs e` THEN
    SIMP_TAC[moi_fsa_vs; IN_ELIM_THM; extreme_point_of]]);;

let MOI_FSA_ABS_NTRI = prove
 (`!c e:real^N->bool.
        FINITE c /\ combinatorial_manifold 2 c /\
        e IN moi_fsa_edges (moi_fsa_abs c)
        ==> CARD {t | t IN moi_fsa_abs c /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_ABS_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `{t | t IN moi_fsa_abs c /\ moi_fsa_vs E SUBSET t} =
    IMAGE moi_fsa_vs {tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr}`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tr:real^N->bool`
        STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`;
                     `tr:real^N->bool`] MOI_FSA_ABS_SUB) THEN
      ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`;
                       `tr:real^N->bool`] MOI_FSA_ABS_SUB) THEN
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fsa_vs:(real^N->bool)->real^N->bool`;
                 `{tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr}`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_FSA_CM_EDGE2 THEN ASM_REWRITE_TAC[]);;

let MOI_FSA_ABS_SURF = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c ==> moi_fsa_surf (moi_fsa_abs c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_surf] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MOI_FSA_ABS_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `2`]
      MOI_FSA_VS_SIZE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FSA_ABS_NTRI THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `{x:real^N} IN c` THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_FSA_LCONN_EMPTY THEN
    REWRITE_TAC[MOI_FSA_ABS_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[moi_fsa_lconn] THEN X_GEN_TAC `y:(real^N->bool)->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!tr:real^N->bool. tr IN c ==> ((x:real^N) IN tr <=> x IN moi_fsa_vs tr)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_VS_MEM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`;
                 `{tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\
                                     moi_fsa_vs tr IN y}`] MOI_FSA_CM_LCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `tr:real^N->bool` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `y SUBSET {t | t IN moi_fsa_abs c /\ (x:real^N) IN t}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `~(y:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t0:real^N->bool`) THEN
      SUBGOAL_THEN `(t0:real^N->bool) IN moi_fsa_abs c` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_FSA_ABS_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t1:real^N->bool`; `t2:real^N->bool`; `u:real^N`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fsa_lclosed (moi_fsa_abs c) (x:real^N) y` THEN
      REWRITE_TAC[moi_fsa_lclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`moi_fsa_vs (t1:real^N->bool)`; `u:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(u:real^N) IN moi_fsa_vs t1 /\ u IN moi_fsa_vs t2 /\
                    (x:real^N) IN moi_fsa_vs t2`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t1:real^N->bool`; `u:real^N`]
            MOI_FSA_VS_MEM);
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t2:real^N->bool`; `u:real^N`]
            MOI_FSA_VS_MEM);
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t2:real^N->bool`; `x:real^N`]
            MOI_FSA_VS_MEM)] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[MOI_FSA_ABS_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `t2:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_FSA_ABS_IMAGE; IN_IMAGE] THEN
  X_GEN_TAC `t':real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tr:real^N->bool`
    STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `t':real^N->bool`)) THEN
  UNDISCH_TAC `{tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\
                                  moi_fsa_vs tr IN y} =
               {t | t IN c /\ aff_dim t = &2 /\ x IN t}` THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `tr:real^N->bool`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_FSA_VS_HULL = prove
 (`!A:real^N->bool. ~affine_dependent A ==> moi_fsa_vs (convex hull A) = A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_vs; EXTENSION; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_FSA_ABS_GEOM = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c ==> moi_fsa_geom (moi_fsa_abs c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_geom; MOI_FSA_ABS_IMAGE; FORALL_IN_IMAGE;
              EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t':real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (s:real^N->bool) /\ ~affine_dependent (s':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (s:real^N->bool) IN c /\ convex hull (s':real^N->bool) IN c`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[]] THEN
  SUBGOAL_THEN `(convex hull s INTER convex hull s':real^N->bool) face_of convex hull s /\
                (convex hull s INTER convex hull s') face_of convex hull s'`
  MP_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `A:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `B:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `A:real^N->bool = B` ASSUME_TAC THENL
   [SUBGOAL_THEN `~affine_dependent (A:real^N->bool) /\ ~affine_dependent (B:real^N->bool)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPEC `A:real^N->bool` MOI_FSA_VS_HULL) THEN
    MP_TAC(ISPEC `B:real^N->bool` MOI_FSA_VS_HULL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `A:real^N->bool`)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let MOI_FSA_CM_PURE = prove
 (`!c s:real^N->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ ~(s = {})
        ==> ?t. t IN c /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_CM_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `&0 <= x:int /\ x <= &2 <=> x = &0 \/ x = &1 \/ x = &2`;
              IMP_IMP] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FSA_CM_VTRI) THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_CM_EDGE2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC
     `CARD {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ s SUBSET t} = 2` THEN
    SUBGOAL_THEN `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ s SUBSET t} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC];
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FSA_ABS_POLY = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c
        ==> moi_fsa_poly (moi_fsa_abs c) = UNIONS c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_poly; MOI_FSA_ABS_IMAGE] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `t:real^N->bool` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_CM_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM SET_TAC[]]]);;

let MOI_FSA_ABS_COUNTS = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c
        ==> UNIONS (moi_fsa_abs c) = {v | {v} IN c} /\
            CARD (moi_fsa_abs c) = CARD {t | t IN c /\ aff_dim t = &2} /\
            CARD (moi_fsa_edges (moi_fsa_abs c)) =
            CARD {e | e IN c /\ aff_dim e = &1}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[MOI_FSA_ABS_IMAGE; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FSA_CM_VTRI) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `x:real^N`]
        MOI_FSA_VS_MEM) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_VS_INJ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `moi_fsa_edges (moi_fsa_abs c) =
                  IMAGE moi_fsa_vs {e:real^N->bool | e IN c /\ aff_dim e = &1}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_FSA_ABS_EDGE] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[];
      MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_VS_INJ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]]);;


let MOI_FSA_CM_EULER = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c
        ==> complex_euler c =
            &(CARD {v | {v} IN c}) - &(CARD {e | e IN c /\ aff_dim e = &1}) +
            &(CARD {t | t IN c /\ aff_dim t = &2})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN c /\ ~(s = {})} =
    ({s | s IN c /\ aff_dim s = &0} UNION {e | e IN c /\ aff_dim e = &1}) UNION
    {t | t IN c /\ aff_dim t = &2}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN c` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_CM_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
     [CONV_TAC INT_REDUCE_CONV;
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {s:real^N->bool | s IN c /\ aff_dim s = &0}
             {e | e IN c /\ aff_dim e = &1} /\
    DISJOINT ({s:real^N->bool | s IN c /\ aff_dim s = &0} UNION
              {e | e IN c /\ aff_dim e = &1})
             {t | t IN c /\ aff_dim t = &2}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_RESTRICT; FINITE_UNION] THEN
  SUBGOAL_THEN
   `sum {s:real^N->bool | s IN c /\ aff_dim s = &0}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {s:real^N->bool | s IN c /\ aff_dim s = &0} (\s. &1) /\
    sum {e:real^N->bool | e IN c /\ aff_dim e = &1}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {e:real^N->bool | e IN c /\ aff_dim e = &1} (\s. -- &1) /\
    sum {t:real^N->bool | t IN c /\ aff_dim t = &2}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {t:real^N->bool | t IN c /\ aff_dim t = &2} (\s. &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN c /\ aff_dim s = &0} =
    IMAGE (\u:real^N. {u}) {u | {u} IN c}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN c}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N. {u}`; `{u:real^N | {u} IN c}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; GSYM real_sub]);;

let MOI_FSA_POLY_COMPACT = prove
 (`!s:(real^N->bool)->bool.
        FINITE s /\ (!t. t IN s ==> FINITE t) ==> compact (moi_fsa_poly s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_poly; SIMPLE_IMAGE] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
  MATCH_MP_TAC FINITE_IMP_COMPACT THEN ASM_SIMP_TAC[]);;

let MOI_FSA_POLY_MEET_NE = prove
 (`!d y:(real^N->bool)->bool.
        (!t. t IN d ==> ~(t = {})) /\ y SUBSET d /\ ~(y = {})
        ==> ~(moi_fsa_poly y INTER moi_fsa_poly d = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(y:(real^N->bool)->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:real^N->bool`) THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real^N`) THEN
  SUBGOAL_THEN `(u:real^N) IN convex hull t` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `u:real^N` THEN
  REWRITE_TAC[moi_fsa_poly; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  CONJ_TAC THEN EXISTS_TAC `convex hull t:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real^N->bool` THEN ASM SET_TAC[]);;

let MOI_FSA_GEOM_MEET = prove
 (`!d y t1 t2 (x:real^N).
        moi_fsa_surf d /\ moi_fsa_geom d /\ y SUBSET d /\
        moi_fsa_dclosed d y /\ t1 IN y /\ t2 IN d /\
        x IN convex hull t1 /\ x IN convex hull t2
        ==> t2 IN y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t1:real^N->bool) IN d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull t1 INTER convex hull t2:real^N->bool =
                convex hull (t1 INTER t2)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_geom (d:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_fsa_geom] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `t1:real^N->bool`; EXISTS_TAC `t2:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w IN t1 /\ w IN t2` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `t1 INTER t2:real^N->bool = {}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `convex hull t1 INTER convex hull t2:real^N->bool =
                 convex hull (t1 INTER t2)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_lconn d (w:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fsa_surf]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t1:real^N->bool`]
    MOI_FSA_LCONN_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `t1:real^N->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:(real^N->bool)->bool` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_FSA_GEOM_DCONN = prove
 (`!d:(real^N->bool)->bool.
        moi_fsa_surf d /\ moi_fsa_geom d /\ connected (moi_fsa_poly d)
        ==> moi_fsa_dconn d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSA_DCONN_ALT] THEN
  X_GEN_TAC `y:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (d:(real^N->bool)->bool) /\
                (!t:real^N->bool. t IN d ==> FINITE t) /\
                (!t:real^N->bool. t IN d ==> ~(t = {}))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_surf (d:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_fsa_surf] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!t:real^N->bool. t HAS_SIZE 3 ==> FINITE t /\ ~(t = {})`
      (fun th -> ASM_MESON_TAC[th]) THEN
    GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `CARD({}:real^N->bool) = 3` THEN
    REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `connected (moi_fsa_poly (d:(real^N->bool)->bool))` THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`moi_fsa_poly (y:(real^N->bool)->bool)`;
                        `moi_fsa_poly ((d:(real^N->bool)->bool) DIFF y)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FSA_POLY_COMPACT THEN
    ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FSA_POLY_COMPACT THEN
    ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF];
    REWRITE_TAC[GSYM MOI_FSA_POLY_UNION] THEN
    SUBGOAL_THEN `(y:(real^N->bool)->bool) UNION (d DIFF y) = d`
     (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[moi_fsa_poly; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `k1:real^N->bool` (CONJUNCTS_THEN2
         (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `k2:real^N->bool` (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
        (K ALL_TAC))) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `y:(real^N->bool)->bool`;
                   `t1:real^N->bool`; `t2:real^N->bool`; `x:real^N`]
      MOI_FSA_GEOM_MEET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(t2:real^N->bool) IN d DIFF y` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_FSA_POLY_MEET_NE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSA_POLY_MEET_NE THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

let MOI_FSA_ABS_DCONN = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c)
        ==> moi_fsa_dconn (moi_fsa_abs c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_GEOM_DCONN THEN
  ASM_SIMP_TAC[MOI_FSA_ABS_SURF; MOI_FSA_ABS_GEOM; MOI_FSA_ABS_POLY]);;

(* ------------------------------------------------------------------------- *)
(* 11. The main theorem.  The abstraction of a finite connected nonempty    *)
(* combinatorial 2-manifold is a closed dual-connected geometric surface,   *)
(* so V + F <= E + 2 (counting); equality gives a PL 2-sphere (closed case, *)
(* transferred into real^N when dimindex(:N) >= 3; in lower dimension a     *)
(* 2-sphere cannot embed, by invariance of domain); conversely a PL 2-sphere *)
(* has Euler characteristic 2 (PL invariance of chi).                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FSA_CHI_ARITH = prove
 (`!x v e f:num P.
        x = &v - &e + &f /\ v + f <= e + 2 /\ (v + f = e + 2 ==> P) /\
        (P ==> x = &2)
        ==> x <= &2 /\ (x = &2 <=> P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x <= &2 /\ (x = &2 <=> v + f = e + 2)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&v - &e + &f <= &2 <=> &v + &f <= &e + &2`;
                REAL_ARITH `&v - &e + &f = &2 <=> &v + &f = &e + &2`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_EQ];
    ASM_MESON_TAC[]]);;

let MOI_FSA_NO_SPHERE_LOWDIM = prove
 (`!K:real^(2,1)finite_sum->bool (s:real^N->bool) f g.
        &3 simplex K /\ homeomorphism (relative_frontier K,s) (f,g) /\
        ~(s = {}) /\ dimindex(:N) <= 2
        ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(relative_frontier K:real^(2,1)finite_sum->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (relative_frontier K:real^(2,1)finite_sum->bool,
                               s:real^N->bool)
                              (f:real^(2,1)finite_sum->real^N,
                               g:real^N->real^(2,1)finite_sum)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (s:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (s:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^(2,1)finite_sum->real^N`;
                   `K:real^(2,1)finite_sum->bool`;
                   `relative_frontier K:real^(2,1)finite_sum->bool`;
                   `(:real^N)`] INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET_GEN) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; AFFINE_UNIV; OPEN_IN_REFL; SUBTOPOLOGY_UNIV;
                    GSYM OPEN_IN] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      REWRITE_TAC[AFF_DIM_UNIV] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
      REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOPEN) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN DISCH_TAC THEN
  UNDISCH_TAC `compact (s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[NOT_BOUNDED_UNIV]);;

let MOI_FSA_SPHERE_IFF = prove
 (`!d:(real^N->bool)->bool s.
        moi_fsa_surf d /\ moi_fsa_geom d /\ moi_fsa_dconn d /\ ~(d = {}) /\
        moi_fsa_poly d = s /\ ~(s = {})
        ==> CARD(UNIONS d) + CARD d <= CARD(moi_fsa_edges d) + 2 /\
            (CARD(UNIONS d) + CARD d = CARD(moi_fsa_edges d) + 2
             ==> pl_sphere 2 s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `d:(real^N->bool)->bool` MOI_FSA_COUNT) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `moi_fsa_surf (d:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_fsa_surf] THEN STRIP_TAC THEN ASM_SIMP_TAC[LE_REFL];
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    DISCH_TAC THEN
    MP_TAC(ISPEC `d:(real^N->bool)->bool` MOI_FSA_CLOSED_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^(2,1)finite_sum->bool`
      (X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^N`
        (X_CHOOSE_THEN `g:real^N->real^(2,1)finite_sum` STRIP_ASSUME_TAC))) THEN
    ASM_CASES_TAC `dimindex(:N) <= 2` THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      MP_TAC(ISPECL [`k:real^(2,1)finite_sum->bool`; `s:real^N->bool`;
                     `f:real^(2,1)finite_sum->real^N`;
                     `g:real^N->real^(2,1)finite_sum`]
        MOI_FSA_NO_SPHERE_LOWDIM) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[pl_homeomorphism];
      MP_TAC(ISPECL [`2`; `relative_frontier k:real^(2,1)finite_sum->bool`;
                     `s:real^N->bool`; `f:real^(2,1)finite_sum->real^N`;
                     `g:real^N->real^(2,1)finite_sum`]
        MOI_CMB_PL_SPHERE_TRANSFER) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1] THEN
      CONJ_TAC THENL
       [ASM_ARITH_TAC;
        MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]]]);;

let MOI_FSA_ABS_EULER = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c
        ==> complex_euler c =
            &(CARD (UNIONS (moi_fsa_abs c))) -
            &(CARD (moi_fsa_edges (moi_fsa_abs c))) +
            &(CARD (moi_fsa_abs c))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FSA_CM_EULER; MOI_FSA_ABS_COUNTS]);;

let MOI_FSA_SPHERE_EULER = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ pl_sphere 2 (UNIONS c)
        ==> complex_euler c = &2`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`relative_frontier (k:real^N->bool)`; `&1 - (-- &1) pow 3`;
                 `c:(real^N->bool)->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX_FRONTIER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED]];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SURFACE_EULER_SPHERE = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {})
     ==> complex_euler c <= &2 /\
         (complex_euler c = &2 <=> pl_sphere 2 (UNIONS c))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(moi_fsa_abs (c:(real^N->bool)->bool) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSA_ABS_POLY) THEN
    ASM_REWRITE_TAC[MOI_FSA_POLY_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fsa_abs (c:(real^N->bool)->bool)`; `UNIONS c:real^N->bool`]
    MOI_FSA_SPHERE_IFF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_ABS_SURF; MOI_FSA_ABS_GEOM; MOI_FSA_ABS_DCONN;
                 MOI_FSA_ABS_POLY];
    STRIP_TAC] THEN
  MATCH_MP_TAC MOI_FSA_CHI_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`CARD(UNIONS (moi_fsa_abs (c:(real^N->bool)->bool)))`;
    `CARD(moi_fsa_edges (moi_fsa_abs (c:(real^N->bool)->bool)))`;
    `CARD(moi_fsa_abs (c:(real^N->bool)->bool))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_ABS_EULER];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC MOI_FSA_SPHERE_EULER THEN ASM_REWRITE_TAC[]]);;

