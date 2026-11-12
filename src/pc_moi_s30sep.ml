(* ========================================================================= *)
(* pc_moi_s30sep: separation in simply connected open sets, Moise 30.1 and *)
(* 30.2 (GTM 47, printed pp.214-215).  Route: an open simply connected set  *)
(* in real^N is borsukian (SIMPLY_CONNECTED_IMP_BORSUKIAN) hence            *)
(* unicoherent (BORSUKIAN_IMP_UNICOHERENT); a connected unicoherent open    *)
(* set has the Phragmen-Brouwer property (two disjoint relatively closed    *)
(* sets neither of which separates two points do not separate them         *)
(* together), proved via the connected frontier of a complementary         *)
(* component; 30.2 follows by induction over a finite family of disjoint   *)
(* relatively closed sets.                                                  *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basic facts: relative complements, separation and components.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S30_OPEN_DIFF_CLOSED_IN = prove
 (`!x c:real^N->bool.
        open x /\ closed_in (subtopology euclidean x) c ==> open (x DIFF c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SET_RULE `(x:real^N->bool) DIFF (x INTER t) = x DIFF t`] THEN
  ASM_SIMP_TAC[OPEN_DIFF]);;

let MOI_S30_OPEN_SEP_NOT_CC = prove
 (`!u v w a b:real^N.
        open v /\ open w /\ u SUBSET v UNION w /\ DISJOINT v w /\
        a IN v /\ b IN w
        ==> ~connected_component u a b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[connected_component]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `connected(t:real^N->bool)` THEN REWRITE_TAC[connected] THEN
  MAP_EVERY EXISTS_TAC [`v:real^N->bool`; `w:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S30_SEPARATES_IN_SUBSET = prove
 (`!x c h k:real^N->bool.
        separates_in x c h k ==> h SUBSET x DIFF c /\ k SUBSET x DIFF c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separates_in] THEN STRIP_TAC THEN
  ASM SET_TAC[]);;

let MOI_S30_SEPARATES_IMP_NOT_CC = prove
 (`!x c h k a b:real^N.
        open x /\ separates_in x c h k /\ a IN h /\ b IN k
        ==> ~connected_component (x DIFF c) a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separates_in] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S30_OPEN_SEP_NOT_CC THEN
  MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_OPEN_TRANS];
    ASM_MESON_TAC[OPEN_IN_OPEN_TRANS];
    ASM SET_TAC[];
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S30_NOT_CC_IMP_SEPARATES = prove
 (`!x c h k a b:real^N.
        open x /\ closed_in (subtopology euclidean x) c /\
        connected h /\ connected k /\
        h SUBSET x DIFF c /\ k SUBSET x DIFF c /\ a IN h /\ b IN k /\
        ~connected_component (x DIFF c) a b
        ==> separates_in x c h k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (x DIFF c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S30_OPEN_DIFF_CLOSED_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `open (connected_component (x DIFF c) (a:real^N))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open ((x DIFF c) DIFF connected_component (x DIFF c) (a:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `x DIFF c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN
    REWRITE_TAC[OPEN_IN_REFL; CLOSED_IN_CONNECTED_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->bool) SUBSET connected_component (x DIFF c) a`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET connected_component (x DIFF c) b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (connected_component (x DIFF c) (a:real^N))
             (connected_component (x DIFF c) b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_COMPONENT_DISJOINT] THEN REWRITE_TAC[IN] THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[separates_in] THEN
  MAP_EVERY EXISTS_TAC
   [`connected_component (x DIFF c) (a:real^N)`;
    `(x DIFF c) DIFF connected_component (x DIFF c) (a:real^N)`] THEN
  MP_TAC(ISPECL [`x DIFF c:real^N->bool`; `a:real^N`]
    CONNECTED_COMPONENT_SUBSET) THEN
  DISCH_TAC THEN ASM_SIMP_TAC[OPEN_IN_OPEN_EQ] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Phragmen-Brouwer property of a connected unicoherent open set x.     *)
(* If p is the component of x DIFF (c UNION d) containing a, b lies outside *)
(* p, and q is the component of x DIFF closure p containing b, then         *)
(* x DIFF q is connected (COMPONENT_COMPLEMENT_CONNECTED), so by            *)
(* unicoherence the relative frontier x INTER closure q DIFF q is           *)
(* connected; it lies in c UNION d, hence in c or in d, and then q cut      *)
(* down to the complement of c (or d) is clopen there, separating b from a. *)
(* ------------------------------------------------------------------------- *)

let MOI_S30_COMPONENT_FACTS = prove
 (`!g a:real^N.
        open g /\ a IN g
        ==> open (connected_component g a) /\
            connected (connected_component g a) /\
            a IN connected_component g a /\
            connected_component g a SUBSET g /\
            g INTER closure (connected_component g a) SUBSET
            connected_component g a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT];
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
    REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
    MP_TAC(ISPECL [`g:real^N->bool`; `a:real^N`]
      CLOSED_IN_CONNECTED_COMPONENT) THEN
    REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN SET_TAC[]]);;

let MOI_S30_CONNECTED_SUBSET_DISJOINT_UNION = prove
 (`!x c d f:real^N->bool.
        closed_in (subtopology euclidean x) c /\
        closed_in (subtopology euclidean x) d /\
        DISJOINT c d /\ connected f /\ f SUBSET c UNION d
        ==> f SUBSET c \/ f SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
  REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `t:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S30_PB_FINISH = prove
 (`!x c p q:real^N->bool a b:real^N.
        open x /\ closed_in (subtopology euclidean x) c /\
        open p /\ a IN p /\ p SUBSET x DIFF c /\ p INTER closure q = {} /\
        b IN x DIFF c /\ open q /\ b IN q /\ q SUBSET x /\
        x INTER closure q DIFF q SUBSET c
        ==> ~connected_component (x DIFF c) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S30_OPEN_SEP_NOT_CC THEN
  MAP_EVERY EXISTS_TAC
   [`(x DIFF c) DIFF closure q:real^N->bool`; `q DIFF c:real^N->bool`] THEN
  MP_TAC(ISPEC `q:real^N->bool` CLOSURE_SUBSET) THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (x DIFF c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S30_OPEN_DIFF_CLOSED_IN]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CLOSURE];
    SUBGOAL_THEN `q DIFF c:real^N->bool = q INTER (x DIFF c)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[OPEN_INTER]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S30_PB_ABSTRACT = prove
 (`!x c d p q:real^N->bool a b:real^N.
        open x /\ unicoherent x /\
        closed_in (subtopology euclidean x) c /\
        closed_in (subtopology euclidean x) d /\ DISJOINT c d /\
        open p /\ a IN p /\ p SUBSET x DIFF (c UNION d) /\
        (x DIFF (c UNION d)) INTER closure p SUBSET p /\
        b IN x DIFF (c UNION d) /\
        open q /\ connected q /\ b IN q /\ q SUBSET x DIFF closure p /\
        (x DIFF closure p) INTER closure q SUBSET q /\
        connected (x DIFF q)
        ==> ~connected_component (x DIFF c) a b \/
            ~connected_component (x DIFF d) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p INTER closure q:real^N->bool = {}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN
    MP_TAC(ISPEC `p:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (x INTER closure q DIFF q:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `x INTER closure q DIFF q:real^N->bool =
      (x INTER closure q) INTER (x DIFF q)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `unicoherent (x:real^N->bool)` THEN
    REWRITE_TAC[unicoherent] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `q:real^N->bool` CLOSURE_SUBSET) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `q:real^N->bool` THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CLOSED_CLOSURE];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
      MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `x INTER closure q DIFF q SUBSET (c UNION d:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[IN_DIFF; IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN closure p` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x INTER closure q DIFF q SUBSET (c:real^N->bool) \/
    x INTER closure q DIFF q SUBSET (d:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S30_CONNECTED_SUBSET_DISJOINT_UNION THEN
    EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISJ1_TAC; DISJ2_TAC] THEN
  MATCH_MP_TAC MOI_S30_PB_FINISH THEN
  MAP_EVERY EXISTS_TAC [`p:real^N->bool`; `q:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S30_PB_POINTWISE = prove
 (`!x c d:real^N->bool a b:real^N.
        open x /\ connected x /\ unicoherent x /\
        closed_in (subtopology euclidean x) c /\
        closed_in (subtopology euclidean x) d /\ DISJOINT c d /\
        connected_component (x DIFF c) a b /\
        connected_component (x DIFF d) a b
        ==> connected_component (x DIFF (c UNION d)) a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(a:real^N) IN x DIFF (c UNION d) /\ (b:real^N) IN x DIFF (c UNION d)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x DIFF c:real^N->bool`; `a:real^N`; `b:real^N`]
      CONNECTED_COMPONENT_IN) THEN
    MP_TAC(ISPECL [`x DIFF d:real^N->bool`; `a:real^N`; `b:real^N`]
      CONNECTED_COMPONENT_IN) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (x DIFF (c UNION d):real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S30_OPEN_DIFF_CLOSED_IN THEN
    ASM_SIMP_TAC[CLOSED_IN_UNION];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `~connected_component (x DIFF c) (a:real^N) b \/
    ~connected_component (x DIFF d) a b`
  MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`x DIFF (c UNION d):real^N->bool`; `a:real^N`]
    MOI_S30_COMPONENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~((b:real^N) IN connected_component (x DIFF (c UNION d)) a)`
  MP_TAC THENL [ASM_REWRITE_TAC[IN]; ALL_TAC] THEN
  SPEC_TAC(`connected_component (x DIFF (c UNION d)) (a:real^N)`,
           `p:real^N->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^N) IN x DIFF closure p` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (x DIFF closure p:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CLOSURE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x DIFF closure p:real^N->bool`; `b:real^N`]
    MOI_S30_COMPONENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `connected (x DIFF connected_component (x DIFF closure p) (b:real^N))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
    EXISTS_TAC `x INTER closure p:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET;
      SET_RULE `(x:real^N->bool) DIFF (x INTER t) = x DIFF t`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `p:real^N->bool` THEN
      MP_TAC(ISPEC `p:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `b:real^N` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SPEC_TAC(`connected_component (x DIFF closure p) (b:real^N)`,
           `q:real^N->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S30_PB_ABSTRACT THEN
  MAP_EVERY EXISTS_TAC [`p:real^N->bool`; `q:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Moise 30.1 (p.214): in an open connected unicoherent x (in particular an *)
(* open simply connected x), if c UNION d separates h from k then c or d    *)
(* does.  The hypotheses closed_in h, closed_in k and DISJOINT h k of the    *)
(* book are not needed.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S30_SIMPLY_CONNECTED_UNICOHERENT = prove
 (`!x:real^N->bool. open x /\ simply_connected x ==> unicoherent x`,
  MESON_TAC[BORSUKIAN_IMP_UNICOHERENT; SIMPLY_CONNECTED_IMP_BORSUKIAN;
            OPEN_IMP_LOCALLY_PATH_CONNECTED]);;

let MOI_S30_SEPARATES_UNION_GEN = prove
 (`!x c d h k:real^N->bool.
        open x /\ connected x /\ unicoherent x /\
        closed_in (subtopology euclidean x) c /\
        closed_in (subtopology euclidean x) d /\
        connected h /\ connected k /\ ~(h = {}) /\ ~(k = {}) /\
        DISJOINT c d /\ DISJOINT c h /\ DISJOINT c k /\
        DISJOINT d h /\ DISJOINT d k /\
        separates_in x (c UNION d) h k
        ==> separates_in x c h k \/ separates_in x d h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?a:real^N. a IN h` (X_CHOOSE_TAC `a:real^N`) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^N. b IN k` (X_CHOOSE_TAC `b:real^N`) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S30_SEPARATES_IN_SUBSET) THEN
  ASM_CASES_TAC `separates_in x c (h:real^N->bool) k` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `separates_in x d (h:real^N->bool) k` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected_component (x DIFF c) (a:real^N) b` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    UNDISCH_TAC `~separates_in x c (h:real^N->bool) k` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S30_NOT_CC_IMP_SEPARATES THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component (x DIFF d) (a:real^N) b` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    UNDISCH_TAC `~separates_in x d (h:real^N->bool) k` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S30_NOT_CC_IMP_SEPARATES THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `c:real^N->bool`; `d:real^N->bool`;
                 `a:real^N`; `b:real^N`] MOI_S30_PB_POINTWISE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S30_SEPARATES_IMP_NOT_CC THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->bool`; `k:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S30_301_GEN = prove
 (`!x c d h k:real^N->bool.
        open x /\ simply_connected x /\
        closed_in (subtopology euclidean x) c /\
        closed_in (subtopology euclidean x) d /\
        connected h /\ connected k /\ ~(h = {}) /\ ~(k = {}) /\
        DISJOINT c d /\ DISJOINT c h /\ DISJOINT c k /\
        DISJOINT d h /\ DISJOINT d k /\
        separates_in x (c UNION d) h k
        ==> separates_in x c h k \/ separates_in x d h k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S30_SEPARATES_UNION_GEN THEN
  ASM_SIMP_TAC[MOI_S30_SIMPLY_CONNECTED_UNICOHERENT;
               SIMPLY_CONNECTED_IMP_CONNECTED]);;

let MOISE_301 = prove
 (`MOISE_301_STATEMENT`,
  REWRITE_TAC[MOISE_301_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S30_301_GEN THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Moise 30.2 (p.215): induction over a finite family of pairwise disjoint  *)
(* relatively closed sets, then the family of components of c.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S30_SEPARATES_IN_EMPTY = prove
 (`!x h k:real^N->bool.
        connected x /\ ~(h = {}) /\ ~(k = {}) ==> ~separates_in x {} h k`,
  REWRITE_TAC[separates_in; DIFF_EMPTY] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `connected (x:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN_EQ] THEN
  MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S30_FINITE_FAMILY = prove
 (`!x h k:real^N->bool.
        open x /\ simply_connected x /\
        connected h /\ connected k /\ ~(h = {}) /\ ~(k = {})
        ==> !ff. FINITE ff
                 ==> (!e. e IN ff
                          ==> closed_in (subtopology euclidean x) e /\
                              DISJOINT e h /\ DISJOINT e k) /\
                     (!e1 e2. e1 IN ff /\ e2 IN ff /\ ~(e1 = e2)
                              ==> DISJOINT e1 e2) /\
                     separates_in x (UNIONS ff) h k
                     ==> ?e. e IN ff /\ separates_in x e h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY] THEN
    MP_TAC(ISPECL [`x:real^N->bool`; `h:real^N->bool`; `k:real^N->bool`]
      MOI_S30_SEPARATES_IN_EMPTY) THEN
    ASM_SIMP_TAC[SIMPLY_CONNECTED_IMP_CONNECTED];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e0:real^N->bool`; `ff:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[UNIONS_INSERT; IN_INSERT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e IN ff
        ==> closed_in (subtopology euclidean x) e /\
            DISJOINT e h /\ DISJOINT e k`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e1 e2:real^N->bool. e1 IN ff /\ e2 IN ff /\ ~(e1 = e2)
        ==> DISJOINT e1 e2`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean x) (e0:real^N->bool) /\
    DISJOINT e0 h /\ DISJOINT e0 k`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean x) (UNIONS ff:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_UNIONS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN ff ==> DISJOINT e0 e` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (e0:real^N->bool) (UNIONS ff) /\
    DISJOINT (UNIONS ff) h /\ DISJOINT (UNIONS ff) k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!e. e IN ff ==> DISJOINT (a:real^N->bool) e)
        ==> DISJOINT a (UNIONS ff)`) THEN ASM_MESON_TAC[];
      MATCH_MP_TAC(SET_RULE
       `(!e. e IN ff ==> DISJOINT e (a:real^N->bool))
        ==> DISJOINT (UNIONS ff) a`) THEN ASM_MESON_TAC[];
      MATCH_MP_TAC(SET_RULE
       `(!e. e IN ff ==> DISJOINT e (a:real^N->bool))
        ==> DISJOINT (UNIONS ff) a`) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `e0:real^N->bool`; `UNIONS ff:real^N->bool`;
                 `h:real^N->bool`; `k:real^N->bool`] MOI_S30_301_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "ih" MP_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S30_302_GEN = prove
 (`!x c h k:real^N->bool.
        open x /\ simply_connected x /\
        closed_in (subtopology euclidean x) c /\
        connected h /\ connected k /\ ~(h = {}) /\ ~(k = {}) /\
        DISJOINT c h /\ DISJOINT c k /\
        FINITE (components c) /\ separates_in x c h k
        ==> ?d. d IN components c /\ separates_in x d h k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `h:real^N->bool`; `k:real^N->bool`]
    MOI_S30_FINITE_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `components(c:real^N->bool)`) THEN
  ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_TRANS THEN EXISTS_TAC `c:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT]]);;

let MOISE_302 = prove
 (`MOISE_302_STATEMENT`,
  REWRITE_TAC[MOISE_302_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S30_302_GEN THEN ASM_REWRITE_TAC[]);;

