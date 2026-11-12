(* ========================================================================= *)
(* pc_top_cover: covering maps of general topological spaces.               *)
(*                                                                           *)
(* General topology in the style of the HOL Light library: it depends only   *)
(* on the HOL Light library (metric.ml conventions: topspace, open_in,       *)
(* continuous_map, homeomorphic_map, path_in, homotopic_with) and on the     *)
(* definition simply_connected_space of poincare_statement.ml. Names mirror  *)
(* those of paths.ml with covering_space replaced by covering_map.           *)
(*                                                                           *)
(* Contents: covering maps and local homeomorphisms; the bridge to the       *)
(* Euclidean covering_space; unique lifting; homotopy and path lifting;      *)
(* monodromy; simply connected bases (connected covers are trivial, lifting  *)
(* criterion, sections); the characterizations of simply_connected_space;   *)
(* local homeomorphisms of compact Hausdorff spaces.                         *)
(*                                                                           *)
(* Definitions, basic properties, the Euclidean bridge.                      *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Covering maps: every point of Y has an open neighbourhood V whose        *)
(* preimage is a union of pairwise disjoint open sets, each mapped           *)
(* homeomorphically onto V (the general form of covering_space).            *)
(* ------------------------------------------------------------------------- *)

let covering_map = new_definition
 `covering_map (X:A topology,Y:B topology) (p:A->B) <=>
    continuous_map (X,Y) p /\ IMAGE p (topspace X) = topspace Y /\
    !y. y IN topspace Y
        ==> ?V. open_in Y V /\ y IN V /\
                ?vs. UNIONS vs = {x | x IN topspace X /\ p x IN V} /\
                     (!U. U IN vs ==> open_in X U) /\ pairwise DISJOINT vs /\
                     (!U. U IN vs
                          ==> homeomorphic_map (subtopology X U,subtopology Y V) p)`;;

let local_homeomorphism_map = new_definition
 `local_homeomorphism_map (X:A topology,Y:B topology) (p:A->B) <=>
    !x. x IN topspace X
        ==> ?U V. open_in X U /\ x IN U /\ open_in Y V /\
                  homeomorphic_map (subtopology X U,subtopology Y V) p`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties.                                                         *)
(* ------------------------------------------------------------------------- *)

let COVERING_MAP_IMP_CONTINUOUS = prove
 (`!X Y (p:A->B). covering_map (X,Y) p ==> continuous_map (X,Y) p`,
  SIMP_TAC[covering_map]);;

let COVERING_MAP_IMP_SURJECTIVE = prove
 (`!X Y (p:A->B). covering_map (X,Y) p ==> IMAGE p (topspace X) = topspace Y`,
  SIMP_TAC[covering_map]);;

let COVERING_MAP_LOCAL_HOMEOMORPHISM = prove
 (`!X Y (p:A->B). covering_map (X,Y) p ==> local_homeomorphism_map (X,Y) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[covering_map; local_homeomorphism_map] THEN
  STRIP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:A->B) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `vs:(A->bool)->bool` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(x:A) IN UNIONS vs` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; REWRITE_TAC[IN_UNIONS]] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `V:B->bool`] THEN ASM_SIMP_TAC[]);;

(* A local homeomorphism is an open map. *)

let TOPC_LOCAL_HOMEOMORPHISM_OPEN_MAP = prove
 (`!X Y (p:A->B). local_homeomorphism_map (X,Y) p ==> open_map (X,Y) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[local_homeomorphism_map; open_map] THEN
  DISCH_TAC THEN X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace X` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `V:B->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (p:A->B) (U INTER w)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `V:B->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_OPEN_MAP) THEN
    REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM SET_TAC[];
    SET_TAC[]]);;

let COVERING_MAP_OPEN_MAP = prove
 (`!X Y (p:A->B). covering_map (X,Y) p ==> open_map (X,Y) p`,
  MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM; TOPC_LOCAL_HOMEOMORPHISM_OPEN_MAP]);;

(* ------------------------------------------------------------------------- *)
(* The bridge: covering_map generalizes the Euclidean covering_space.        *)
(* ------------------------------------------------------------------------- *)

let TOPC_HOMEOMORPHIC_MAP_EUCLIDEAN = prove
 (`!(p:real^M->real^N) u v.
        homeomorphic_map (subtopology euclidean u,subtopology euclidean v) p <=>
        ?q. homeomorphism (u,v) (p,q)`,
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY]);;

let COVERING_MAP_EUCLIDEAN = prove
 (`!c (p:real^M->real^N) s.
        covering_map (subtopology euclidean c,subtopology euclidean s) p <=>
        covering_space(c,p) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[covering_map; covering_space; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
  ASM_CASES_TAC `IMAGE (p:real^M->real^N) c = s` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  SUBGOAL_THEN
   `!t u. open_in (subtopology euclidean s) t /\
          open_in (subtopology euclidean c) u
          ==> (homeomorphic_map
                 (subtopology (subtopology euclidean c) u,
                  subtopology (subtopology euclidean s) t) (p:real^M->real^N) <=>
               ?q. homeomorphism (u,t) (p,q))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPC_HOMEOMORPHIC_MAP_EUCLIDEAN] THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
    ASM_SIMP_TAC[SET_RULE `(u:real^M->bool) SUBSET c ==> c INTER u = u`;
                 SET_RULE `(t:real^N->bool) SUBSET s ==> s INTER t = t`];
    AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Unique lifting.                                                           *)
(* ========================================================================= *)

(* A homeomorphism of subspaces is injective on its domain. *)

let TOPC_HOMEOMORPHIC_MAP_INJ = prove
 (`!X Y (p:A->B) U V x x'.
        homeomorphic_map (subtopology X U,subtopology Y V) p /\
        U SUBSET topspace X /\ x IN U /\ x' IN U /\ p x = p x'
        ==> x = x'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic_map; TOPSPACE_SUBTOPOLOGY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `x':A`]) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]);;

(* Clopen argument: a nonempty subset of a connected space that is a        *)
(* neighbourhood of each of its points and whose complement is a            *)
(* neighbourhood of each of its points is the whole space.                  *)

let TOPC_CONNECTED_SPACE_CLOPEN = prove
 (`!Z (S:C->bool) z0.
        connected_space Z /\ S SUBSET topspace Z /\ z0 IN S /\
        (!z. z IN S ==> ?W. open_in Z W /\ z IN W /\ W SUBSET S) /\
        (!z. z IN topspace Z /\ ~(z IN S)
             ==> ?W. open_in Z W /\ z IN W /\ W SUBSET topspace Z DIFF S)
        ==> S = topspace Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `S:C->bool` o
    GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN]) THEN
  SUBGOAL_THEN `open_in Z (S:C->bool)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in Z (S:C->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[closed_in] THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Two points with the same image lie in sheets that coincide or are        *)
(* disjoint, the first one mapped injectively.                              *)

let TOPC_COVERING_MAP_TWO_SHEETS = prove
 (`!X Y (p:A->B) x1 x2.
        covering_map (X,Y) p /\ x1 IN topspace X /\ x2 IN topspace X /\
        p x1 = p x2
        ==> ?U1 U2. open_in X U1 /\ open_in X U2 /\ x1 IN U1 /\ x2 IN U2 /\
                    (U1 = U2 \/ DISJOINT U1 U2) /\
                    (!x x'. x IN U1 /\ x' IN U1 /\ p x = p x' ==> x = x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [covering_map]) THEN
  DISCH_THEN(MP_TAC o SPEC `(p:A->B) x1` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_MAP_IMP_SURJECTIVE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `vs:(A->bool)->bool` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(x1:A) IN UNIONS vs /\ (x2:A) IN UNIONS vs` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `U1:A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `U2:A->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`U1:A->bool`; `U2:A->bool`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
    DISCH_THEN(MP_TAC o SPECL [`U1:A->bool`; `U2:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_HOMEOMORPHIC_MAP_INJ THEN
    MAP_EVERY EXISTS_TAC
     [`X:A topology`; `Y:B topology`; `p:A->B`; `U1:A->bool`; `V:B->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET]]);;

(* Two lifts of the same map from a connected space that agree at one point *)
(* agree everywhere.                                                         *)

let COVERING_MAP_LIFT_UNIQUE = prove
 (`!X Y (p:A->B) Z (f1:C->A) f2 z0.
        covering_map (X,Y) p /\ connected_space Z /\
        continuous_map (Z,X) f1 /\ continuous_map (Z,X) f2 /\
        (!z. z IN topspace Z ==> p(f1 z) = p(f2 z)) /\
        z0 IN topspace Z /\ f1 z0 = f2 z0
        ==> !z. z IN topspace Z ==> f1 z = f2 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{z | z IN topspace Z /\ (f1:C->A) z = f2 z} = topspace Z`
  MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC TOPC_CONNECTED_SPACE_CLOPEN THEN
  EXISTS_TAC `z0:C` THEN ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET_RESTRICT] THEN
  SUBGOAL_THEN
   `!z. z IN topspace Z
        ==> ?U1 U2. open_in X U1 /\ open_in X U2 /\
                    (f1:C->A) z IN U1 /\ (f2:C->A) z IN U2 /\
                    (U1 = U2 \/ DISJOINT U1 U2) /\
                    (!x x'. x IN U1 /\ x' IN U1 /\ (p:A->B) x = p x' ==> x = x')`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:C` THEN DISCH_TAC THEN
    MATCH_MP_TAC TOPC_COVERING_MAP_TWO_SHEETS THEN
    EXISTS_TAC `Y:B topology` THEN ASM_SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `z:C` THEN REWRITE_TAC[IN_ELIM_THM] THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:C`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U1:A->bool`; `U2:A->bool`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `U1:A->bool = U2` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `{w | w IN topspace Z /\ (f1:C->A) w IN U2} INTER
                {w | w IN topspace Z /\ (f2:C->A) w IN U2}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `X:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `w:C` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:C`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U1:A->bool`; `U2:A->bool`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `DISJOINT (U1:A->bool) U2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC o check (is_disj o concl)) THENL
       [DISCH_TAC THEN UNDISCH_TAC `~((f1:C->A) z = f2 z)` THEN
        MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
          check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
        ASM_SIMP_TAC[] THEN ASM SET_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `{w | w IN topspace Z /\ (f1:C->A) w IN U1} INTER
                {w | w IN topspace Z /\ (f2:C->A) w IN U2}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `X:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_DIFF] THEN
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Homotopy lifting and path lifting.  For a covering map p,                *)
(* a homotopy h : [0,1] x Z -> Y and a lift f of h(0,.), a lift k of h with *)
(* k(0,.) = f exists for every topological space Z: first on [0,1] x N for  *)
(* a neighbourhood N of each point of Z (extension step plus a sup argument *)
(* on [0,1]), then globally by uniqueness of lifts and the pasting lemma.   *)
(* ========================================================================= *)

(* One extension step: a lift on [0,T] x N extends to [0,b] x N' when       *)
(* h maps [T,b] x M into an open set V with a sheet U over it.               *)

let TOPC_LIFT_EXTEND = prove
 (`!X Y (p:A->B) Z (h:real#C->B) (k:real#C->A) N M U V q t1 t2.
        continuous_map
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z,Y) h /\
        open_in Z N /\ open_in Z M /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &1 /\
        continuous_map
          (subtopology
            (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z)
            (real_interval[&0,t1] CROSS N),X) k /\
        (!t z. t IN real_interval[&0,t1] /\ z IN N ==> p(k(t,z)) = h(t,z)) /\
        open_in X U /\ open_in Y V /\
        homeomorphic_maps (subtopology X U,subtopology Y V) (p,q) /\
        (!t z. t IN real_interval[t1,t2] /\ z IN M ==> h(t,z) IN V)
        ==> open_in Z {z | z IN N INTER M /\ k(t1,z) IN U} /\
            continuous_map
              (subtopology
                (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z)
                (real_interval[&0,t2] CROSS {z | z IN N INTER M /\ k(t1,z) IN U}),X)
              (\w. if FST w <= t1 then k w else q(h w)) /\
            (!t z. t IN real_interval[&0,t2] /\ z IN N INTER M /\ k(t1,z) IN U
                   ==> p((\w. if FST w <= t1 then k w else q(h w)) (t,z)) = h(t,z)) /\
            (!t z. t IN real_interval[&0,t1]
                   ==> (\w. if FST w <= t1 then k w else q(h w)) (t,z) = k(t,z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(N:C->bool) SUBSET topspace Z /\ (M:C->bool) SUBSET topspace Z`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; IN_INTER]) THEN
  SUBGOAL_THEN `continuous_map (subtopology Z N,X) (\z:C. (k:real#C->A)(t1,z))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology
            (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                           (Z:C topology))
            (real_interval[&0,t1] CROSS (N:C->bool))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_PAIRED] THEN
      REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
        REWRITE_TAC[CONTINUOUS_MAP_ID]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      X_GEN_TAC `z:C` THEN STRIP_TAC THEN REWRITE_TAC[IN_CROSS] THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{z | z IN N INTER M /\ (k:real#C->A)(t1,z) IN U} =
      M INTER {z | z IN topspace(subtopology Z N) /\ (\z:C. k(t1,z)) z IN U}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `N:C->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `X:A topology` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN
      REWRITE_TAC[CONTINUOUS_MAP_FST];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO) o
        check (fun th -> can (term_match []
          `continuous_map (subtopology a b,X:A topology) (k:real#C->A)`)
          (concl th))) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS;
                  TOPSPACE_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      SIMP_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology Y (V:B->bool)` THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
        EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY;
                    FORALL_PAIR_THM; IN_INTER; IN_ELIM_THM; IN_CROSS] THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_CROSS;
                  IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `z:C`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
      SUBGOAL_THEN `h(t1,z):B = (p:A->B)((k:real#C->A)(t1,z))` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL];
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
          check (fun th -> can (term_match []
           `continuous_map (subtopology Z N,X:A topology)
                           (\z:C. (k:real#C->A)(t1,z))`) (concl th))) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]]];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:C`] THEN
    REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t <= t1` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
          check (fun th -> can (term_match []
            `continuous_map (prod_topology a b,Y:B topology) (h:real#C->B)`)
            (concl th))) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC]];
    SIMP_TAC[IN_REAL_INTERVAL]]);;

(* Around each point (t,z) of [0,1] x Z the homotopy maps a product of a    *)
(* time interval and an open set into an evenly covered open set.           *)

let TOPC_HOMOTOPY_BOX = prove
 (`!X Y (p:A->B) Z (h:real#C->B) t z.
     covering_map (X,Y) p /\
     continuous_map
       (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z,Y) h /\
     t IN real_interval[&0,&1] /\ z IN topspace Z
     ==> ?e M V vs. &0 < e /\ open_in Z M /\ z IN M /\ open_in Y V /\
                    UNIONS vs = {x | x IN topspace X /\ p x IN V} /\
                    (!U. U IN vs ==> open_in X U) /\
                    (!U. U IN vs
                         ==> homeomorphic_map (subtopology X U,subtopology Y V) p) /\
                    (!t' z'. t' IN real_interval[&0,&1] /\ abs(t' - t) < e /\
                             z' IN M
                             ==> h(t',z') IN V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real#C->B)(t,z) IN topspace Y` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map]) THEN
    ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(h:real#C->B)(t,z)` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [covering_map]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `vs:(A->bool)->bool` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL
   [`h:real#C->B`;
    `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (Z:C topology)`;
    `Y:B topology`; `V:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_IN_PROD_TOPOLOGY_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `z:C`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real->bool`; `M:C->bool`; `u':real->bool`] THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`e:real`; `M:C->bool`; `V:B->bool`; `vs:(A->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t':real`; `z':C`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET] o
    check (is_binary "SUBSET" o concl)) THEN
  DISCH_THEN(MP_TAC o SPEC `(t':real,z':C)`) THEN
  REWRITE_TAC[IN_CROSS; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[]);;

(* The local lift: on [0,1] x N for an open neighbourhood N of each point.  *)
(* S is the set of times r such that a lift exists on [0,r] x N for some N; *)
(* the extension step at its sup s shows that s = 1 belongs to S.           *)

let TOPC_LIFT_HOMOTOPY_LOCAL = prove
 (`!X Y (p:A->B) Z (h:real#C->B) f z.
     covering_map (X,Y) p /\
     continuous_map
       (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z,Y) h /\
     continuous_map (Z,X) f /\ (!z. z IN topspace Z ==> h(&0,z) = p(f z)) /\
     z IN topspace Z
     ==> ?N k. open_in Z N /\ z IN N /\
               continuous_map
                 (subtopology
                   (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z)
                   (real_interval[&0,&1] CROSS N),X) k /\
               (!z'. z' IN N ==> k(&0,z') = f z') /\
               (!t z'. t IN real_interval[&0,&1] /\ z' IN N
                       ==> p(k(t,z')) = h(t,z'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `S = {r | r IN real_interval[&0,&1] /\
             ?N (k:real#C->A).
               open_in Z N /\ z IN N /\
               continuous_map
                 (subtopology
                   (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                  (Z:C topology))
                   (real_interval[&0,r] CROSS N),X) k /\
               (!z'. z' IN N ==> k(&0,z') = (f:C->A) z') /\
               (!t z'. t IN real_interval[&0,r] /\ z' IN N
                       ==> (p:A->B)(k(t,z')) = (h:real#C->B)(t,z'))}` THEN
  SUBGOAL_THEN `&1 IN S` MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN `&0 IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MAP_EVERY EXISTS_TAC [`topspace Z:C->bool`; `(f:C->A) o (SND:real#C->C)`] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `Z:C topology` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND];
      REWRITE_TAC[REAL_ARITH `&0 <= t /\ t <= &0 <=> t = &0`] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN S ==> &0 <= r /\ r <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM; IN_REAL_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s = sup S` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s /\ s <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`; `Z:C topology`;
                 `h:real#C->B`; `s:real`; `z:C`] TOPC_HOMOTOPY_BOX) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`e:real`; `M:C->bool`; `V:B->bool`; `vs:(A->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?r. r IN S /\ s - e < r` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(s <= s - e)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_NOT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?N (k:real#C->A).
      open_in Z N /\ z IN N /\
      continuous_map
        (subtopology
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                         (Z:C topology))
          (real_interval[&0,r] CROSS N),X) k /\
      (!z'. z' IN N ==> k(&0,z') = (f:C->A) z') /\
      (!t z'. t IN real_interval[&0,r] /\ z' IN N
              ==> (p:A->B)(k(t,z')) = (h:real#C->B)(t,z'))`
  MP_TAC THENL
   [UNDISCH_TAC `(r:real) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`N:C->bool`; `k:real#C->A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= r /\ r <= &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real#C->A)(r,z) IN topspace X` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
      check (fun th -> can (term_match []
        `continuous_map (subtopology a b,X:A topology) (k:real#C->A)`)
        (concl th))) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_CROSS;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A->B)((k:real#C->A)(r,z)) IN V` ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:A->B)((k:real#C->A)(r,z)) = h(r,z)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t' z'. (&0 <= t' /\ t' <= &1) /\ abs(t' - s) < e /\ z' IN M
                 ==> (h:real#C->B)(t',z') IN V`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s - e < r` THEN UNDISCH_TAC `&0 < e` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> can (term_match []
        `!x. x IN S ==> x <= s`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r <= s` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real#C->A)(r,z) IN UNIONS vs` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; REWRITE_TAC[IN_UNIONS]] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?q. homeomorphic_maps (subtopology X U,subtopology Y V) ((p:A->B),q)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[HOMEOMORPHIC_MAP_MAPS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`; `Z:C topology`;
                 `h:real#C->B`; `k:real#C->A`; `N:C->bool`; `M:C->bool`;
                 `U:A->bool`; `V:B->bool`; `q:B->A`; `r:real`;
                 `min (&1) (s + e / &2)`] TOPC_LIFT_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `z':C`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t' z'. (&0 <= t' /\ t' <= &1) /\ abs(t' - s) < e /\ z' IN M
                 ==> (h:real#C->B)(t',z') IN V`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s - e < r` THEN UNDISCH_TAC `&0 < e` THEN
      UNDISCH_TAC `&0 <= r` THEN UNDISCH_TAC `r <= t` THEN
      UNDISCH_TAC `t <= min (&1) (s + e / &2)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `min (&1) (s + e / &2) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`{z | z IN N INTER M /\ (k:real#C->A)(r,z) IN U}`;
      `\w. if FST w <= r then (k:real#C->A) w else (q:B->A)((h:real#C->B) w)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
       `!t z. t IN real_interval[&0,min (&1) (s + e / &2)] /\ z IN N INTER M /\
              (k:real#C->A)(r,z) IN U
              ==> (p:A->B)(if t <= r then k(t,z)
                           else (q:B->A)((h:real#C->B)(t,z))) = h(t,z)`)
       (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `min (&1) (s + e / &2) = &1` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) (s + e / &2)` o
    check (fun th -> can (term_match [] `!x. x IN S ==> x <= s`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `s <= &1` THEN
  REAL_ARITH_TAC);;

let TOPC_SLICE_CONTINUOUS = prove
 (`!Z (X:A topology) (k:real#C->A) N z.
        continuous_map
          (subtopology
            (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z)
            (real_interval[&0,&1] CROSS N),X) k /\
        z IN N /\ N SUBSET topspace Z
        ==> continuous_map (subtopology euclideanreal (real_interval[&0,&1]),X)
                           (\t. k(t,z))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology
     (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                    (Z:C topology))
     (real_interval[&0,&1] CROSS (N:C->bool))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_PAIRED] THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CROSS;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID];
    ASM SET_TAC[];
    ASM_SIMP_TAC[]]);;

(* The homotopy lifting property of covering maps, for every space Z.       *)

let COVERING_MAP_LIFT_HOMOTOPY = prove
 (`!X Y (p:A->B) Z (h:real#C->B) f.
        covering_map (X,Y) p /\
        continuous_map
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z,Y) h /\
        continuous_map (Z,X) f /\
        (!z. z IN topspace Z ==> h(&0,z) = p(f z))
        ==> ?k. continuous_map
                  (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) Z,X) k /\
                (!z. z IN topspace Z ==> k(&0,z) = f z) /\
                (!t z. t IN real_interval[&0,&1] /\ z IN topspace Z
                       ==> p(k(t,z)) = h(t,z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`; `Z:C topology`;
                 `h:real#C->B`; `f:C->A`] TOPC_LIFT_HOMOTOPY_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`NN:C->C->bool`; `KK:C->real#C->A`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (Z:C topology)`;
    `X:A topology`; `KK:C->real#C->A`;
    `\z:C. real_interval[&0,&1] CROSS (NN:C->C->bool) z`; `topspace Z:C->bool`]
   PASTING_LEMMA_EXISTS) THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; UNIONS_GSPEC;
                  IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `z:C`] THEN STRIP_TAC THEN
      EXISTS_TAC `z:C` THEN ASM_SIMP_TAC[];
      X_GEN_TAC `i:C` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:C`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_IN_CROSS] THEN
      DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEANREAL; SUBSET_UNIV];
      MAP_EVERY X_GEN_TAC [`i:C`; `j:C`] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `w:C`] THEN
      REWRITE_TAC[IN_INTER; IN_CROSS] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:C`) THEN FIRST_ASSUM(MP_TAC o SPEC `j:C`) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                     `subtopology euclideanreal (real_interval[&0,&1])`;
                     `\t. (KK:C->real#C->A) i (t,w)`;
                     `\t. (KK:C->real#C->A) j (t,w)`;
                     `&0`] COVERING_MAP_LIFT_UNIQUE) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[CONNECTED_SPACE_SUBTOPOLOGY;
                     CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC TOPC_SLICE_CONTINUOUS THEN
          EXISTS_TAC `Z:C topology` THEN EXISTS_TAC `(NN:C->C->bool) i` THEN
          ASM_SIMP_TAC[OPEN_IN_SUBSET];
          MATCH_MP_TAC TOPC_SLICE_CONTINUOUS THEN
          EXISTS_TAC `Z:C topology` THEN EXISTS_TAC `(NN:C->C->bool) j` THEN
          ASM_SIMP_TAC[OPEN_IN_SUBSET];
          REPEAT STRIP_TAC THEN ASM_SIMP_TAC[IN_REAL_INTERVAL]];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real#C->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:real#C->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:C` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(&0,z):real#C`; `z:C`] o
      check (fun th -> can (term_match []
        `!x i. i IN (s:C->bool) /\ x IN (u:real#C->bool)
               ==> (g:real#C->A) x = (KK:C->real#C->A) i x`) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:C` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_CROSS; IN_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:C`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(t,z):real#C`; `z:C`] o
      check (fun th -> can (term_match []
        `!x i. i IN (s:C->bool) /\ x IN (u:real#C->bool)
               ==> (g:real#C->A) x = (KK:C->real#C->A) i x`) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:C` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_CROSS] THEN SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Path lifting: the homotopy lifting property for a one-point space.       *)

let COVERING_MAP_LIFT_PATH_STRONG = prove
 (`!X Y (p:A->B) g x.
        covering_map (X,Y) p /\ path_in Y g /\ x IN topspace X /\ p x = g(&0)
        ==> ?h. path_in X h /\ h(&0) = x /\
                !t. t IN real_interval[&0,&1] ==> p(h t) = g t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                 `subtopology euclideanreal {&0}`;
                 `\w:real#real. (g:real->B)(FST w)`; `\s:real. (x:A)`]
         COVERING_MAP_LIFT_HOMOTOPY) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST] THEN ASM_REWRITE_TAC[GSYM path_in];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real#real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t. (k:real#real->A)(t,&0)` THEN
  ASM_SIMP_TAC[IN_SING] THEN REWRITE_TAC[path_in] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                            (subtopology euclideanreal {&0})` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_SING]);;

(* ========================================================================= *)
(* Lifts of constant paths, monodromy, simply connected bases:               *)
(* a covering map from a path-connected space onto a simply connected space *)
(* is injective, hence a homeomorphism.                                      *)
(* ========================================================================= *)

(* Slices of a map on the unit square. *)

let TOPC_SQUARE_SLICES = prove
 (`!(top:A topology) (k:real#real->A) a.
        continuous_map
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                         (subtopology euclideanreal (real_interval[&0,&1])),top) k /\
        a IN real_interval[&0,&1]
        ==> continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                           (\s. k(s,a)) /\
            continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                           (\t. k(a,t))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                  (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]);;

let TOPC_CONNECTED_UNIT_INTERVAL = prove
 (`connected_space (subtopology euclideanreal (real_interval[&0,&1]))`,
  MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL_INTERVAL]);;

(* A lift of a constant path is constant. *)

let TOPC_LIFT_CONSTANT_PATH = prove
 (`!X Y (p:A->B) c y s0.
        covering_map (X,Y) p /\
        continuous_map (subtopology euclideanreal (real_interval[&0,&1]),X) c /\
        (!s. s IN real_interval[&0,&1] ==> p(c s) = y) /\
        s0 IN real_interval[&0,&1]
        ==> !s. s IN real_interval[&0,&1] ==> c s = c s0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                 `subtopology euclideanreal (real_interval[&0,&1])`;
                 `c:real->A`; `\s:real. (c:real->A) s0`; `s0:real`]
         COVERING_MAP_LIFT_UNIQUE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  TOPC_CONNECTED_UNIT_INTERVAL; CONTINUOUS_MAP_CONST] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [DISJ2_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
        check (fun th -> can (term_match []
          `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),X:A topology) c`)
          (concl th))) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
      ASM_SIMP_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Monodromy: lifts of paths homotopic with fixed endpoints, starting at the *)
(* same point, end at the same point.                                       *)

let COVERING_MAP_MONODROMY = prove
 (`!X Y (p:A->B) g1 g2 h1 h2.
        covering_map (X,Y) p /\
        homotopic_with (\r. r(&0) = g1(&0) /\ r(&1) = g1(&1))
          (subtopology euclideanreal (real_interval[&0,&1]),Y) g1 g2 /\
        path_in X h1 /\ path_in X h2 /\ h1(&0) = h2(&0) /\
        (!t. t IN real_interval[&0,&1] ==> p(h1 t) = g1 t /\ p(h2 t) = g2 t)
        ==> h1(&1) = h2(&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with; path_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `H:real#real->B` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                 `subtopology euclideanreal (real_interval[&0,&1])`;
                 `H:real#real->B`; `h1:real->A`] COVERING_MAP_LIFT_HOMOTOPY) THEN
  ASM_SIMP_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real#real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the two edges s |-> K(s,0), s |-> K(s,1) are constant *)
  SUBGOAL_THEN `(K:real#real->A)(&1,&0) = K(&0,&0) /\ K(&1,&1) = K(&0,&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                     `\s. (K:real#real->A)(s,&0)`; `(g1:real->B)(&0)`; `&0`]
             TOPC_LIFT_CONSTANT_PATH);
      MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                     `\s. (K:real#real->A)(s,&1)`; `(g1:real->B)(&1)`; `&0`]
             TOPC_LIFT_CONSTANT_PATH)] THEN
    ASM_SIMP_TAC[TOPC_SQUARE_SLICES] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* t |-> K(1,t) lifts g2 from h2(0), so it is h2 *)
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                 `subtopology euclideanreal (real_interval[&0,&1])`;
                 `\t. (K:real#real->A)(&1,t)`; `h2:real->A`; `&0`]
         COVERING_MAP_LIFT_UNIQUE) THEN
  ASM_SIMP_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; TOPC_CONNECTED_UNIT_INTERVAL;
               TOPC_SQUARE_SLICES] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_SIMP_TAC[]);;

(* A covering map from a path-connected space onto a simply connected      *)
(* space is injective (free loops: lift the null-homotopy of p o c).        *)

let COVERING_MAP_INJECTIVE = prove
 (`!X Y (p:A->B).
        covering_map (X,Y) p /\ path_connected_space X /\ simply_connected_space Y
        ==> !x x'. x IN topspace X /\ x' IN topspace X /\ p x = p x' ==> x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`] o
    GEN_REWRITE_RULE I [path_connected_space]) THEN
  ASM_REWRITE_TAC[path_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(p:A->B) o (c:real->A)`; `\t:real. (p:A->B) a`] o
    GEN_REWRITE_RULE I [simply_connected_space]) THEN
  REWRITE_TAC[o_THM; path_in] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `X:A topology` THEN
      ASM_SIMP_TAC[COVERING_MAP_IMP_CONTINUOUS];
      DISJ2_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_MAP_IMP_SURJECTIVE) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[homotopic_with; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#real->B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                 `subtopology euclideanreal (real_interval[&0,&1])`;
                 `H:real#real->B`; `c:real->A`] COVERING_MAP_LIFT_HOMOTOPY) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real#real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* at s = 1 the lift of the constant loop is constant *)
  SUBGOAL_THEN `(K:real#real->A)(&1,&1) = K(&1,&0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
      `\t. (K:real#real->A)(&1,t)`; `(p:A->B) a`; `&0`]
      TOPC_LIFT_CONSTANT_PATH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`X:A topology`; `K:real#real->A`; `&1`]
          TOPC_SQUARE_SLICES) THEN ASM_SIMP_TAC[];
        X_GEN_TAC `s:real` THEN DISCH_TAC THEN
        TRANS_TAC EQ_TRANS `(H:real#real->B)(&1,s)` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!t z. t IN real_interval[&0,&1] /\ z IN real_interval[&0,&1]
                   ==> (p:A->B)((K:real#real->A)(t,z)) = (H:real#real->B)(t,z)`)
            (concl th))) THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]];
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the two edges lift the same path and agree at s = 1 *)
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                 `subtopology euclideanreal (real_interval[&0,&1])`;
                 `\s. (K:real#real->A)(s,&0)`; `\s. (K:real#real->A)(s,&1)`; `&1`]
         COVERING_MAP_LIFT_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                    TOPC_CONNECTED_UNIT_INTERVAL] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`X:A topology`; `K:real#real->A`; `&0`]
        TOPC_SQUARE_SLICES) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`X:A topology`; `K:real#real->A`; `&1`]
        TOPC_SQUARE_SLICES) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(p:A->B)((K:real#real->A)(s,&0)) = (H:real#real->B)(s,&0) /\
        (p:A->B)((K:real#real->A)(s,&1)) = (H:real#real->B)(s,&1)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!t z. t IN real_interval[&0,&1] /\ z IN real_interval[&0,&1]
                 ==> (p:A->B)((K:real#real->A)(t,z)) = (H:real#real->B)(t,z)`)
          (concl th))) THEN ASM_REWRITE_TAC[];
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN ASM_SIMP_TAC[]]);;

let COVERING_MAP_HOMEOMORPHISM = prove
 (`!X Y (p:A->B).
        covering_map (X,Y) p /\ path_connected_space X /\ simply_connected_space Y
        ==> homeomorphic_map (X,Y) p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BIJECTIVE_OPEN_IMP_HOMEOMORPHIC_MAP THEN
  ASM_SIMP_TAC[COVERING_MAP_IMP_CONTINUOUS; COVERING_MAP_OPEN_MAP;
               COVERING_MAP_IMP_SURJECTIVE] THEN
  ASM_MESON_TAC[COVERING_MAP_INJECTIVE]);;

(* ========================================================================= *)
(* Characterizations of simply_connected_space (as for                      *)
(* simply_connected in paths.ml).  The free-to-based step factors a free    *)
(* null-homotopy of a loop through the closed unit disk of the complex      *)
(* plane (a quotient of the square) and uses straight-line homotopies in    *)
(* the disk.                                                                 *)
(* ========================================================================= *)

(* Monotonicity of the homotopy property. *)

let TOPC_HOMOTOPIC_WITH_MONO = prove
 (`!P Q (X:A topology) (Y:B topology) f g.
        homotopic_with P (X,Y) f g /\ (!h. P h ==> Q h)
        ==> homotopic_with Q (X,Y) f g`,
  REWRITE_TAC[homotopic_with] THEN MESON_TAC[]);;

(* Continuity of real functions on real subspaces (the statement of          *)
(* GRGD_CONTINUOUS_MAP_REAL in pc_grg_dist.ml, proved again here so that     *)
(* this file depends only on the library).                                   *)

let TOPC_CONTINUOUS_MAP_REAL_FUNCTION = prove
 (`!h s. continuous_map (subtopology euclideanreal s,euclideanreal) h <=>
         h real_continuous_on s`,
  REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; CONTINUOUS_MAP_EQ_LIFT;
              CONTINUOUS_MAP_EUCLIDEAN; REAL_CONTINUOUS_ON] THEN
  REWRITE_TAC[o_ASSOC]);;

let TOPC_CONTINUOUS_MAP_REAL_COMPOSE = prove
 (`!(top:A topology) g h.
        continuous_map (top,euclideanreal) g /\ h real_continuous_on (:real)
        ==> continuous_map (top,euclideanreal) (\x. h(g x))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:real->real`; `(:real)`] TOPC_CONTINUOUS_MAP_REAL_FUNCTION) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV]);;

(* The join of a path with the reverse of another path with the same end.  *)

let TOPC_PATH_IN_JOIN_REVERSE = prove
 (`!top (p:real->A) q.
        path_in top p /\ path_in top q /\ p(&1) = q(&1)
        ==> path_in top (\t. if t <= &1 / &2 then p(&2 * t) else q(&2 - &2 * t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_in] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval [&0,&1])` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY;
        TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER;
        IN_REAL_INTERVAL; IN_ELIM_THM] THEN
  (CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC) THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_ID]);;

(* Constant loops along a path are homotopic as loops. *)

let TOPC_CONSTANT_LOOPS_HOMOTOPIC = prove
 (`!top (g:real->A).
        path_in top g
        ==> homotopic_with (\r. r(&1) = r(&0))
              (subtopology euclideanreal (real_interval[&0,&1]),top)
              (\t. g(&0)) (\t. g(&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC `\w:real#real. (g:real->A)(FST w)` THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
  REWRITE_TAC[CONTINUOUS_MAP_FST] THEN ASM_REWRITE_TAC[GSYM path_in]);;

let TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED = prove
 (`!top:A topology. simply_connected_space top ==> path_connected_space top`,
  GEN_TAC THEN REWRITE_TAC[simply_connected_space; path_connected_space] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\t:real. (a:A)`; `\t:real. (b:A)`]) THEN
  ASM_REWRITE_TAC[PATH_IN_CONST; homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\s. (H:real#real->A)(s,&0)` THEN ASM_REWRITE_TAC[path_in] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                            (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

(* The map (s,t) |-> (1 - s) exp(2 pi i t) from the square onto the disk.  *)

let TOPC_DISK_MAP_CONTINUOUS = prove
 (`continuous_map
     (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                    (subtopology euclideanreal (real_interval[&0,&1])),
      euclidean)
     (\w:real#real. Cx(&1 - FST w) * cexp(ii * Cx(&2 * pi * SND w)))`,
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; DIMINDEX_2; FORALL_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP;
              RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0;
              REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `continuous_map
      (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                     (subtopology euclideanreal (real_interval[&0,&1])),
       euclideanreal) FST /\
    continuous_map
      (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                     (subtopology euclideanreal (real_interval[&0,&1])),
       euclideanreal) SND`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_REAL_SUB; CONTINUOUS_MAP_REAL_CONST] THEN
  MATCH_MP_TAC TOPC_CONTINUOUS_MAP_REAL_COMPOSE THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_COS; REAL_CONTINUOUS_ON_SIN] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN ASM_REWRITE_TAC[ETA_AX]);;

let TOPC_DISK_MAP_IMAGE = prove
 (`IMAGE (\w:real#real. Cx(&1 - FST w) * cexp(ii * Cx(&2 * pi * SND w)))
         (real_interval[&0,&1] CROSS real_interval[&0,&1]) =
   cball(Cx(&0),&1)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; IN_REAL_INTERVAL;
              GSYM COMPLEX_VEC_0; IN_CBALL_0] THEN
  X_GEN_TAC `z:complex` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_CEXP_II] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1 - norm(z:complex)`; `Arg z / (&2 * pi)`] THEN
    MP_TAC(SPEC `z:complex` ARG) THEN MP_TAC PI_POS THEN
    MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN
    SIMP_TAC[REAL_FIELD `&0 < pi ==> &2 * pi * x / (&2 * pi) = x`] THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`] THEN
    REPEAT STRIP_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < pi ==> &0 < &2 * pi`] THEN
      ASM_REAL_ARITH_TAC]]);;

let TOPC_DISK_MAP_FIBRES = prove
 (`!s t s' t'.
        s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1] /\
        s' IN real_interval[&0,&1] /\ t' IN real_interval[&0,&1] /\
        Cx(&1 - s) * cexp(ii * Cx(&2 * pi * t)) =
        Cx(&1 - s') * cexp(ii * Cx(&2 * pi * t'))
        ==> s = s' /\
            (s = &1 \/ t = t' \/ t = &0 /\ t' = &1 \/ t = &1 /\ t' = &0)`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s:real = s'` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_CEXP_II] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[]] THEN
  ASM_CASES_TAC `s' = &1` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPLEX_EQ_MUL_LCANCEL]) THEN
  ASM_REWRITE_TAC[CX_INJ; REAL_ARITH `&1 - x = &0 <=> x = &1`; CEXP_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t = t' + n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
    REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX; IM_MUL_CX; IM_II; IM_CX] THEN
    MP_TAC PI_POS THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = &0` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* A free null-homotopy of a loop (constant at the end s = 1, closed at each *)
(* stage) factors through the closed unit disk: D((1 - s) exp(2 pi i t)) =  *)
(* H(s,t), with D continuous.                                                *)

let TOPC_LOOP_DISK = prove
 (`!top (H:real#real->A).
        continuous_map
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                         (subtopology euclideanreal (real_interval[&0,&1])),top) H /\
        (!t. t IN real_interval[&0,&1] ==> H(&1,t) = H(&1,&0)) /\
        (!s. s IN real_interval[&0,&1] ==> H(s,&1) = H(s,&0))
        ==> ?D. continuous_map (subtopology euclidean (cball(Cx(&0),&1)),top) D /\
                !s t. s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1]
                      ==> D(Cx(&1 - s) * cexp(ii * Cx(&2 * pi * t))) = H(s,t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (subtopology euclideanreal (real_interval[&0,&1]))`;
    `subtopology euclidean (cball(Cx(&0),&1))`; `top:A topology`;
    `\w:real#real. Cx(&1 - FST w) * cexp(ii * Cx(&2 * pi * SND w))`;
    `H:real#real->A`] QUOTIENT_MAP_LIFT_EXISTS) THEN
  ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  FORALL_PAIR_THM; IN_CROSS] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_IMP_QUOTIENT_MAP THEN
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPC_DISK_MAP_IMAGE] THEN
      SUBGOAL_THEN
       `continuous_map
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                         (subtopology euclideanreal (real_interval[&0,&1])),
           subtopology euclidean (cball(Cx(&0),&1)))
          (\w:real#real. Cx(&1 - FST w) * cexp(ii * Cx(&2 * pi * SND w)))`
      ASSUME_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPC_DISK_MAP_CONTINUOUS] THEN
        REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                    TOPC_DISK_MAP_IMAGE; SUBSET_REFL];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_IMP_CLOSED_MAP THEN
        ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN] THEN
        REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN
        SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; COMPACT_IN_EUCLIDEANREAL_INTERVAL]];
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `s':real`; `t':real`] THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`s:real`; `t:real`; `s':real`; `t':real`]
        TOPC_DISK_MAP_FIBRES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `D:complex->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `D:complex->A` THEN ASM_SIMP_TAC[]]);;

(* Circular paths t |-> exp(i (c t + d)) are continuous. *)

let TOPC_CEXP_PATH_CONTINUOUS = prove
 (`!c d. continuous_map (subtopology euclideanreal (real_interval[&0,&1]),euclidean)
                        (\t. cexp(ii * Cx(c * t + d)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; DIMINDEX_2; FORALL_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CEXP; IM_CEXP;
              RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0;
              REAL_MUL_LID] THEN
  CONJ_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_REAL_COMPOSE THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_COS; REAL_CONTINUOUS_ON_SIN] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID]);;

(* Straight-line homotopy inside the disk between two paths with the same    *)
(* endpoints, read through a continuous map D on the disk.                   *)

let TOPC_DISK_STRAIGHT_HOMOTOPY = prove
 (`!top (D:complex->A) (a:real->complex) b.
        continuous_map (subtopology euclidean (cball(Cx(&0),&1)),top) D /\
        continuous_map (subtopology euclideanreal (real_interval[&0,&1]),euclidean) a /\
        continuous_map (subtopology euclideanreal (real_interval[&0,&1]),euclidean) b /\
        (!t. t IN real_interval[&0,&1] ==> norm(a t) <= &1 /\ norm(b t) <= &1) /\
        a(&0) = b(&0) /\ a(&1) = b(&1)
        ==> homotopic_with (\r. r(&0) = D(a(&0)) /\ r(&1) = D(a(&1)))
              (subtopology euclideanreal (real_interval[&0,&1]),top)
              (\t. D(a t)) (\t. D(b t))`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) HOMOTOPIC_WITH w)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC `\w:real#real. (D:complex->A)((&1 - FST w) % a(SND w) + FST w % b(SND w))` THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID; VECTOR_ADD_RID;
           REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - t) % x + t % x = x:real^N`] THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (subtopology euclideanreal (real_interval[&0,&1]))`;
    `subtopology euclidean (cball(Cx(&0),&1))`; `top:A topology`;
    `\w:real#real. (&1 - FST w) % (a:real->complex)(SND w) + FST w % b(SND w)`;
    `D:complex->A`] CONTINUOUS_MAP_COMPOSE) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_SND]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                IN_CROSS; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `t:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_CBALL_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH lhand NORM_TRIANGLE o lhand o snd) THEN
    REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= c ==> b <= a ==> b <= c`) THEN
    SUBGOAL_THEN `abs(&1 - u) = &1 - u /\ abs u = u` (CONJUNCTS_THEN SUBST1_TAC)
    THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN ASM_REAL_ARITH_TAC]);;

(* In a simply connected space, paths with the same endpoints are homotopic *)
(* with fixed endpoints: the loop p followed by q backwards factors through *)
(* the disk, where the two half circles are homotopic along straight lines. *)

let TOPC_SIMPLY_CONNECTED_HOMOTOPIC_PATHS = prove
 (`!top (p:real->A) q.
        simply_connected_space top /\ path_in top p /\ path_in top q /\
        q(&0) = p(&0) /\ q(&1) = p(&1)
        ==> homotopic_with (\r. r(&0) = p(&0) /\ r(&1) = p(&1))
              (subtopology euclideanreal (real_interval[&0,&1]),top) p q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = \t. if t <= &1 / &2 then (p:real->A)(&2 * t) else q(&2 - &2 * t)` THEN
  SUBGOAL_THEN `path_in top (L:real->A)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC TOPC_PATH_IN_JOIN_REVERSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real->A)(&0) IN topspace top` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
      check (fun th -> can (term_match []
        `continuous_map (subtopology euclideanreal s,top:A topology) p`)
        (concl th))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`L:real->A`; `\t:real. (p:real->A)(&0)`] o
    GEN_REWRITE_RULE I [simply_connected_space]) THEN
  ASM_REWRITE_TAC[PATH_IN_CONST] THEN ANTS_TAC THENL
   [EXPAND_TAC "L" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[homotopic_with]) THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `H:real#real->A`] TOPC_LOOP_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:complex->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> (D:complex->A)(cexp(ii * Cx(pi * t + &0))) = p t /\
            D(cexp(ii * Cx(--pi * t + &2 * pi))) = q t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `t / &2`] o
        check (fun th -> can (term_match []
          `!s t. s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1]
                 ==> (D:complex->A)(Cx(&1 - s) * cexp(ii * Cx(&2 * pi * t))) =
                     H(s,t)`) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&1 - t / &2`] o
        check (fun th -> can (term_match []
          `!s t. s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1]
                 ==> (D:complex->A)(Cx(&1 - s) * cexp(ii * Cx(&2 * pi * t))) =
                     H(s,t)`) (concl th)))] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_RZERO; COMPLEX_MUL_LID] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[REAL_ARITH `&2 * pi * t / &2 = pi * t + &0`;
                REAL_ARITH `&2 * pi * (&1 - t / &2) = --pi * t + &2 * pi`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[] THENL
     [COND_CASES_TAC THENL [AP_TERM_TAC THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      COND_CASES_TAC THENL
       [SUBGOAL_THEN `t = &1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        AP_TERM_TAC THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cexp(ii * Cx(&2 * pi)) = Cx(&1)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` CEXP_INTEGER_2PI) THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_MUL_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `D:complex->A`;
                 `\t. cexp(ii * Cx(pi * t + &0))`;
                 `\t. cexp(ii * Cx(--pi * t + &2 * pi))`]
                TOPC_DISK_STRAIGHT_HOMOTOPY) THEN
  ASM_REWRITE_TAC[TOPC_CEXP_PATH_CONTINUOUS; NORM_CEXP_II; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RID] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; CEXP_0] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&0` (ASSUME
    `!t. t IN real_interval[&0,&1]
        ==> (D:complex->A)(cexp(ii * Cx(pi * t + &0))) = p t /\
            D(cexp(ii * Cx(--pi * t + &2 * pi))) = q t`)) THEN
  MP_TAC(SPEC `&1` (ASSUME
    `!t. t IN real_interval[&0,&1]
        ==> (D:complex->A)(cexp(ii * Cx(pi * t + &0))) = p t /\
            D(cexp(ii * Cx(--pi * t + &2 * pi))) = q t`)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\t. (D:complex->A)(cexp(ii * Cx(pi * t + &0)))`;
    `\t. (D:complex->A)(cexp(ii * Cx(--pi * t + &2 * pi)))`] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The characterizations of simply_connected_space.                         *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_ANY = prove
 (`!top:A topology.
        simply_connected_space top <=>
        !p a. path_in top p /\ p(&1) = p(&0) /\ a IN topspace top
              ==> homotopic_with (\r. r(&1) = r(&0))
                    (subtopology euclideanreal (real_interval[&0,&1]),top)
                    p (\t. a)`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[simply_connected_space] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[PATH_IN_CONST];
    DISCH_TAC THEN REWRITE_TAC[simply_connected_space] THEN
    MAP_EVERY X_GEN_TAC [`p:real->A`; `q:real->A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real->A)(&0) IN topspace top` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
        check (fun th -> can (term_match []
          `continuous_map (subtopology euclideanreal s,top:A topology) p`)
          (concl th))) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `\t:real. (p:real->A)(&0)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_SOME = prove
 (`!top:A topology.
        simply_connected_space top <=>
        path_connected_space top /\
        !p. path_in top p /\ p(&1) = p(&0)
            ==> ?a. a IN topspace top /\
                    homotopic_with (\r. r(&1) = r(&0))
                      (subtopology euclideanreal (real_interval[&0,&1]),top)
                      p (\t. a)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
    X_GEN_TAC `p:real->A` THEN STRIP_TAC THEN
    EXISTS_TAC `(p:real->A)(&0)` THEN
    SUBGOAL_THEN `(p:real->A)(&0) IN topspace top` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
        check (fun th -> can (term_match []
          `continuous_map (subtopology euclideanreal s,top:A topology) p`)
          (concl th))) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real->A`; `a:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real->A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN EXISTS_TAC `\t:real. (b:A)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:A`; `a:A`] o
      GEN_REWRITE_RULE I [path_connected_space]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `g:real->A`] TOPC_CONSTANT_LOOPS_HOMOTOPIC) THEN
    ASM_REWRITE_TAC[]]);;

let SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_ALL = prove
 (`!top:A topology.
        simply_connected_space top <=>
        topspace top = {} \/
        ?a. a IN topspace top /\
            !p. path_in top p /\ p(&1) = p(&0)
                ==> homotopic_with (\r. r(&1) = r(&0))
                      (subtopology euclideanreal (real_interval[&0,&1]),top)
                      p (\t. a)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `topspace top:A->bool = {}` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    ASM_MESON_TAC[];
    STRIP_TAC THENL
     [REWRITE_TAC[simply_connected_space; path_in] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
        check (fun th -> can (term_match []
          `continuous_map (subtopology euclideanreal s,top:A topology) p`)
          (concl th))) THEN
      ASM_REWRITE_TAC[SUBSET_EMPTY; IMAGE_EQ_EMPTY;
                      TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                      REAL_INTERVAL_EQ_EMPTY] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[simply_connected_space] THEN
      MAP_EVERY X_GEN_TAC [`p:real->A`; `q:real->A`] THEN STRIP_TAC THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN EXISTS_TAC `\t:real. (a:A)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

let SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_PATH = prove
 (`!top:A topology.
        simply_connected_space top <=>
        path_connected_space top /\
        !p. path_in top p /\ p(&1) = p(&0)
            ==> homotopic_with (\r. r(&0) = p(&0) /\ r(&1) = p(&1))
                  (subtopology euclideanreal (real_interval[&0,&1]),top)
                  p (\t. p(&0))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
    X_GEN_TAC `p:real->A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `p:real->A`; `\t:real. (p:real->A)(&0)`]
      TOPC_SIMPLY_CONNECTED_HOMOTOPIC_PATHS) THEN
    ASM_REWRITE_TAC[PATH_IN_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
      check (fun th -> can (term_match []
        `continuous_map (subtopology euclideanreal s,top:A topology) p`)
        (concl th))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_SOME] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real->A` THEN STRIP_TAC THEN
    EXISTS_TAC `(p:real->A)(&0)` THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
        check (fun th -> can (term_match []
          `continuous_map (subtopology euclideanreal s,top:A topology) p`)
          (concl th))) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC TOPC_HOMOTOPIC_WITH_MONO THEN
      EXISTS_TAC `\r:real->A. r(&0) = p(&0) /\ r(&1) = p(&1)` THEN
      ASM_SIMP_TAC[] THEN SIMP_TAC[]]]);;

let SIMPLY_CONNECTED_SPACE_EQ_HOMOTOPIC_PATHS = prove
 (`!top:A topology.
        simply_connected_space top <=>
        path_connected_space top /\
        !p q. path_in top p /\ path_in top q /\
              q(&0) = p(&0) /\ q(&1) = p(&1)
              ==> homotopic_with (\r. r(&0) = p(&0) /\ r(&1) = p(&1))
                    (subtopology euclideanreal (real_interval[&0,&1]),top) p q`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_SIMPLY_CONNECTED_HOMOTOPIC_PATHS THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_PATH] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real->A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[PATH_IN_CONST] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map] o
      check (fun th -> can (term_match []
        `continuous_map (subtopology euclideanreal s,top:A topology) p`)
        (concl th))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The lifting criterion for simply connected, locally path-                *)
(* connected domains, and sections of coverings of simply connected bases.  *)
(* ========================================================================= *)

(* Continuity is local. *)

let TOPC_CONTINUOUS_MAP_LOCAL = prove
 (`!(Z:C topology) (X:A topology) k.
        (!z. z IN topspace Z
             ==> ?W. open_in Z W /\ z IN W /\ continuous_map (subtopology Z W,X) k)
        ==> continuous_map (Z,X) k`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `W:C->C->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Z:C topology`; `X:A topology`; `\z:C. (k:C->A)`;
                 `W:C->C->bool`; `topspace Z:C->bool`] PASTING_LEMMA_EXISTS) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:C->A` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `g:C->A` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:C` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:C`; `z:C`]) THEN
    ASM_SIMP_TAC[IN_INTER]]);;

(* The join of two paths. *)

let TOPC_PATH_IN_JOIN = prove
 (`!top (p:real->A) q.
        path_in top p /\ path_in top q /\ p(&1) = q(&0)
        ==> path_in top (\t. if t <= &1 / &2 then p(&2 * t) else q(&2 * t - &1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_in] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval [&0,&1])` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY;
        TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER;
        IN_REAL_INTERVAL; IN_ELIM_THM] THEN
  (CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC) THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_ID]);;

(* Points of a path lie in the topological space. *)

let TOPC_PATH_IN_TOPSPACE = prove
 (`!top (g:real->A) t.
        path_in top g /\ t IN real_interval[&0,&1] ==> g t IN topspace top`,
  REWRITE_TAC[path_in; continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  MESON_TAC[]);;

(* A local homeomorphism has continuous local inverses. *)

let TOPC_LOCAL_HOMEOMORPHISM_LOCAL_INVERSE = prove
 (`!X Y (p:A->B) x.
        local_homeomorphism_map (X,Y) p /\ x IN topspace X
        ==> ?U V q. open_in X U /\ open_in Y V /\ x IN U /\
                    continuous_map (subtopology Y V,X) q /\
                    (!x'. x' IN U ==> p x' IN V /\ q(p x') = x') /\
                    (!y. y IN V ==> q y IN U /\ p(q y) = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[local_homeomorphism_map] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `x:A`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `V:B->bool`] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:B->A` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `V:B->bool`; `q:B->A`] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace X /\ (V:B->bool) SUBSET topspace Y`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Uniqueness of the endpoint of lifts along paths with the same ends in a  *)
(* simply connected space.                                                  *)

let TOPC_LIFT_ENDPOINT_UNIQUE = prove
 (`!X Y (p:A->B) Z (f:C->B) g1 g2 h1 h2.
        covering_map (X,Y) p /\ simply_connected_space Z /\
        continuous_map (Z,Y) f /\
        path_in Z g1 /\ path_in Z g2 /\ g2(&0) = g1(&0) /\ g2(&1) = g1(&1) /\
        path_in X h1 /\ path_in X h2 /\ h1(&0) = h2(&0) /\
        (!t. t IN real_interval[&0,&1] ==> p(h1 t) = f(g1 t)) /\
        (!t. t IN real_interval[&0,&1] ==> p(h2 t) = f(g2 t))
        ==> h1(&1) = h2(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `homotopic_with (\r. r(&0) = (g1:real->C)(&0) /\ r(&1) = g1(&1))
      (subtopology euclideanreal (real_interval[&0,&1]),Z) g1 g2`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [SIMPLY_CONNECTED_SPACE_EQ_HOMOTOPIC_PATHS]) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                 `(f:C->B) o (g1:real->C)`; `(f:C->B) o (g2:real->C)`;
                 `h1:real->A`; `h2:real->A`] COVERING_MAP_MONODROMY) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  (REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC)) THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT THEN
    EXISTS_TAC `\r. r(&0) = (g1:real->C)(&0) /\ r(&1) = g1(&1)` THEN
    EXISTS_TAC `Z:C topology` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[o_THM];
    ASM_SIMP_TAC[o_THM]]);;

(* The local step of the lifting criterion: near the end of a path g, the   *)
(* endpoints of lifts along extensions of g form a continuous map.          *)

let TOPC_LIFT_CRITERION_LOCAL = prove
 (`!X Y (p:A->B) Z (f:C->B) g h.
        covering_map (X,Y) p /\ locally_path_connected_space Z /\
        continuous_map (Z,Y) f /\ path_in Z g /\ path_in X h /\
        (!t. t IN real_interval[&0,&1] ==> p(h t) = f(g t))
        ==> ?W l. open_in Z W /\ g(&1) IN W /\
                  continuous_map (subtopology Z W,X) l /\
                  !z. z IN W
                      ==> ?g' h'. path_in Z g' /\ g'(&0) = g(&0) /\ g'(&1) = z /\
                                  path_in X h' /\ h'(&0) = h(&0) /\ h'(&1) = l z /\
                                  !t. t IN real_interval[&0,&1]
                                      ==> p(h' t) = f(g' t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real->C)(&1) IN topspace Z /\ (h:real->A)(&1) IN topspace X`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TOPC_PATH_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`; `(h:real->A)(&1)`]
    TOPC_LOCAL_HOMEOMORPHISM_LOCAL_INVERSE) THEN
  ASM_SIMP_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `V:B->bool`; `q:B->A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:C->B)((g:real->C)(&1)) IN V /\ (q:B->A)(f(g(&1))) = h(&1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th ->
      can (term_match [] `!t. t IN real_interval[&0,&1]
                              ==> (p:A->B)((h:real->A) t) = (f:C->B)((g:real->C) t)`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* a path-connected neighbourhood W of g(1) mapped into V *)
  FIRST_ASSUM(MP_TAC o SPECL
   [`{z | z IN topspace Z /\ (f:C->B) z IN V}`; `(g:real->C)(&1)`] o
    GEN_REWRITE_RULE I [LOCALLY_PATH_CONNECTED_SPACE]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `Y:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:C->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `continuous_map (subtopology Z W,X) ((q:B->A) o (f:C->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology Y (V:B->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:C->bool`; `(q:B->A) o (f:C->B)`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:C` THEN DISCH_TAC THEN
  (* a path c in W from g(1) to z *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`(g:real->C)(&1)`; `z:C`] o CONJUNCT2 o
    GEN_REWRITE_RULE I [PATH_CONNECTED_IN]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->C` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_in X (((q:B->A) o (f:C->B)) o (c:real->C))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_IN_COMPOSE THEN EXISTS_TAC `subtopology Z (W:C->bool)` THEN
    ASM_REWRITE_TAC[PATH_IN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\t. if t <= &1 / &2 then (g:real->C)(&2 * t) else (c:real->C)(&2 * t - &1)`;
    `\t. if t <= &1 / &2 then (h:real->A)(&2 * t)
         else (((q:B->A) o (f:C->B)) o (c:real->C))(&2 * t - &1)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TOPC_PATH_IN_JOIN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC TOPC_PATH_IN_JOIN THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[o_THM];
    REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[o_THM];
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[o_THM] THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t. t IN real_interval[&0,&1]
                                ==> (p:A->B)((h:real->A) t) = (f:C->B)((g:real->C) t)`)
            (concl th))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(c:real->C)(&2 * t - &1) IN W` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
          check (fun th -> can (term_match []
            `IMAGE (c:real->C) (real_interval[&0,&1]) SUBSET W`) (concl th))) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:C->B)((c:real->C)(&2 * t - &1)) IN V` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]]]]);;

(* The lifting criterion: maps from a simply connected, locally path-       *)
(* connected space lift through any covering map.                           *)

let COVERING_MAP_LIFT_STRONG = prove
 (`!X Y (p:A->B) Z (f:C->B) z0 x0.
        covering_map (X,Y) p /\
        simply_connected_space Z /\ locally_path_connected_space Z /\
        continuous_map (Z,Y) f /\ z0 IN topspace Z /\ x0 IN topspace X /\
        p x0 = f z0
        ==> ?k. continuous_map (Z,X) k /\ k z0 = x0 /\
                !z. z IN topspace Z ==> p(k z) = f z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* endpoints of lifts along paths from z0 to z do not depend on the path *)
  SUBGOAL_THEN
   `!z:C x1:A x2:A.
      (?g h. path_in Z g /\ g(&0) = z0 /\ g(&1) = z /\
             path_in X h /\ h(&0) = x0 /\ h(&1) = x1 /\
             (!t. t IN real_interval[&0,&1] ==> (p:A->B)(h t) = (f:C->B)(g t))) /\
      (?g h. path_in Z g /\ g(&0) = z0 /\ g(&1) = z /\
             path_in X h /\ h(&0) = x0 /\ h(&1) = x2 /\
             (!t. t IN real_interval[&0,&1] ==> (p:A->B)(h t) = (f:C->B)(g t)))
      ==> x1 = x2`
  (LABEL_TAC "U") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `g1:real->C` (X_CHOOSE_THEN `h1:real->A` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `g2:real->C` (X_CHOOSE_THEN `h2:real->A` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`; `Z:C topology`;
                   `f:C->B`; `g1:real->C`; `g2:real->C`; `h1:real->A`; `h2:real->A`]
           TOPC_LIFT_ENDPOINT_UNIQUE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* such lifts exist *)
  SUBGOAL_THEN
   `!z:C. z IN topspace Z
          ==> ?x:A g h. path_in Z g /\ g(&0) = z0 /\ g(&1) = z /\
                        path_in X h /\ h(&0) = x0 /\ h(&1) = x /\
                        (!t. t IN real_interval[&0,&1]
                             ==> (p:A->B)(h t) = (f:C->B)(g t))`
  MP_TAC THENL
   [X_GEN_TAC `z:C` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED) THEN
    REWRITE_TAC[path_connected_space] THEN
    DISCH_THEN(MP_TAC o SPECL [`z0:C`; `z:C`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->C` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`;
                   `(f:C->B) o (g:real->C)`; `x0:A`] COVERING_MAP_LIFT_PATH_STRONG) THEN
    ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
     [MATCH_MP_TAC PATH_IN_COMPOSE THEN EXISTS_TAC `Z:C topology` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `h:real->A` STRIP_ASSUME_TAC)] THEN
    MAP_EVERY EXISTS_TAC [`(h:real->A)(&1)`; `g:real->C`; `h:real->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:C->A` THEN DISCH_THEN(LABEL_TAC "K") THEN
  EXISTS_TAC `k:C->A` THEN
  SUBGOAL_THEN `(k:C->A) z0 = x0` ASSUME_TAC THENL
   [USE_THEN "U" MATCH_MP_TAC THEN EXISTS_TAC `z0:C` THEN CONJ_TAC THENL
     [USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`\t:real. (z0:C)`; `\t:real. (x0:A)`] THEN
      ASM_REWRITE_TAC[PATH_IN_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `z:C` THEN DISCH_TAC THEN
    USE_THEN "K" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:C) IN topspace Z`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->C` (X_CHOOSE_THEN `h:real->A`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th ->
      can (term_match [] `!t. t IN real_interval[&0,&1]
                              ==> (p:A->B)((h:real->A) t) = (f:C->B)((g:real->C) t)`)
          (concl th))) THEN
    ASM_REWRITE_TAC[]] THEN
  (* continuity is local *)
  MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `z:C` THEN DISCH_TAC THEN
  USE_THEN "K" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:C) IN topspace Z`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->C` (X_CHOOSE_THEN `h:real->A`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`; `Z:C topology`;
                 `f:C->B`; `g:real->C`; `h:real->A`] TOPC_LIFT_CRITERION_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:C->bool` (X_CHOOSE_THEN `l:C->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L")))))) THEN
  EXISTS_TAC `W:C->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `l:C->A` THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  X_GEN_TAC `w:C` THEN STRIP_TAC THEN
  USE_THEN "U" MATCH_MP_TAC THEN EXISTS_TAC `w:C` THEN CONJ_TAC THENL
   [USE_THEN "L" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Sections of coverings of simply connected, locally path-connected        *)
(* spaces.                                                                  *)

let COVERING_MAP_SECTION = prove
 (`!X Y (p:A->B) x0.
        covering_map (X,Y) p /\
        simply_connected_space Y /\ locally_path_connected_space Y /\
        x0 IN topspace X
        ==> ?s. continuous_map (Y,X) s /\ s(p x0) = x0 /\
                !y. y IN topspace Y ==> p(s y) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`; `Y:B topology`;
                 `\y:B. y`; `(p:A->B) x0`; `x0:A`] COVERING_MAP_LIFT_STRONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_ID] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_MAP_IMP_CONTINUOUS) THEN
    REWRITE_TAC[continuous_map] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Local homeomorphisms from compact Hausdorff spaces.                       *)
(* ========================================================================= *)

(* Finitely many points of a Hausdorff space have pairwise disjoint open    *)
(* neighbourhoods.                                                          *)

let TOPC_HAUSDORFF_FINITE_SEPARATION = prove
 (`!X (s:A->bool).
        hausdorff_space X /\ s SUBSET topspace X /\ FINITE s
        ==> ?w. (!x. x IN s ==> open_in X (w x) /\ x IN w x) /\
                (!x x'. x IN s /\ x' IN s /\ ~(x = x')
                        ==> DISJOINT (w x) (w x'))`,
  GEN_TAC THEN ASM_CASES_TAC `hausdorff_space (X:A topology)` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC BINDER_CONV [TAUT `(p /\ q ==> r) <=> (q ==> p ==> r)`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:A topology`; `{a:A}`; `t:A->bool`]
    HAUSDORFF_SPACE_COMPACT_SEPARATION) THEN
  ASM_SIMP_TAC[FINITE_IMP_COMPACT_IN; FINITE_SING; SING_SUBSET] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (X_CHOOSE_THEN `v:A->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x:A. if x = a then u else (w:A->A->bool) x INTER v` THEN
  REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x:A = a` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `x':A`] THEN
    ASM_CASES_TAC `x:A = a` THEN ASM_CASES_TAC `x':A = a` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `DISJOINT ((w:A->A->bool) x) (w x')` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SET_TAC[]]]]);;

(* Fibres of a local homeomorphism from a compact space into a Hausdorff    *)
(* space are finite.                                                        *)

let TOPC_LOCAL_HOMEOMORPHISM_FINITE_FIBRE = prove
 (`!X Y (p:A->B) y.
        compact_space X /\ hausdorff_space Y /\
        continuous_map (X,Y) p /\ local_homeomorphism_map (X,Y) p /\
        y IN topspace Y
        ==> FINITE {x | x IN topspace X /\ p x = y}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A topology`; `{x | x IN topspace X /\ (p:A->B) x = y}`]
    DISCRETE_COMPACT_IN_EQ_FINITE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[derived_set_of; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN topspace X /\ (p:A->B) x = y` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:A` o GEN_REWRITE_RULE I [local_homeomorphism_map]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `V:B->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x':A` THEN
    ONCE_REWRITE_TAC[TAUT `~(~a /\ b /\ c) <=> b /\ c ==> a`] THEN STRIP_TAC THEN
    MATCH_MP_TAC TOPC_HOMEOMORPHIC_MAP_INJ THEN
    MAP_EVERY EXISTS_TAC
     [`X:A topology`; `Y:B topology`; `p:A->B`; `U:A->bool`; `V:B->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    MATCH_MP_TAC(TAUT `p ==> (p ==> q /\ r) ==> r`) THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{x | x IN topspace X /\ (p:A->B) x = y} =
      {x | x IN topspace X /\ p x IN {y}}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_SING]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `Y:B topology` THEN ASM_SIMP_TAC[CLOSED_IN_HAUSDORFF_SING]]);;

(* A local inverse restricted to a smaller sheet over a smaller open set.   *)

let TOPC_SHEET_HOMEOMORPHIC_MAP = prove
 (`!X Y (p:A->B) q U V0 S V.
        continuous_map (X,Y) p /\ U SUBSET topspace X /\
        continuous_map (subtopology Y V0,X) q /\
        (!x. x IN U ==> p x IN V0 /\ q(p x) = x) /\
        (!y. y IN V0 ==> q y IN U /\ p(q y) = y) /\
        S SUBSET U /\ V SUBSET IMAGE p S
        ==> homeomorphic_map
              (subtopology X (S INTER {x | x IN topspace X /\ p x IN V}),
               subtopology Y V) p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `q:B->A` THEN REWRITE_TAC[homeomorphic_maps] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `V0:B->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x:A. x IN S /\ p x = (z:B)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* A surjective local homeomorphism from a compact Hausdorff space onto a   *)
(* Hausdorff space is a covering map.                                       *)

let COMPACT_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP = prove
 (`!X Y (p:A->B).
        compact_space X /\ hausdorff_space X /\ hausdorff_space Y /\
        continuous_map (X,Y) p /\ IMAGE p (topspace X) = topspace Y /\
        local_homeomorphism_map (X,Y) p
        ==> covering_map (X,Y) p`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[covering_map] THEN
  X_GEN_TAC `b:B` THEN DISCH_TAC THEN
  ABBREV_TAC `s = {x | x IN topspace X /\ (p:A->B) x = b}` THEN
  SUBGOAL_THEN
   `(!x:A. x IN s ==> x IN topspace X /\ (p:A->B) x = b) /\
    (!x:A. x IN topspace X /\ (p:A->B) x = b ==> x IN s)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:A->bool) /\ s SUBSET topspace X /\ ~(s = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC TOPC_LOCAL_HOMEOMORPHISM_FINITE_FIBRE THEN
      EXISTS_TAC `Y:B topology` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      SUBGOAL_THEN `(b:B) IN IMAGE (p:A->B) (topspace X)` MP_TAC THENL
       [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  (* local inverses at the points of the fibre *)
  SUBGOAL_THEN
   `!x. ?U V q. x IN s
                ==> open_in X U /\ open_in Y V /\ x IN U /\
                    continuous_map (subtopology Y V,X) q /\
                    (!x'. x' IN U ==> (p:A->B) x' IN V /\ q(p x') = x') /\
                    (!y. y IN V ==> q y IN U /\ p(q y) = y)`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN s` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC TOPC_LOCAL_HOMEOMORPHISM_LOCAL_INVERSE THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`U:A->A->bool`; `V:A->B->bool`; `q:A->B->A`] THEN
  DISCH_THEN(LABEL_TAC "Q") THEN
  (* disjoint neighbourhoods of the points of the fibre *)
  MP_TAC(ISPECL [`X:A topology`; `s:A->bool`] TOPC_HAUSDORFF_FINITE_SEPARATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open_map (X,Y) (p:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[TOPC_LOCAL_HOMEOMORPHISM_OPEN_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN s ==> open_in X ((U:A->A->bool) x INTER w x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the image of the complement of the sheets is closed and misses b *)
  ABBREV_TAC
   `k = topspace X DIFF UNIONS (IMAGE (\x. (U:A->A->bool) x INTER w x) s)` THEN
  SUBGOAL_THEN `closed_in Y (IMAGE (p:A->B) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `X:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "k" THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM_SIMP_TAC[FORALL_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC
   `v = (topspace Y DIFF IMAGE (p:A->B) k) INTER
        INTERS (IMAGE (\x. IMAGE p ((U:A->A->bool) x INTER w x)) s)` THEN
  EXISTS_TAC `v:B->bool` THEN
  SUBGOAL_THEN `open_in Y (v:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      MATCH_MP_TAC OPEN_IN_INTERS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[open_map]) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN s ==> x IN (U:A->A->bool) x /\ x IN w x`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:B) IN v` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN EXPAND_TAC "k" THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; INTERS_IMAGE; IN_ELIM_THM; IN_IMAGE;
                UNIONS_IMAGE] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC
   `IMAGE (\x. ((U:A->A->bool) x INTER w x) INTER
               {x' | x' IN topspace X /\ (p:A->B) x' IN v}) s` THEN
  REPEAT CONJ_TAC THENL
   [(* the sheets cover the preimage of v *)
    REWRITE_TAC[UNIONS_IMAGE; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `z:A` THEN EQ_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `~((z:A) IN k)` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(p:A->B) z IN IMAGE p k` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(p:A->B) z IN v` THEN EXPAND_TAC "v" THEN SET_TAC[];
      EXPAND_TAC "k" THEN REWRITE_TAC[IN_DIFF; UNIONS_IMAGE; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
    (* the sheets are open *)
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `Y:B topology` THEN ASM_REWRITE_TAC[];
    (* the sheets are pairwise disjoint *)
    REWRITE_TAC[PAIRWISE_IMAGE] THEN REWRITE_TAC[pairwise] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `x':A`] THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `DISJOINT ((w:A->A->bool) x) (w x')` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    (* the sheets are mapped homeomorphically onto v *)
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "Q" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN s`))) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC TOPC_SHEET_HOMEOMORPHIC_MAP THEN
    MAP_EVERY EXISTS_TAC
     [`(q:A->B->A) x`; `(U:A->A->bool) x`; `(V:A->B->bool) x`] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN CONJ_TAC THENL
     [SET_TAC[];
      EXPAND_TAC "v" THEN REWRITE_TAC[SUBSET; IN_INTER; INTERS_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]]]);;

(* A local homeomorphism from a compact Hausdorff path-connected space into *)
(* a simply connected Hausdorff space is injective, and onto when X is      *)
(* nonempty (the image is open and closed).                                 *)

let COMPACT_LOCAL_HOMEOMORPHISM_SIMPLY_CONNECTED_BIJECTIVE = prove
 (`!X Y (p:A->B).
        compact_space X /\ hausdorff_space X /\ path_connected_space X /\
        hausdorff_space Y /\ simply_connected_space Y /\
        continuous_map (X,Y) p /\ local_homeomorphism_map (X,Y) p
        ==> (!x x'. x IN topspace X /\ x' IN topspace X /\ p x = p x' ==> x = x') /\
            (~(topspace X = {}) ==> IMAGE p (topspace X) = topspace Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(topspace X = {}) ==> IMAGE (p:A->B) (topspace X) = topspace Y`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `connected_space (Y:B topology)` MP_TAC THENL
     [ASM_MESON_TAC[TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED;
                    PATH_CONNECTED_IMP_CONNECTED_SPACE];
      ALL_TAC] THEN
    REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (p:A->B) (topspace X)`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`X:A topology`; `Y:B topology`; `p:A->B`]
          TOPC_LOCAL_HOMEOMORPHISM_OPEN_MAP) THEN
        ASM_REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[OPEN_IN_TOPSPACE];
        MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `X:A topology` THEN
        ASM_REWRITE_TAC[GSYM compact_space]];
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `topspace X:A->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  MATCH_MP_TAC COVERING_MAP_INJECTIVE THEN
  EXISTS_TAC `Y:B topology` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPACT_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP THEN
  ASM_SIMP_TAC[]);;

