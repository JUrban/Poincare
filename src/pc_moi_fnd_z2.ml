needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_gf2.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_tubed.ml";;
needs "src/pc_moi_s28_cut.ml";;
needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_star.ml";;
needs "src/pc_moi_fnd_bicol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_fnd_z2: foundations of the Moise PL core (Moise, Geometric        *)
(* Topology in Dimensions 2 and 3, GTM 47, 23.19 in Z/2 form, p.172).       *)
(* Main theorem (the statement term MOI_FND_COCYCLE_NONSPHERE_BOUNDARY of    *)
(* pc_moi_fnd_stmt.ml):                                                      *)
(*   Z2_COCYCLE_NONSPHERE_BOUNDARY: a finite connected combinatorial        *)
(*   3-manifold with boundary with a boundary component that is not a PL   *)
(*   2-sphere has a Z/2 1-cocycle that is not a coboundary.                 *)
(* Route: cardinal counting over GF(2) with parity incidence maps; the       *)
(* boundary pairing and the faces of the tetrahedra bound the 1-coboundaries *)
(* (dual connectivity of the 3-manifold), and chi(boundary) = 2 chi(c) with  *)
(* chi <= 2 per boundary component, below 2 for a non-sphere.                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The cochain maps of a complex.  moi_fz2_sk c k: k-simplices;             *)
(* moi_fz2_v c: vertex points; d0 (vertex sets to edges, the coboundary of  *)
(* z2_coboundary), d1 (edges to triangles, the cocycle condition), and the  *)
(* map L of triangles to the tetrahedra (INL) and the boundary components   *)
(* (INR) containing an odd number of them.                                   *)
(* ------------------------------------------------------------------------- *)

let moi_fz2_sk = new_definition
 `moi_fz2_sk (c:(real^N->bool)->bool) k = {s | s IN c /\ aff_dim s = &k}`;;

let moi_fz2_v = new_definition
 `moi_fz2_v (c:(real^N->bool)->bool) = {v:real^N | {v} IN c}`;;

let moi_fz2_d0 = new_definition
 `moi_fz2_d0 (c:(real^N->bool)->bool) =
    moi_fz2_pm (\(v:real^N) e. {v} IN c /\ v IN e) (moi_fz2_sk c 1)`;;

let moi_fz2_d1 = new_definition
 `moi_fz2_d1 (c:(real^N->bool)->bool) =
    moi_fz2_pm (\(e:real^N->bool) s. e IN moi_fz2_sk c 1 /\ e SUBSET s) (moi_fz2_sk c 2)`;;

let moi_fz2_ly = new_definition
 `moi_fz2_ly (c:(real^N->bool)->bool) =
    IMAGE (INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) (moi_fz2_sk c 3) UNION
    IMAGE (INR:(real^N->bool)->(real^N->bool)+(real^N->bool))
          (components (complex_boundary c))`;;

let moi_fz2_lr = new_definition
 `moi_fz2_lr (c:(real^N->bool)->bool) (f:real^N->bool)
             (y:(real^N->bool)+(real^N->bool)) <=>
    f IN moi_fz2_sk c 2 /\
    ((?r. y = INL r /\ f SUBSET r) \/ (?b. y = INR b /\ f SUBSET b))`;;

let moi_fz2_l = new_definition
 `moi_fz2_l (c:(real^N->bool)->bool) = moi_fz2_pm (moi_fz2_lr c) (moi_fz2_ly c)`;;

let MOI_FZ2_LR = prove
 (`!c (f:real^N->bool) r b.
     (moi_fz2_lr c f (INL r) <=> f IN moi_fz2_sk c 2 /\ f SUBSET r) /\
     (moi_fz2_lr c f (INR b) <=> f IN moi_fz2_sk c 2 /\ f SUBSET b)`,
  REWRITE_TAC[moi_fz2_lr; sum_DISTINCT; sum_INJECTIVE] THEN MESON_TAC[]);;

let MOI_FZ2_FINITE = prove
 (`!c:(real^N->bool)->bool.
     FINITE c
     ==> (!k. FINITE (moi_fz2_sk c k)) /\ FINITE (moi_fz2_v c) /\
         CARD (moi_fz2_v c) = CARD (moi_fz2_sk c 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. FINITE (moi_fz2_sk (c:(real^N->bool)->bool) k)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_fz2_sk] THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_fz2_v] THEN
    MP_TAC(ISPECL [`\v:real^N. {v}`; `c:(real^N->bool)->bool`] FINITE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `UNIONS c:real^N->bool`] MOI_FTD_VERTEX_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{s | s IN c /\ aff_dim s = &0 /\ s SUBSET UNIONS c} = moi_fz2_sk c 0 /\
                {v | {v} IN c /\ v IN UNIONS c} = moi_fz2_v (c:(real^N->bool)->bool)`
  (fun th -> REWRITE_TAC[th] THEN SIMP_TAC[]) THEN
  REWRITE_TAC[moi_fz2_sk; moi_fz2_v; EXTENSION; IN_ELIM_THM; IN_UNIONS] THEN
  CONJ_TAC THEN GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN MESON_TAC[IN_SING]);;

(* The incidence finiteness needed for additivity. *)

let MOI_FZ2_MAPS_SD = prove
 (`!c:(real^N->bool)->bool.
     FINITE c
     ==> (!w1 w2. moi_fz2_d0 c (moi_fz2_sd w1 w2) =
                  moi_fz2_sd (moi_fz2_d0 c w1) (moi_fz2_d0 c w2)) /\
         (!z1 z2. moi_fz2_d1 c (moi_fz2_sd z1 z2) =
                  moi_fz2_sd (moi_fz2_d1 c z1) (moi_fz2_d1 c z2)) /\
         (!u1 u2. moi_fz2_l c (moi_fz2_sd u1 u2) =
                  moi_fz2_sd (moi_fz2_l c u1) (moi_fz2_l c u2))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE) THEN
  REWRITE_TAC[moi_fz2_d0; moi_fz2_d1; moi_fz2_l] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_FZ2_PM_SD THEN GEN_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `moi_fz2_v (c:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[moi_fz2_v] THEN SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `moi_fz2_sk (c:(real^N->bool)->bool) 1` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `moi_fz2_sk (c:(real^N->bool)->bool) 2` THEN
    ASM_REWRITE_TAC[moi_fz2_lr] THEN SET_TAC[]]);;

(* The z2 definitions in terms of d0 and d1. *)

let MOI_FZ2_COCYCLE = prove
 (`!c (z:(real^N->bool)->bool).
     z2_cocycle c z <=> z SUBSET moi_fz2_sk c 1 /\ moi_fz2_d1 c z = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[z2_cocycle; moi_fz2_d1; moi_fz2_pm] THEN
  SUBGOAL_THEN `z SUBSET moi_fz2_sk c 1 <=>
                (!e:real^N->bool. e IN z ==> e IN c /\ aff_dim e = &1)`
  SUBST1_TAC THENL [REWRITE_TAC[moi_fz2_sk; SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `!e:real^N->bool. e IN z ==> e IN c /\ aff_dim e = &1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s:real^N->bool. {e | e IN z /\ e IN moi_fz2_sk c 1 /\ e SUBSET s} =
                                 {e | e IN z /\ e SUBSET s}` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; moi_fz2_sk] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; moi_fz2_sk; GSYM NOT_EVEN] THEN
  MESON_TAC[]);;

let MOI_FZ2_COBOUNDARY = prove
 (`!c (z:(real^N->bool)->bool).
     z SUBSET moi_fz2_sk c 1
     ==> (z2_coboundary c z <=>
          z IN IMAGE (moi_fz2_d0 c) {w | w SUBSET moi_fz2_v c})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[z2_coboundary; IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[moi_fz2_d0; moi_fz2_pm] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `w:real^N->bool`) THEN
    EXISTS_TAC `w INTER moi_fz2_v (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    UNDISCH_TAC `(z:(real^N->bool)->bool) SUBSET moi_fz2_sk c 1` THEN
    REWRITE_TAC[moi_fz2_sk; moi_fz2_v; EXTENSION; SUBSET; IN_ELIM_THM; IN_INTER] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real^N->bool` THEN
    SUBGOAL_THEN `{v | (v IN w /\ {v} IN c) /\ {v} IN c /\ v IN e} =
                  {v:real^N | v IN w /\ v IN e /\ {v} IN c}` SUBST1_TAC THENL
     [SET_TAC[]; ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM; moi_fz2_sk] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Cycles.  Each edge of a tetrahedron lies in exactly two of its           *)
(* triangles, each edge of a boundary component in exactly two of its       *)
(* triangles; hence L o d1 = 0 (double counting mod 2).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FZ2_VS_SUBSET = prove
 (`!c s t:real^N->bool.
     simplicial_complex c /\ s IN c /\ t IN c /\ s SUBSET t
     ==> moi_fsa_vs s SUBSET moi_fsa_vs t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x:real^N} IN c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_VS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `x:real^N`] MOI_FSA_VS_MEM) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `x:real^N`] MOI_FSA_VS_MEM) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FZ2_SIMPLEX_FACTS = prove
 (`!c t:real^N->bool.
     simplicial_complex c /\ t IN c
     ==> convex hull (moi_fsa_vs t) = t /\ FINITE (moi_fsa_vs t) /\
         &(CARD (moi_fsa_vs t)) = aff_dim t + &1 /\
         (!w. w SUBSET moi_fsa_vs t
              ==> convex hull w IN c /\ moi_fsa_vs (convex hull w) = w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSA_VS) THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    REWRITE_TAC[SYM(el 1 cs); el 2 cs; el 3 cs; el 5 cs]));;

let MOI_FZ2_TET_EDGE2 = prove
 (`!c (r:real^N->bool) e.
     simplicial_complex c /\ r IN c /\ aff_dim r = &3 /\
     e IN c /\ aff_dim e = &1 /\ e SUBSET r
     ==> {f | f IN c /\ aff_dim f = &2 /\ f SUBSET r /\ e SUBSET f} HAS_SIZE 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_fsa_vs (e:real^N->bool) SUBSET moi_fsa_vs r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FZ2_VS_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FZ2_SIMPLEX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RH") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RS")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FZ2_SIMPLEX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EH") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `CARD (moi_fsa_vs (r:real^N->bool)) = 4 /\
                CARD (moi_fsa_vs (e:real^N->bool)) = 2` STRIP_ASSUME_TAC
  THENL [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN moi_fsa_vs r DIFF moi_fsa_vs e
      ==> convex hull (x INSERT moi_fsa_vs e) IN c /\
          moi_fsa_vs (convex hull (x INSERT moi_fsa_vs e)) = x INSERT moi_fsa_vs e /\
          CARD (x INSERT moi_fsa_vs e) = 3`
  (LABEL_TAC "XH") THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    USE_THEN "RS" (MP_TAC o SPEC `(x:real^N) INSERT moi_fsa_vs e`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CARD_CLAUSES; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{f | f IN c /\ aff_dim f = &2 /\ f SUBSET r /\ e SUBSET f} =
    IMAGE (\x:real^N. convex hull (x INSERT moi_fsa_vs e)) (moi_fsa_vs r DIFF moi_fsa_vs e)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `moi_fsa_vs (f:real^N->bool) SUBSET moi_fsa_vs r /\
                    moi_fsa_vs e SUBSET moi_fsa_vs f`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC MOI_FZ2_VS_SUBSET THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`] MOI_FZ2_SIMPLEX_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FH") (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
      SUBGOAL_THEN `CARD (moi_fsa_vs (f:real^N->bool)) = 3` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(moi_fsa_vs (f:real^N->bool) DIFF moi_fsa_vs e) HAS_SIZE 1` MP_TAC THENL
       [ASM_SIMP_TAC[HAS_SIZE; CARD_DIFF; FINITE_DIFF; ARITH]; ALL_TAC] THEN
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN EXISTS_TAC `x:real^N` THEN
      SUBGOAL_THEN `moi_fsa_vs (f:real^N->bool) = x INSERT moi_fsa_vs e` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_fsa_vs (f:real^N->bool) DIFF moi_fsa_vs e = {x}` THEN
        UNDISCH_TAC `moi_fsa_vs (e:real^N->bool) SUBSET moi_fsa_vs f` THEN SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "FH" (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `moi_fsa_vs (f:real^N->bool) DIFF moi_fsa_vs e = {x}` THEN
        UNDISCH_TAC `moi_fsa_vs (f:real^N->bool) SUBSET moi_fsa_vs r` THEN SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      USE_THEN "XH" (MP_TAC o C MP
        (ASSUME `(x:real^N) IN moi_fsa_vs r DIFF moi_fsa_vs e`) o SPEC `x:real^N`) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        concl th = `f = convex hull ((x:real^N) INSERT moi_fsa_vs e)`)) THEN
      SUBGOAL_THEN `aff_dim (convex hull ((x:real^N) INSERT moi_fsa_vs e)) = &2`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`moi_fsa_vs (r:real^N->bool)`; `(x:real^N) INSERT moi_fsa_vs e`]
          MOI_FTD_SUBHULL_DIM_GEN) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [ACCEPT_TAC(CONJUNCT1(MATCH_MP MOI_FSA_VS
              (CONJ (ASSUME `simplicial_complex (c:(real^N->bool)->bool)`)
                    (ASSUME `(r:real^N->bool) IN c`))));
            UNDISCH_TAC `(x:real^N) IN moi_fsa_vs r DIFF moi_fsa_vs e` THEN
            UNDISCH_TAC `moi_fsa_vs (e:real^N->bool) SUBSET moi_fsa_vs r` THEN SET_TAC[]];
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "RH" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC HULL_MONO THEN
        UNDISCH_TAC `(x:real^N) IN moi_fsa_vs r DIFF moi_fsa_vs e` THEN
        UNDISCH_TAC `moi_fsa_vs (e:real^N->bool) SUBSET moi_fsa_vs r` THEN SET_TAC[];
        USE_THEN "EH" (fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "XH" (fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(MP (SPEC `x:real^N` th)
      (ASSUME `(x:real^N) IN moi_fsa_vs r DIFF moi_fsa_vs e`))))) THEN
    USE_THEN "XH" (fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(MP (SPEC `y:real^N` th)
      (ASSUME `(y:real^N) IN moi_fsa_vs r DIFF moi_fsa_vs e`))))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
       lhs (concl th) = `convex hull ((x:real^N) INSERT moi_fsa_vs e)`)) THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN moi_fsa_vs r DIFF moi_fsa_vs e` THEN
    UNDISCH_TAC `(y:real^N) IN moi_fsa_vs r DIFF moi_fsa_vs e` THEN
    UNDISCH_TAC `(y:real^N) INSERT moi_fsa_vs e = x INSERT moi_fsa_vs e` THEN SET_TAC[];
    ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF; ARITH]]);;

let MOI_FZ2_SURF_EDGE2 = prove
 (`!c (b:real^N->bool) e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\
     e IN c /\ aff_dim e = &1 /\ e SUBSET b
     ==> {f | f IN c /\ aff_dim f = &2 /\ f SUBSET b /\ e SUBSET f} HAS_SIZE 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `b:real^N->bool` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{s | s IN c /\ s SUBSET b}:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FSA_CM_EDGE2) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* L o d1 = 0. *)

let MOI_FZ2_L_D1 = prove
 (`!c (z:(real^N->bool)->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ z SUBSET moi_fz2_sk c 1
     ==> moi_fz2_l c (moi_fz2_d1 c z) = {}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE) THEN
  SUBGOAL_THEN
   `!tt:(real^N->bool)->bool.
      tt SUBSET moi_fz2_sk c 2 /\
      (!e. e IN z ==> EVEN (CARD {f | f IN tt /\ e SUBSET f}))
      ==> EVEN (CARD {f | f IN moi_fz2_d1 c z /\ f IN tt})`
  (LABEL_TAC "PAR") THENL
   [X_GEN_TAC `tt:(real^N->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{f | f IN moi_fz2_d1 (c:(real^N->bool)->bool) z /\ f IN tt} =
      {f | f IN tt /\ ODD (CARD {e | e IN z /\
                                    (\e f. e IN moi_fz2_sk c 1 /\ e SUBSET f) e f})}`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_fz2_d1; moi_fz2_pm; EXTENSION; IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FZ2_DOUBLE_EVEN THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET];
      ASM_MESON_TAC[FINITE_SUBSET];
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N->bool.
      (!e. e IN z /\ e SUBSET x
           ==> EVEN (CARD {f | f IN c /\ aff_dim f = &2 /\ f SUBSET x /\ e SUBSET f}))
      ==> EVEN (CARD {a | a IN moi_fz2_d1 c z /\ a IN moi_fz2_sk c 2 /\ a SUBSET x})`
  (LABEL_TAC "PX") THENL
   [X_GEN_TAC `x:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "PAR" (MP_TAC o SPEC `{f | f IN moi_fz2_sk c 2 /\ f SUBSET (x:real^N->bool)}`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(e:real^N->bool) SUBSET x` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; moi_fz2_sk] THEN MESON_TAC[];
      SUBGOAL_THEN `{f | (f IN moi_fz2_sk c 2 /\ f SUBSET x) /\ (e:real^N->bool) SUBSET f} = {}`
      SUBST1_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES; EVEN]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN z ==> e IN c /\ aff_dim e = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:(real^N->bool)->bool) SUBSET moi_fz2_sk c 1` THEN
    REWRITE_TAC[moi_fz2_sk; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fz2_l; moi_fz2_pm; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  X_GEN_TAC `y:(real^N->bool)+(real^N->bool)` THEN
  REWRITE_TAC[moi_fz2_ly; IN_UNION; IN_IMAGE; GSYM NOT_EVEN] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `~EVEN (CARD {a | a IN moi_fz2_d1 c z /\
                               moi_fz2_lr c a (y:(real^N->bool)+(real^N->bool))})` THEN
  ASM_REWRITE_TAC[MOI_FZ2_LR] THEN
  USE_THEN "PX" MATCH_MP_TAC THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`; `e:real^N->bool`]
      MOI_FZ2_TET_EDGE2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(x:real^N->bool) IN moi_fz2_sk c 3` THEN
      REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN SIMP_TAC[];
      SIMP_TAC[HAS_SIZE; ARITH]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`; `e:real^N->bool`]
      MOI_FZ2_SURF_EDGE2) THEN
    ASM_SIMP_TAC[HAS_SIZE; ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* Dual connectivity.  A PL 2-sphere or 2-ball minus finitely many          *)
(* points is connected; in a finite family of compact sets whose union      *)
(* minus a finite set is connected, closure under meeting off that set      *)
(* gives everything; the triangles of a vertex link are connected through   *)
(* shared edges; the tetrahedra of a finite connected cm_wb 3 are connected *)
(* through shared triangles (MOI_FRN_TOUCH_CLOSED).                          *)
(* ------------------------------------------------------------------------- *)

let MOI_FZ2_CONVEX_DIFF_CONN = prove
 (`!(k:real^N->bool) g.
     convex k /\ &2 <= aff_dim k /\ FINITE g ==> connected (k DIFF g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONVEX_DIFF_COUNTABLE THEN
  ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; COLLINEAR_AFF_DIM] THEN ASM_INT_ARITH_TAC);;

let MOI_FZ2_HOMEO_DIFF_CONN = prove
 (`!(k:real^N->bool) (p:real^N->bool) f g fin.
     homeomorphism (k,p) (f,g) /\ FINITE fin /\
     (!h. FINITE h ==> connected (k DIFF h))
     ==> connected (p DIFF fin)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p DIFF fin = IMAGE (f:real^N->real^N) (k DIFF IMAGE g (fin INTER p))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `homeomorphism (k,p) (f:real^N->real^N,g)` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM]; SET_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_SIMP_TAC[FINITE_INTER]]);;

(* The relative frontier of a 3-simplex minus finitely many points. *)

let MOI_FZ2_SIMPLEX3_RF_CONN = prove
 (`!(k:real^N->bool) h.
     &3 simplex k /\ FINITE h ==> connected (relative_frontier k DIFF h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `FINITE (S:real^N->bool) /\ CARD S = 4` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (convex hull S) =
                UNIONS {convex hull (S DELETE u) | u | u IN (S:real^N->bool)}`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON; POLYHEDRON_CONVEX_HULL] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_GSPEC] THEN
  SUBGOAL_THEN `{x | ?u. u IN S /\ x IN convex hull (S DELETE u)} DIFF h =
                UNIONS {convex hull (S DELETE u) DIFF h | u | u IN (S:real^N->bool)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS_PAIRWISE THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FZ2_CONVEX_DIFF_CONN THEN ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MP_TAC(ISPECL [`S:real^N->bool`; `S DELETE (u:real^N)`] MOI_FTD_SUBHULL_DIM_GEN) THEN
    ASM_REWRITE_TAC[DELETE_SUBSET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CARD_DELETE] THEN CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `w:real^N = u` THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `?a b:real^N. a IN S /\ b IN S /\ ~(a = b) /\ ~(a = u) /\ ~(a = w) /\
                             ~(b = u) /\ ~(b = w)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(S DELETE (u:real^N) DELETE w) HAS_SIZE 2` MP_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; CARD_DELETE; FINITE_DELETE; IN_DELETE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] SUBSET convex hull (S DELETE u) INTER
                convex hull (S DELETE w)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTER; SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `INFINITE (segment[a:real^N,b] DIFF h)` MP_TAC THENL
   [MATCH_MP_TAC INFINITE_DIFF_FINITE THEN ASM_REWRITE_TAC[INFINITE; FINITE_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC(MESON[FINITE_EMPTY] `!s:real^N->bool. s = {} ==> FINITE s`) THEN
  ASM SET_TAC[]);;

let MOI_FZ2_CONVEX_INFINITE = prove
 (`!s:real^N->bool. convex s /\ &1 <= aff_dim s ==> INFINITE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a b:real^N. a IN s /\ b IN s /\ ~(a = b)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `s:real^N->bool = {} \/ ?a. s = {a}` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN UNDISCH_TAC `&1 <= aff_dim (s:real^N->bool)` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (segment[a:real^N,b])` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT];
    ASM_REWRITE_TAC[FINITE_SEGMENT]]);;

(* Closure under meeting off a finite set. *)

let MOI_FZ2_CLOSED_DCONN = prove
 (`!(tt:(real^N->bool)->bool) v0 Z.
     FINITE tt /\ (!s. s IN tt ==> compact s /\ INFINITE s) /\ FINITE v0 /\
     connected (UNIONS tt DIFF v0) /\ Z SUBSET tt /\ ~(Z = {}) /\
     (!s s'. s IN Z /\ s' IN tt /\ ~(s INTER s' SUBSET v0) ==> s' IN Z)
     ==> Z = tt`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!z t:(real^N->bool)->bool. z SUBSET t /\ t DIFF z = {}
                          ==> z = t`) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `connected (UNIONS tt DIFF v0:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`UNIONS (Z:(real^N->bool)->bool)`;
                        `UNIONS (tt DIFF Z:(real^N->bool)->bool)`] THEN
  SUBGOAL_THEN `FINITE (Z:(real^N->bool)->bool) /\ FINITE (tt DIFF Z:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN tt ==> ~(s DIFF v0 = {})` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `INFINITE (s DIFF v0:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC INFINITE_DIFF_FINITE THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[INFINITE; FINITE_EMPTY]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED; SUBSET];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED; IN_DIFF];
    ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIONS; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(s':real^N->bool) IN Z` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_TAC `s:real^N->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(Z:(real^N->bool)->bool = {})`)) THEN
    SUBGOAL_THEN `~((s:real^N->bool) DIFF v0 = {})` MP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]];
    FIRST_X_ASSUM(X_CHOOSE_TAC `s:real^N->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(tt DIFF Z:(real^N->bool)->bool = {})`)) THEN
    SUBGOAL_THEN `~((s:real^N->bool) DIFF v0 = {})` MP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]]]);;

(* Vertex links: purity, connectivity off the vertices, dual connectivity. *)

let MOI_FZ2_LINK_PURE = prove
 (`!c (v:real^N) s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ {v} IN c /\
     s IN simplicial_link c v /\ ~(s = {})
     ==> ?s'. s' IN simplicial_link c v /\ aff_dim s' = &2 /\ s SUBSET s'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`] MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull ((v:real^N) INSERT s)`]
    MOI_FBC_CMWB3_PURE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `r:real^N->bool`] MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
      MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `aff_dim (r:real^N->bool) = &3` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`; `s':real^N->bool`]
      MOI_FM3_LINK_JOIN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `convex hull ((v:real^N) INSERT s) SUBSET r` THEN ASM_REWRITE_TAC[]]);;

let MOI_FZ2_LINK_CONN = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ {v} IN c
     ==> FINITE {w | {w} IN simplicial_link c v} /\
         connected (UNIONS (simplicial_link c v) DIFF {w | {w} IN simplicial_link c v})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {w:real^N | {w} IN simplicial_link c v}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^N. {w}`; `simplicial_link c (v:real^N)`] FINITE_IMAGE_INJ) THEN
    ASM_SIMP_TAC[MOI_FM3_LINK_FINITE] THEN ANTS_TAC THENL [SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link c (v:real^N))) \/
                pl_ball 2 (UNIONS (simplicial_link c v))` MP_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_sphere; pl_ball; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_FZ2_HOMEO_DIFF_CONN THENL
   [MAP_EVERY EXISTS_TAC [`relative_frontier k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FZ2_SIMPLEX3_RF_CONN THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FZ2_CONVEX_DIFF_CONN THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX; INT_LE_REFL]]);;

let MOI_FZ2_LINK_DCONN = prove
 (`!c (v:real^N) Z.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ {v} IN c /\
     Z SUBSET {s | s IN simplicial_link c v /\ aff_dim s = &2} /\ ~(Z = {}) /\
     (!s s'. s IN Z /\ s' IN simplicial_link c v /\ aff_dim s' = &2 /\
             aff_dim (s INTER s') = &1 ==> s' IN Z)
     ==> Z = {s | s IN simplicial_link c v /\ aff_dim s = &2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (simplicial_link c (v:real^N)) /\
                FINITE (simplicial_link c v)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_LINK_SC) THEN
    ASM_SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FZ2_LINK_CONN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FZ2_CLOSED_DCONN THEN
  EXISTS_TAC `{w:real^N | {w} IN simplicial_link c v}` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FZ2_CONVEX_INFINITE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; INT_ARITH_TAC]];
    SUBGOAL_THEN `UNIONS {s | s IN simplicial_link c v /\ aff_dim s = &2} =
                  UNIONS (simplicial_link c (v:real^N))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_FZ2_LINK_PURE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s':real^N->bool` THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s':real^N->bool = s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `aff_dim:(real^N->bool)->int`)) (concl th) &&
      is_forall (concl th))) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^N->bool) IN simplicial_link c v /\ aff_dim s = &2` STRIP_ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s INTER s') face_of (s:real^N->bool) /\ s INTER s' IN simplicial_link c v`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `s:real^N->bool`; `s':real^N->bool`]
        MOI_FM3_LF_INTER) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (s INTER s':real^N->bool) < &2` ASSUME_TAC THENL
     [SUBGOAL_THEN `aff_dim (s INTER s':real^N->bool) < aff_dim s` MP_TAC THENL
       [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[MOI_FM3_LF_CONVEX];
          DISCH_TAC THEN
          SUBGOAL_THEN `(s:real^N->bool) SUBSET s'` ASSUME_TAC THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `~(s':real^N->bool = s)` THEN REWRITE_TAC[] THEN
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
          EXISTS_TAC `simplicial_link c (v:real^N)` THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `!x:int. ~(x = -- &1) /\ ~(x = &0) /\ x < &2 /\ -- &1 <= x
                                    ==> x = &1`) THEN
    ASM_REWRITE_TAC[AFF_DIM_GE; AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(s INTER s' SUBSET {w:real^N | {w} IN simplicial_link c v})` THEN
      ASM_REWRITE_TAC[EMPTY_SUBSET];
      DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN
      UNDISCH_TAC `~(s INTER s' SUBSET {w:real^N | {w} IN simplicial_link c v})` THEN
      UNDISCH_TAC `(s INTER s':real^N->bool) IN simplicial_link c v` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* Tetrahedra over adjacent link triangles share a triangle. *)

let MOI_FZ2_TET_ADJ = prove
 (`!c (v:real^N) s1 s2.
     lf_simplicial_complex c /\ {v} IN c /\
     s1 IN simplicial_link c v /\ s2 IN simplicial_link c v /\
     aff_dim s1 = &2 /\ aff_dim s2 = &2 /\ aff_dim (s1 INTER s2) = &1
     ==> aff_dim (convex hull (v INSERT s1) INTER convex hull (v INSERT s2)) = &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (simplicial_link c (v:real^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_LINK_SC) THEN
    ASM_SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1:real^N->bool = s2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ((s2:real^N->bool) INTER s2) = &1` THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1 INTER s2:real^N->bool) IN simplicial_link c v` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s1:real^N->bool` THEN
    ASM_MESON_TAC[MOI_FM3_LF_INTER];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; t]
    MOI_FM3_LINK_JOIN)) [`s1:real^N->bool`; `s2:real^N->bool`; `s1 INTER s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INT_ARITH `!x:int. &2 <= x /\ x < &3 ==> x = &2`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `aff_dim (convex hull ((v:real^N) INSERT (s1 INTER s2)))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[SUBSET_INTER] THEN
    CONJ_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s1 INTER s2:real^N->bool`]
      MOI_FM3_LINK_JOIN_SUBSET) THEN
    ASM_MESON_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(convex hull ((v:real^N) INSERT s1) = convex hull (v INSERT s2))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FM3_LINK_JOIN_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (convex hull ((v:real^N) INSERT s1)) = &3` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX];
    ASM_MESON_TAC[MOI_FM3_LF_INTER];
    DISCH_TAC THEN
    UNDISCH_TAC `~(convex hull ((v:real^N) INSERT s1) = convex hull (v INSERT s2))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Dual connectivity of finite connected combinatorial 3-manifolds. *)

let MOI_FZ2_DCONN3 = prove
 (`!c Z.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ connected (UNIONS c) /\
     Z SUBSET moi_fz2_sk c 3 /\ ~(Z = {}) /\
     (!t t'. t IN Z /\ t' IN moi_fz2_sk c 3 /\ aff_dim (t INTER t') = &2 ==> t' IN Z)
     ==> Z = moi_fz2_sk (c:(real^N->bool)->bool) 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE) THEN
  MATCH_MP_TAC MOI_FRN_TOUCH_CLOSED THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
      INT_ARITH_TAC];
    SUBGOAL_THEN `UNIONS (moi_fz2_sk c 3) = UNIONS (c:(real^N->bool)->bool)`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_fz2_sk] THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; moi_fz2_sk; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FBC_CMWB3_PURE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &3 /\ t' IN c /\ aff_dim t' = &3`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t':real^N->bool) IN moi_fz2_sk c 3` THEN
    UNDISCH_TAC `(Z:(real^N->bool)->bool) SUBSET moi_fz2_sk c 3` THEN
    UNDISCH_TAC `(t:real^N->bool) IN Z` THEN
    REWRITE_TAC[moi_fz2_sk; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. {v} IN c /\ v IN t /\ v IN t'` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t INTER t':real^N->bool`] MOI_FM3_LF_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_FACE THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[MOI_FM3_LF_INTER];
      REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Zl = {s | s IN simplicial_link c (v:real^N) /\ aff_dim s = &2 /\
                        convex hull (v INSERT s) IN Z}` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `Zl:(real^N->bool)->bool`]
    MOI_FZ2_LINK_DCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Zl" THEN SET_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
        MOI_FM3_LINK_OPP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `s0:real^N->bool` THEN
      EXPAND_TAC "Zl" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`]
        MOI_FM3_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `t = convex hull ((v:real^N) INSERT s0)` THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `aff_dim (t:real^N->bool) = aff_dim (s0:real^N->bool) + &1` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      EXPAND_TAC "Zl" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `aff_dim:(real^N->bool)->int`)) (concl th) &&
        is_forall (concl th) && can (find_term (fun t -> t = `Z:(real^N->bool)->bool`)) (concl th))) THEN
      EXISTS_TAC `convex hull ((v:real^N) INSERT s1)` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s2:real^N->bool`]
          MOI_FM3_LINK_JOIN) THEN
        ASM_REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC;
        MATCH_MP_TAC MOI_FZ2_TET_ADJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t':real^N->bool`] MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`] MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s':real^N->bool) IN Zl` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `aff_dim (t':real^N->bool) = &3` THEN
    UNDISCH_TAC `t' = convex hull ((v:real^N) INSERT s')` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    EXPAND_TAC "Zl" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The image of L.  L of a boundary triangle is {INL r, INR b}, of          *)
(* an interior triangle {INL r, INL r'}; with dual connectivity the image   *)
(* of L contains every even subset of its target set.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_FZ2_SD3 = prove
 (`!a b d:A. ~(d = a) /\ ~(d = b) ==> moi_fz2_sd (moi_fz2_sd {a} {b}) {b,d} = {a,d}`,
  REWRITE_TAC[moi_fz2_sd] THEN SET_TAC[]);;

let MOI_FZ2_SD_PAIR = prove
 (`!a x y:A. ~(x = a) /\ ~(y = a) /\ ~(x = y)
             ==> moi_fz2_sd {a,x} {a,y} = {x,y} /\ moi_fz2_sd {x} {y} = {x,y}`,
  REWRITE_TAC[moi_fz2_sd] THEN SET_TAC[]);;

let MOI_FZ2_SD_SING = prove
 (`!x y:A. ~(x = y) ==> moi_fz2_sd {x} {y} = {x,y}`,
  REWRITE_TAC[moi_fz2_sd] THEN SET_TAC[]);;

let MOI_FZ2_FINITE_COMPS = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> FINITE (components (complex_boundary c))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_boundary] THEN
  MATCH_MP_TAC MOI_FBC_FINITE_COMPONENTS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary]]);;

let MOI_FZ2_L_SING = prove
 (`!c (f:real^N->bool).
     f IN moi_fz2_sk c 2
     ==> moi_fz2_l c {f} =
         IMAGE INL {r | r IN moi_fz2_sk c 3 /\ f SUBSET r} UNION
         IMAGE INR {b | b IN components (complex_boundary c) /\ f SUBSET b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fz2_l; moi_fz2_pm] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:(real^N->bool)+(real^N->bool)` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `ODD (CARD {a | a IN {f} /\ moi_fz2_lr c a y}) <=>
                moi_fz2_lr c (f:real^N->bool) y` SUBST1_TAC THENL
   [ASM_CASES_TAC `moi_fz2_lr c (f:real^N->bool) y` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `{a | a IN {f} /\ moi_fz2_lr c a y} = {f:real^N->bool}` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[CARD_SING; ODD; ARITH]];
      SUBGOAL_THEN `{a | a IN {f} /\ moi_fz2_lr c a y} = {}:(real^N->bool)->bool`
      SUBST1_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES; ODD]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fz2_ly; moi_fz2_lr; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[sum_DISTINCT; sum_INJECTIVE]);;

(* A boundary triangle has one tetrahedron and lies in one component. *)

let MOI_FZ2_BD_TRI = prove
 (`!c (f:real^N->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ f IN moi_fz2_sk c 2 /\
     f SUBSET complex_boundary c
     ==> ?r b. {r' | r' IN moi_fz2_sk c 3 /\ f SUBSET r'} = {r} /\
               {b' | b' IN components (complex_boundary c) /\ f SUBSET b'} = {b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->bool) IN c /\ aff_dim f = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fz2_sk; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `{r' | r' IN moi_fz2_sk c 3 /\ (f:real^N->bool) SUBSET r'} HAS_SIZE 1`
  MP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`] MOI_FTD_TRIANGLE_COFACES) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`] MOI_FTD_TRIANGLE_BOUNDARY) THEN
    ASM_REWRITE_TAC[moi_fz2_sk; HAS_SIZE; IN_ELIM_THM] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC `r:real^N->bool`) THEN EXISTS_TAC `r:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(f:real^N->bool = {})` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `connected (f:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  EXISTS_TAC `connected_component (complex_boundary c) (x:real^N)` THEN
  SUBGOAL_THEN `(x:real^N) IN complex_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_component (complex_boundary c) (x:real^N) IN
                components (complex_boundary c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) SUBSET connected_component (complex_boundary c) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `b:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`complex_boundary c:real^N->bool`; `b:real^N->bool`;
                   `connected_component (complex_boundary c) (x:real^N)`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> (p <=> ~q) ==> q`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^N` THEN
    ASM_MESON_TAC[SUBSET];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* An interior triangle r INTER r' gives {INL r, INL r'}. *)

let MOI_FZ2_INT_TRI = prove
 (`!c (r:real^N->bool) r'.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     r IN moi_fz2_sk c 3 /\ r' IN moi_fz2_sk c 3 /\ aff_dim (r INTER r') = &2
     ==> r INTER r' IN moi_fz2_sk c 2 /\ moi_fz2_l c {r INTER r'} = {INL r, INL r'}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `(r INTER r':real^N->bool) IN c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_MESON_TAC[MOI_FM3_LF_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r:real^N->bool = r')` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ((r':real^N->bool) INTER r') = &2` THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r INTER r':real^N->bool`]
    MOI_FTD_TRIANGLE_COFACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{q | q IN c /\ aff_dim q = &3 /\ (r INTER r':real^N->bool) SUBSET q} =
                {r, r'}` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{r:real^N->bool, r'} SUBSET
                  {q | q IN c /\ aff_dim q = &3 /\ r INTER r' SUBSET q}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`{r:real^N->bool, r'}`;
                   `{q | q IN c /\ aff_dim q = &3 /\ r INTER r' SUBSET (q:real^N->bool)}`]
      CARD_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((r INTER r':real^N->bool) SUBSET complex_boundary c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r INTER r':real^N->bool`]
      MOI_FTD_TRIANGLE_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r INTER r':real^N->bool`] MOI_FZ2_L_SING) THEN
  ASM_REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `{q | (q IN c /\ aff_dim q = &3) /\ (r INTER r':real^N->bool) SUBSET q} = {r, r'} /\
    {b | b IN components (complex_boundary c) /\ r INTER r' SUBSET b} = {}`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `{q | q IN c /\ aff_dim q = &3 /\ (r INTER r':real^N->bool) SUBSET q} =
                   {r, r'}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET_TRANS]];
    REWRITE_TAC[IMAGE_CLAUSES; UNION_EMPTY]]);;

let MOI_FZ2_COMP_TRI = prove
 (`!c (b:real^N->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c)
     ==> ?f. f IN moi_fz2_sk c 2 /\ f SUBSET complex_boundary c /\ f SUBSET b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `(x:real^N) IN complex_boundary c` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [complex_boundary] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->bool` THEN
  SUBGOAL_THEN `(f:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [REWRITE_TAC[complex_boundary] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `f:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `complex_boundary c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_MESON_TAC[MOI_FM3_LF_CONVEX];
    ASM SET_TAC[]]);;

(* Every even subset of the target of L is in its image. *)

let MOI_FZ2_IMAGE_L = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ connected (UNIONS c) /\
     ~(components (complex_boundary c) = {})
     ==> !x. x SUBSET moi_fz2_ly c /\ EVEN (CARD x)
             ==> x IN IMAGE (moi_fz2_l c) {u | u SUBSET moi_fz2_sk c 2}`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_MAPS_SD) THEN
  ABBREV_TAC `G = IMAGE (moi_fz2_l c) {u | u SUBSET moi_fz2_sk (c:(real^N->bool)->bool) 2}` THEN
  SUBGOAL_THEN `!u v. u IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool) /\ v IN G ==> moi_fz2_sd u v IN G`
  (LABEL_TAC "GSD") THENL
   [EXPAND_TAC "G" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FZ2_IMAGE_SD THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[MOI_FZ2_POW_SD];
    ALL_TAC] THEN
  SUBGOAL_THEN `({}:((real^N->bool)+(real^N->bool))->bool) IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[EMPTY_SUBSET; moi_fz2_l; MOI_FZ2_PM_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f. f IN moi_fz2_sk c 2 ==> moi_fz2_l c {f:real^N->bool} IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool)`
  (LABEL_TAC "GS") THENL
   [EXPAND_TAC "G" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r r':real^N->bool. r IN moi_fz2_sk c 3 /\ r' IN moi_fz2_sk c 3
                        ==> moi_fz2_sd {INL r} {INL r'} IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool)`
  (LABEL_TAC "G2") THENL
   [X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `{r':real^N->bool | r' IN moi_fz2_sk c 3 /\
                                       moi_fz2_sd {INL r} {INL r'} IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool)}`] MOI_FZ2_DCONN3) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `r:real^N->bool` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; MOI_FZ2_SD];
        MAP_EVERY X_GEN_TAC [`r1:real^N->bool`; `r2:real^N->bool`] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r1:real^N->bool`; `r2:real^N->bool`]
          MOI_FZ2_INT_TRI) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `~(r1:real^N->bool = r2)` ASSUME_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `aff_dim ((r2:real^N->bool) INTER r2) = &2` THEN
          REWRITE_TAC[INTER_IDEMPOT] THEN
          UNDISCH_TAC `(r2:real^N->bool) IN moi_fz2_sk c 3` THEN
          REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          INT_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN
         `moi_fz2_sd {(INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) r} {INL r2} =
          moi_fz2_sd (moi_fz2_sd {INL r} {INL r1})
                     ((INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) r1 INSERT {INL r2})`
        SUBST1_TAC THENL
         [SUBGOAL_THEN `~((INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) r1 = INL r2)`
          MP_TAC THENL [ASM_REWRITE_TAC[sum_INJECTIVE]; ALL_TAC] THEN
          REWRITE_TAC[moi_fz2_sd] THEN SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "GSD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          can (find_term (fun t -> t = `moi_fz2_l (c:(real^N->bool)->bool)`)) (concl th))) THEN
        USE_THEN "GS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `r':real^N->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `{r':real^N->bool | r' IN moi_fz2_sk c 3 /\
                                     moi_fz2_sd {INL r} {INL r'} IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool)} = moi_fz2_sk c 3` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r b:real^N->bool. r IN moi_fz2_sk c 3 /\ b IN components (complex_boundary c)
                       ==> {INL r, INR b} IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool)`
  (LABEL_TAC "G5") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FZ2_COMP_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`] MOI_FZ2_BD_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `rf:real^N->bool` (X_CHOOSE_THEN `bf:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `bf:real^N->bool = b /\ (rf:real^N->bool) IN moi_fz2_sk c 3` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fz2_l c {f} =
                  {(INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) rf, INR b}`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[MOI_FZ2_L_SING] THEN REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{(INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) r, INR b} =
      moi_fz2_sd (moi_fz2_sd {INL r} {INL rf}) {INL rf, INR b}`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FZ2_SD3 THEN
      REWRITE_TAC[sum_DISTINCT];
      ALL_TAC] THEN
    USE_THEN "GSD" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "G2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term (fun t -> t = `moi_fz2_l (c:(real^N->bool)->bool)`)) (concl th))) THEN
      USE_THEN "GS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r0:real^N->bool. r0 IN moi_fz2_sk c 3` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `b:real^N->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(components (complex_boundary (c:(real^N->bool)->bool)) = {})`)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FZ2_COMP_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`] MOI_FZ2_BD_TRI) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN moi_fz2_ly c /\ y2 IN moi_fz2_ly c /\ ~(y1 = y2) ==> {y1, y2} IN (G:(((real^N->bool)+(real^N->bool))->bool)->bool)`
  (LABEL_TAC "PR") THENL
   [REWRITE_TAC[moi_fz2_ly; IN_UNION; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ASM_REWRITE_TAC[sum_INJECTIVE; sum_DISTINCT] THEN REPEAT DISCH_TAC THENL
     [MP_TAC(ISPECL [`(INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) x`;
                     `(INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) x'`] MOI_FZ2_SD_SING) THEN
      ASM_REWRITE_TAC[sum_INJECTIVE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "G2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "G5" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[INSERT_AC] THEN USE_THEN "G5" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`(INL:(real^N->bool)->(real^N->bool)+(real^N->bool)) r0`;
                     `(INR:(real^N->bool)->(real^N->bool)+(real^N->bool)) x`;
                     `(INR:(real^N->bool)->(real^N->bool)+(real^N->bool)) x'`] MOI_FZ2_SD_PAIR) THEN
      ASM_REWRITE_TAC[sum_INJECTIVE; sum_DISTINCT] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      USE_THEN "GSD" MATCH_MP_TAC THEN CONJ_TAC THEN USE_THEN "G5" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(((real^N->bool)+(real^N->bool))->bool)->bool`; `moi_fz2_ly (c:(real^N->bool)->bool)`]
    MOI_FZ2_EVEN_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_fz2_ly] THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; MOI_FZ2_FINITE_COMPS];
    EXPAND_TAC "G" THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Euler bound n0 + n2 + 1 <= n1 + n3 + m and the count.                *)
(* 2 chi(c) = chi(boundary) = sum of the component characteristics, each at *)
(* most 2 and at most 1 for the non-sphere; then |Z^1| >= 2 |B^1|.           *)
(* ------------------------------------------------------------------------- *)

let MOI_FZ2_EULER_BOUND = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     (?b. b IN components (complex_boundary c) /\ ~pl_sphere 2 b)
     ==> CARD (moi_fz2_sk c 0) + CARD (moi_fz2_sk c 2) + 1 <=
         CARD (moi_fz2_sk c 1) + CARD (moi_fz2_sk c 3) +
         CARD (components (complex_boundary c))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC(el 2 cs) THEN ASSUME_TAC(el 3 cs) THEN LABEL_TAC "BC" (el 4 cs)) THEN
  SUBGOAL_THEN `FINITE (components (complex_boundary (c:(real^N->bool)->bool)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FZ2_FINITE_COMPS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:real^N->bool. k IN components (complex_boundary c)
       ==> complex_euler {s | s IN c /\ s SUBSET k} <= &2 /\
           (complex_euler {s | s IN c /\ s SUBSET k} = &2 <=> pl_sphere 2 k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "BC" (STRIP_ASSUME_TAC o C MP
      (ASSUME `(k:real^N->bool) IN components (complex_boundary c)`) o SPEC `k:real^N->bool`) THEN
    MP_TAC(ISPEC `{s | s IN c /\ s SUBSET (k:real^N->bool)}` SURFACE_EULER_SPHERE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT] THEN
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler {s | s IN c /\ s SUBSET (b:real^N->bool)} <= &1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `{s | s IN c /\ s SUBSET (b:real^N->bool)}` MOI_STD_EULER_INTEGER) THEN
    SPEC_TAC(`complex_euler {s | s IN c /\ s SUBSET (b:real^N->bool)}`,`x:real`) THEN
    GEN_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`x:real`; `&2`] REAL_LT_INTEGERS) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_euler (boundary_complex c) =
    sum (components (complex_boundary c))
        (\k:real^N->bool. complex_euler {s | s IN c /\ s SUBSET k})`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (boundary_complex (c:(real^N->bool)->bool))`
    ASSUME_TAC THENL
     [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN CONJ_TAC THENL
       [REWRITE_TAC[boundary_complex] THEN MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[combinatorial_manifold]];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_S8CU_EULER_SUM th]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[boundary_complex; EXTENSION; IN_ELIM_THM] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (components (complex_boundary c))
        (\k:real^N->bool. complex_euler {s | s IN c /\ s SUBSET k}) <=
    &1 + &(CARD (components (complex_boundary c)) - 1) * &2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\k:real^N->bool. complex_euler {s | s IN c /\ s SUBSET k}`;
                   `components (complex_boundary (c:(real^N->bool)->bool))`;
                   `b:real^N->bool`] SUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ d <= z ==> d = y - x ==> y <= &1 + z`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD (components (complex_boundary (c:(real^N->bool)->bool)) DELETE
                       (b:real^N->bool))) * &2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_BOUND THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
      ASM_SIMP_TAC[CARD_DELETE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FTD_EULER_BOUNDARY) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FTD_EULER_DIM3) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CM_WB_DIM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= CARD (components (complex_boundary (c:(real^N->bool)->bool)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  UNDISCH_TAC
   `sum (components (complex_boundary c))
        (\k:real^N->bool. complex_euler {s | s IN c /\ s SUBSET k}) <=
    &1 + &(CARD (components (complex_boundary c)) - 1) * &2` THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN DISCH_TAC THEN REWRITE_TAC[moi_fz2_sk] THEN
  MATCH_MP_TAC(ARITH_RULE `2 * (a + b) + 1 <= 2 * (c + d + e) ==> a + b + 1 <= c + d + e`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c d m:real. &2 * (a - b + c - d) <= &1 + (m - &1) * &2
                     ==> &2 * (a + c) + &1 <= &2 * (b + d + m)`) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* The kernel of d0 contains {} and the vertex set. *)

let MOI_FZ2_D0_KER = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ ~(moi_fz2_v c = {})
     ==> 2 * CARD (IMAGE (moi_fz2_d0 c) {w | w SUBSET moi_fz2_v c}) <=
         2 EXP CARD (moi_fz2_v c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_MAPS_SD) THEN
  MP_TAC(ISPECL [`moi_fz2_v (c:(real^N->bool)->bool)`; `moi_fz2_d0 (c:(real^N->bool)->bool)`]
    MOI_FZ2_KERNEL_IMAGE_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
  SUBGOAL_THEN `{{}, moi_fz2_v c} SUBSET
                {w | w SUBSET moi_fz2_v c /\ moi_fz2_d0 (c:(real^N->bool)->bool) w = {}}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET; SUBSET_REFL] THENL
     [REWRITE_TAC[moi_fz2_d0; MOI_FZ2_PM_EMPTY];
      REWRITE_TAC[moi_fz2_d0; moi_fz2_pm; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      X_GEN_TAC `e:real^N->bool` THEN REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN
      ASM_CASES_TAC `(e:real^N->bool) IN c /\ aff_dim e = &1` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `1`]
        MOI_FTD_SIMPLEX_VERTEX_CARD) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `{v | v IN moi_fz2_v c /\ {v} IN c /\ v IN e} =
                    {v:real^N | {v} IN c /\ v IN e}` SUBST1_TAC THENL
       [REWRITE_TAC[moi_fz2_v; EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
        ASM_REWRITE_TAC[ARITH]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{{}, moi_fz2_v (c:(real^N->bool)->bool)}`;
                 `{w | w SUBSET moi_fz2_v c /\ moi_fz2_d0 (c:(real^N->bool)->bool) w = {}}`]
    CARD_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{w:real^N->bool | w SUBSET moi_fz2_v c}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  UNDISCH_TAC `~(moi_fz2_v (c:(real^N->bool)->bool) = {})` THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN SIMP_TAC[] THEN ARITH_TAC);;

let MOI_FZ2_LY_CARD = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> FINITE (moi_fz2_ly c) /\
         CARD (moi_fz2_ly c) =
         CARD (moi_fz2_sk c 3) + CARD (components (complex_boundary c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE_COMPS o
    CONJ (ASSUME `FINITE (c:(real^N->bool)->bool)`)) THEN
  REWRITE_TAC[moi_fz2_ly] THEN ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[sum_DISTINCT];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_SIMP_TAC[sum_INJECTIVE]);;

(* The count: some cocycle is not a coboundary. *)

let Z2_COCYCLE_NONSPHERE_BOUNDARY = prove
 (MOI_FND_COCYCLE_NONSPHERE_BOUNDARY,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_FINITE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FZ2_MAPS_SD) THEN
  SUBGOAL_THEN `~(components (complex_boundary (c:(real^N->bool)->bool)) = {})`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_fz2_v (c:(real^N->bool)->bool) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FZ2_COMP_TRI) THEN
    ASM_REWRITE_TAC[moi_fz2_sk; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`] MOI_FM3_LF_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
      INT_ARITH_TAC;
      REWRITE_TAC[moi_fz2_v] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FZ2_D0_KER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FZ2_EULER_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FZ2_LY_CARD) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fz2_sk (c:(real^N->bool)->bool) 1`; `moi_fz2_d1 (c:(real^N->bool)->bool)`]
    MOI_FZ2_KERNEL_IMAGE_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_fz2_sk (c:(real^N->bool)->bool) 2`; `moi_fz2_l (c:(real^N->bool)->bool)`]
    MOI_FZ2_KERNEL_IMAGE_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Z1 = {z | z SUBSET moi_fz2_sk c 1 /\ moi_fz2_d1 (c:(real^N->bool)->bool) z = {}}` THEN
  ABBREV_TAC `B1 = IMAGE (moi_fz2_d0 c) {w | w SUBSET moi_fz2_v (c:(real^N->bool)->bool)}` THEN
  SUBGOAL_THEN
   `CARD (IMAGE (moi_fz2_d1 c) {z | z SUBSET moi_fz2_sk c 1}) <=
    CARD {u | u SUBSET moi_fz2_sk c 2 /\ moi_fz2_l (c:(real^N->bool)->bool) u = {}}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `z:(real^N->bool)->bool` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[MOI_FZ2_L_D1] THEN REWRITE_TAC[moi_fz2_d1; MOI_FZ2_PM_SUBSET];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{u:(real^N->bool)->bool | u SUBSET moi_fz2_sk c 2}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP ((CARD (moi_fz2_sk c 3) + CARD (components (complex_boundary c))) - 1) <=
    CARD (IMAGE (moi_fz2_l c) {u | u SUBSET moi_fz2_sk (c:(real^N->bool)->bool) 2})`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(moi_fz2_ly (c:(real^N->bool)->bool) = {})` ASSUME_TAC THENL
     [REWRITE_TAC[moi_fz2_ly; EMPTY_UNION; IMAGE_EQ_EMPTY] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `moi_fz2_ly (c:(real^N->bool)->bool)` MOI_FZ2_EVEN_SUBSETS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FZ2_IMAGE_L) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_POWERSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP CARD (moi_fz2_sk (c:(real^N->bool)->bool) 0) <=
                CARD (Z1:((real^N->bool)->bool)->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP CARD (moi_fz2_sk (c:(real^N->bool)->bool) 0) *
                  2 EXP CARD (moi_fz2_sk c 2) <=
                  CARD (Z1:((real^N->bool)->bool)->bool) * 2 EXP CARD (moi_fz2_sk c 2)`
    MP_TAC THENL
     [ALL_TAC; SIMP_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `2 EXP (CARD (moi_fz2_sk (c:(real^N->bool)->bool) 1) +
                       ((CARD (moi_fz2_sk c 3) + CARD (components (complex_boundary c))) - 1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_ADD] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq (concl th) && lhs (concl th) = `2 EXP CARD (moi_fz2_sk (c:(real^N->bool)->bool) 1)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq (concl th) && lhs (concl th) = `2 EXP CARD (moi_fz2_sk (c:(real^N->bool)->bool) 2)`)) THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (B1:((real^N->bool)->bool)->bool) < CARD (Z1:((real^N->bool)->bool)->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(2 EXP CARD (moi_fz2_sk (c:(real^N->bool)->bool) 0) = 0)` MP_TAC THENL
     [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    UNDISCH_TAC `2 * CARD (B1:((real^N->bool)->bool)->bool) <=
                 2 EXP CARD (moi_fz2_sk (c:(real^N->bool)->bool) 0)` THEN
    UNDISCH_TAC `2 EXP CARD (moi_fz2_sk (c:(real^N->bool)->bool) 0) <=
                 CARD (Z1:((real^N->bool)->bool)->bool)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:(real^N->bool)->bool. z IN Z1 /\ ~(z IN B1)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~((s:((real^N->bool)->bool)->bool) SUBSET t)
                            ==> ?x. x IN s /\ ~(x IN t)`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Z1:((real^N->bool)->bool)->bool`; `B1:((real^N->bool)->bool)->bool`]
      CARD_SUBSET) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [EXPAND_TAC "B1" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_POWERSET];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `z:(real^N->bool)->bool` THEN
  UNDISCH_TAC `(z:(real^N->bool)->bool) IN Z1` THEN EXPAND_TAC "Z1" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FZ2_COCYCLE; MOI_FZ2_COBOUNDARY] THEN
  UNDISCH_TAC `~((z:(real^N->bool)->bool) IN B1)` THEN EXPAND_TAC "B1" THEN SIMP_TAC[]);;

