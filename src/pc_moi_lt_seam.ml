(* ========================================================================= *)
(* pc_moi_lt_seam: the seam half of the arc case of the cut step of the loop *)
(* theorem, Moise GTM 47 p.185-187 Cases 3-4.  Main theorem SEAM :           *)
(* |- MOI_LCUS_SEAM (pc_moi_lt_cutbstmt.ml): the disk D_2 = R1 + R0 + R2     *)
(* reglued crosswise along the double arc k, with the touching seam pushed   *)
(* apart inside the buffer w, is a normal2 disk of smaller complexity whose  *)
(* boundary loop is homotopic in w to the D_2 word.                          *)
(* Structure: the 3D push is the named statement MOI_LSM_PUSH (Part 1);      *)
(* SEAM_FROM_PUSH : |- MOI_LSM_PUSH ==> MOI_LCUS_SEAM is the 2D assembly     *)
(* (the touching map F on the model rectangle, the pushed map, its double    *)
(* image, the crossing2 charts by MOI_LC0_CROSSING2_TRANSFER and the         *)
(* boundary loop by MOI_LC0_DISK_LOOP); PUSH is proved from the crossing2    *)
(* charts along k (normalized charts, chart pushes, composite).              *)
(* ========================================================================= *)

needs "src/pc_moi_lt_cutbstmt.ml";;
needs "src/pc_moi_lt_cutb0.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the D_2 model maps and the push statement.                        *)
(*   moi_lsm_rho e: the affine involution of the model rectangle exchanging  *)
(*   its two outer parts, (x,y) -> (3-x, 1-y) in Case 3 (e) and (3-x, y) in  *)
(*   Case 4.  moi_lsm_psi e: rho on the outer parts, the identity on the     *)
(*   middle part; f o g o psi is the touching disk D_2 before the push.      *)
(*   MOI_LSM_PUSH: for the double arc k of the model, a family hh of maps  *)
(*   of the manifold, the identity at                                        *)
(*   time 0 and off a closed set S around k (S misses the other double       *)
(*   components and the middle line of R0, and meets the boundary only in   *)
(*   w), keeping the boundary and S; at time 1 it is PL and injective, it   *)
(*   moves k off the image of f, and moves every point of the seam-1 side    *)
(*   (R0 left of x = 3/2, and R2) either not at all or off the image.        *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_rho = new_definition
 `moi_lsm_rho e (z:real^2) = vector[&3 - z$1; if e then &1 - z$2 else z$2]:real^2`;;

let moi_lsm_psi = new_definition
 `moi_lsm_psi e (z:real^2) = if z$1 <= &1 \/ &2 <= z$1 then moi_lsm_rho e z else z`;;

let MOI_LSM_PUSH =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N) w (g:real^2->real^2) e k.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal2_disk c f /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE f (relative_frontier std_triangle) SUBSET w /\
     moi_lcus_model c f g e /\
     k IN components (moi_lt_double_image f) /\
     {x | x IN std_triangle /\ f x IN k} =
     IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
              segment[vector[&2; &0],vector[&2; &1]])
     ==> ?(hh:real^1->real^N->real^N) S.
           closed S /\ k SUBSET S /\
           DISJOINT S (moi_lt_double_image f DIFF k) /\
           DISJOINT S (IMAGE (f o g) (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]])) /\
           S INTER complex_boundary c SUBSET w /\
           (\z. hh (fstcart z) (sndcart z)) continuous_on
             (interval[vec 0,vec 1] PCROSS UNIONS c) /\
           (!z. z IN UNIONS c ==> hh (vec 0) z = z) /\
           (!t z. t IN interval[vec 0,vec 1] /\ z IN UNIONS c
                  ==> hh t z IN UNIONS c /\
                      (hh t z IN complex_boundary c <=> z IN complex_boundary c) /\
                      (~(z IN S) ==> hh t z = z) /\
                      (z IN S ==> hh t z IN S)) /\
           pl_map_on (UNIONS c) (hh (vec 1)) /\
           (!z z'. z IN UNIONS c /\ z' IN UNIONS c /\ hh (vec 1) z = hh (vec 1) z'
                   ==> z = z') /\
           (!x. x IN IMAGE g (interval[vector[&1; &0],vector[&3 / &2; &1]] UNION
                              interval[vector[&2; &0],vector[&3; &1]])
                ==> hh (vec 1) (f x) = f x \/
                    ~(hh (vec 1) (f x) IN IMAGE f std_triangle)) /\
           (!y. y IN k ==> ~(hh (vec 1) y IN IMAGE f std_triangle))`;;

if not (type_of MOI_LSM_PUSH = bool_ty && frees MOI_LSM_PUSH = [])
then failwith "MOI_LSM_PUSH: not a closed boolean";;

(* ------------------------------------------------------------------------- *)
(* Part 2: the model rectangle and the involution rho.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_IN_MR = prove
 (`!z:real^2. z IN moi_lcus_mr <=> &0 <= z$1 /\ z$1 <= &3 /\ &0 <= z$2 /\ z$2 <= &1`,
  REWRITE_TAC[moi_lcus_mr; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_LSM_MR_EQ = prove
 (`moi_lcus_mr = interval[vector[&0; &0],vector[&3; &1]]:real^2->bool`,
  REWRITE_TAC[moi_lcus_mr; MOI_LC0_VEC0]);;

let MOI_LSM_MR_FACTS = prove
 (`polytope moi_lcus_mr /\ convex moi_lcus_mr /\ compact moi_lcus_mr /\
   bounded moi_lcus_mr /\ ~(interior moi_lcus_mr = {}) /\
   relative_frontier moi_lcus_mr = frontier moi_lcus_mr /\
   frontier moi_lcus_mr =
   {z:real^2 | z IN moi_lcus_mr /\ (z$1 = &0 \/ z$1 = &3 \/ z$2 = &0 \/ z$2 = &1)} /\
   moi_lcus_mr DIFF frontier moi_lcus_mr =
   {z:real^2 | &0 < z$1 /\ z$1 < &3 /\ &0 < z$2 /\ z$2 < &1}`,
  MP_TAC(SPECL [`&0`; `&3`] MOI_LC0_RECT_FACTS) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &3`; GSYM MOI_LSM_MR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; MOI_LSM_IN_MR] THEN
  CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

(* The chords. *)

let MOI_LSM_CHORDS = prove
 (`segment[vector[&1; &0],vector[&1; &1]] = {z:real^2 | z$1 = &1 /\ &0 <= z$2 /\ z$2 <= &1} /\
   segment[vector[&2; &0],vector[&2; &1]] = {z:real^2 | z$1 = &2 /\ &0 <= z$2 /\ z$2 <= &1} /\
   segment[vector[&3 / &2; &0],vector[&3 / &2; &1]] =
   {z:real^2 | z$1 = &3 / &2 /\ &0 <= z$2 /\ z$2 <= &1}`,
  SIMP_TAC[MOI_LC0_VSEG; REAL_POS]);;

let MOI_LSM_CHORDS_IN_MR = prove
 (`!z:real^2. z IN moi_lcus_mr
              ==> (z IN segment[vector[&1; &0],vector[&1; &1]] UNION
                        segment[vector[&2; &0],vector[&2; &1]] <=>
                   z$1 = &1 \/ z$1 = &2)`,
  REWRITE_TAC[MOI_LSM_CHORDS; IN_UNION; IN_ELIM_THM; MOI_LSM_IN_MR] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

(* The involution rho. *)

let MOI_LSM_RHO = prove
 (`!e (z:real^2).
     moi_lsm_rho e z $1 = &3 - z$1 /\
     moi_lsm_rho e z $2 = (if e then &1 - z$2 else z$2) /\
     moi_lsm_rho e (moi_lsm_rho e z) = z /\
     (moi_lsm_rho e z IN moi_lcus_mr <=> z IN moi_lcus_mr)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_rho; VECTOR_2; MOI_LSM_IN_MR] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LSM_RHO_AFFINE = prove
 (`!e. ?l (y:real^2). linear l /\ !z. moi_lsm_rho e z = l z + y`,
  GEN_TAC THEN
  EXISTS_TAC `\z:real^2. vector[--(z$1); if e then --(z$2) else z$2]:real^2` THEN
  EXISTS_TAC `vector[&3; if e then &1 else &0]:real^2` THEN
  BOOL_CASES_TAC `e:bool` THEN
  REWRITE_TAC[linear; moi_lsm_rho; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_LSM_RHO_PL = prove
 (`!e s:real^2->bool. locally_polyhedral s ==> pl_map_on s (moi_lsm_rho e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:bool` MOI_LSM_RHO_AFFINE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^2` (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\z:real^2. l z + (y:real^2)` THEN
  ASM_SIMP_TAC[PL_MAP_ON_AFFINE]);;

let MOI_LSM_RHO_CONTINUOUS = prove
 (`!e s:real^2->bool. moi_lsm_rho e continuous_on s`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `e:bool` MOI_LSM_RHO_AFFINE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^2` (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_lsm_rho e = \z:real^2. l z + (y:real^2)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST]);;

(* rho exchanges the two outer parts and the two chords, and maps the   *)
(* frontier of the model onto itself.                                    *)

let MOI_LSM_RHO_PARTS = prove
 (`!e (z:real^2).
     z IN moi_lcus_mr
     ==> (moi_lsm_rho e z $1 <= &1 <=> &2 <= z$1) /\
         (&2 <= moi_lsm_rho e z $1 <=> z$1 <= &1) /\
         (moi_lsm_rho e z $1 = &1 <=> z$1 = &2) /\
         (moi_lsm_rho e z $1 = &2 <=> z$1 = &1) /\
         (moi_lsm_rho e z IN frontier moi_lcus_mr <=> z IN frontier moi_lcus_mr)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LSM_MR_FACTS; IN_ELIM_THM; MOI_LSM_RHO] THEN
  REWRITE_TAC[MOI_LSM_IN_MR] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* The chord relation of the model in terms of rho. *)

let MOI_LSM_RHO_CHORDS = prove
 (`!(f:real^2->real^N) (g:real^2->real^2) e z.
     (!t. &0 <= t /\ t <= &1
          ==> f (g (vector[&1; t])) = f (g (vector[&2; if e then &1 - t else t]))) /\
     z IN moi_lcus_mr /\ (z$1 = &1 \/ z$1 = &2)
     ==> f (g (moi_lsm_rho e z)) = f (g z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LSM_IN_MR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R") STRIP_ASSUME_TAC) THENL
   [(* z on chord 1: rho z = (2, sigma y) *)
    USE_THEN "R" (MP_TAC o SPEC `(z:real^2)$2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `vector[&1; (z:real^2)$2] = z /\
                  vector[&2; if e then &1 - (z:real^2)$2 else z$2] = moi_lsm_rho e z`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[moi_lsm_rho; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      ASM_REAL_ARITH_TAC;
      MESON_TAC[]];
    (* z on chord 2: rho z = (1, sigma y) *)
    USE_THEN "R" (MP_TAC o SPEC `if e then &1 - (z:real^2)$2 else z$2`) THEN
    ANTS_TAC THENL [COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `vector[&1; if e then &1 - (z:real^2)$2 else z$2] = moi_lsm_rho e z /\
                  vector[&2; if e then &1 - (if e then &1 - (z:real^2)$2 else z$2)
                             else (if e then &1 - z$2 else z$2)] = z`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[moi_lsm_rho; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    ASM_CASES_TAC `e:bool` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_LSM_MR_RELFRONT = prove
 (`relative_frontier moi_lcus_mr = frontier moi_lcus_mr`,
  REWRITE_TAC[MOI_LSM_MR_FACTS]);;

let MOI_LSM_MR_FRONTIER = prove
 (`!z:real^2. z IN frontier moi_lcus_mr <=>
              z IN moi_lcus_mr /\ (z$1 = &0 \/ z$1 = &3 \/ z$2 = &0 \/ z$2 = &1)`,
  REWRITE_TAC[MOI_LSM_MR_FACTS; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: consequences of the model.  g is a homeomorphism of the model    *)
(* onto std_triangle, boundary to boundary; the chords are exactly the      *)
(* points sent into k; rho matches the two chords under f o g; f o g is     *)
(* injective on each chord (a third preimage would appear otherwise).       *)
(* ------------------------------------------------------------------------- *)

(* Three distinct points cannot lie in a fibre of at most two points. *)

let MOI_LSM_THREE = prove
 (`!(s:A->bool) a b c.
     FINITE s /\ CARD s <= 2 /\ a IN s /\ b IN s /\ c IN s /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c)
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD {a:A,b,c} <= CARD (s:A->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {a:A,b,c} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
    UNDISCH_TAC `CARD (s:A->bool) <= 2` THEN ARITH_TAC]);;

let MOI_LSM_MODEL = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) e.
     moi_lt_normal2_disk c f /\ moi_lcus_model c f g e
     ==> ?g' k. pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g') /\
                (!z. z IN moi_lcus_mr ==> g z IN std_triangle /\ g' (g z) = z) /\
                (!x. x IN std_triangle ==> g' x IN moi_lcus_mr /\ g (g' x) = x) /\
                (!z. z IN moi_lcus_mr
                     ==> (g z IN relative_frontier std_triangle <=>
                          z IN frontier moi_lcus_mr)) /\
                k IN components (moi_lt_double_image f) /\
                ~(k INTER complex_boundary c = {}) /\
                {x | x IN std_triangle /\ f x IN k} =
                IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
                         segment[vector[&2; &0],vector[&2; &1]]) /\
                (!z. z IN moi_lcus_mr ==> (f (g z) IN k <=> z$1 = &1 \/ z$1 = &2)) /\
                (!z. z IN moi_lcus_mr /\ (z$1 = &1 \/ z$1 = &2)
                     ==> f (g (moi_lsm_rho e z)) = f (g z)) /\
                (!z z'. z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\
                        (z$1 = &1 \/ z$1 = &2) /\ z'$1 = z$1 /\ f (g z) = f (g z')
                        ==> z = z')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lcus_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `g':real^2->real^2`) (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)
        (LABEL_TAC "REL"))))) THEN
  MAP_EVERY EXISTS_TAC [`g':real^2->real^2`; `k:real^N->bool`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z:real^2. z IN moi_lcus_mr ==> (g:real^2->real^2) z IN std_triangle`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN std_triangle ==> (g':real^2->real^2) x IN moi_lcus_mr`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  (* boundary to boundary *)
  SUBGOAL_THEN `!z:real^2. z IN moi_lcus_mr
                  ==> ((g:real^2->real^2) z IN relative_frontier std_triangle <=>
                       z IN frontier moi_lcus_mr)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^2) (relative_frontier moi_lcus_mr) =
                 relative_frontier std_triangle` THEN
    REWRITE_TAC[MOI_LSM_MR_RELFRONT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z0:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z0:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
       [UNDISCH_TAC `(z0:real^2) IN frontier moi_lcus_mr` THEN
        REWRITE_TAC[MOI_LSM_MR_FRONTIER] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `z:real^2 = z0` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the points sent into k *)
  SUBGOAL_THEN `!z:real^2. z IN moi_lcus_mr
                  ==> ((f:real^2->real^N) ((g:real^2->real^2) z) IN k <=>
                       z$1 = &1 \/ z$1 = &2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(SPEC `z:real^2` MOI_LSM_CHORDS_IN_MR) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} =
                 IMAGE (g:real^2->real^2) (segment[vector[&1; &0],vector[&1; &1]] UNION
                                           segment[vector[&2; &0],vector[&2; &1]])` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^2) z`) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z0:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z0:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
       [UNDISCH_TAC `(z0:real^2) IN segment[vector[&1; &0],vector[&1; &1]] UNION
                                      segment[vector[&2; &0],vector[&2; &1]]` THEN
        REWRITE_TAC[MOI_LSM_CHORDS; IN_UNION; IN_ELIM_THM; MOI_LSM_IN_MR] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `z:real^2 = z0` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the chord relation under rho *)
  SUBGOAL_THEN `!z:real^2. z IN moi_lcus_mr /\ (z$1 = &1 \/ z$1 = &2)
                  ==> (f:real^2->real^N) ((g:real^2->real^2) (moi_lsm_rho e z)) = f (g z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LSM_RHO_CHORDS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* injectivity on each chord *)
  MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CH") STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `z:real^2 = z'` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_LA2_NORMAL_BASIC o
              MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^2->real^N) ((g:real^2->real^2) z)` o last o CONJUNCTS) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_lsm_rho e (z:real^2) IN moi_lcus_mr /\
                ~(moi_lsm_rho e z = z) /\ ~(moi_lsm_rho e z = z')`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LSM_RHO] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MOI_LSM_RHO] THEN
    USE_THEN "CH" MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) ((g:real^2->real^2) (moi_lsm_rho e z)) = f (g z)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `moi_lsm_rho e`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`{x | x IN std_triangle /\ (f:real^2->real^N) x = f ((g:real^2->real^2) z)}`;
    `(g:real^2->real^2) z`; `(g:real^2->real^2) z'`;
    `(g:real^2->real^2) (moi_lsm_rho e z)`] MOI_LSM_THREE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the touching map moi_lsm_tm f g e = f o g o psi on the model.    *)
(* On the outer parts it is f o g o rho, on the middle part f o g (the two  *)
(* formulas agree on the chords by the model relation); it is PL, it maps  *)
(* the model into the image of f, exactly the chords into k, and exactly   *)
(* the frontier of the model into the boundary of c.                        *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_tm = new_definition
 `moi_lsm_tm (f:real^2->real^N) (g:real^2->real^2) e z = f (g (moi_lsm_psi e z))`;;

let MOI_LSM_PSI = prove
 (`!e z:real^2.
     z IN moi_lcus_mr
     ==> moi_lsm_psi e z IN moi_lcus_mr /\
         (moi_lsm_psi e z IN frontier moi_lcus_mr <=> z IN frontier moi_lcus_mr) /\
         (moi_lsm_psi e z $1 = &1 \/ moi_lsm_psi e z $1 = &2 <=> z$1 = &1 \/ z$1 = &2) /\
         (z$1 <= &1 \/ &2 <= z$1 ==> moi_lsm_psi e z = moi_lsm_rho e z) /\
         (&1 < z$1 /\ z$1 < &2 ==> moi_lsm_psi e z = z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `e:bool` o MATCH_MP
    (MESON[MOI_LSM_RHO_PARTS] `!z. z IN moi_lcus_mr ==> !e.
        (moi_lsm_rho e z $1 <= &1 <=> &2 <= z$1) /\
        (&2 <= moi_lsm_rho e z $1 <=> z$1 <= &1) /\
        (moi_lsm_rho e z $1 = &1 <=> z$1 = &2) /\
        (moi_lsm_rho e z $1 = &2 <=> z$1 = &1) /\
        (moi_lsm_rho e z IN frontier moi_lcus_mr <=> z IN frontier moi_lcus_mr)`)) THEN
  REWRITE_TAC[moi_lsm_psi] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= &1 \/ &2 <= z$1` THEN ASM_REWRITE_TAC[MOI_LSM_RHO] THEN
  ASM_REAL_ARITH_TAC);;

(* The touching map on the three parts. *)

let MOI_LSM_TM_PIECES = prove
 (`!(f:real^2->real^N) (g:real^2->real^2) e z.
     (!z. z IN moi_lcus_mr /\ (z$1 = &1 \/ z$1 = &2)
          ==> f (g (moi_lsm_rho e z)) = f (g z)) /\
     z IN moi_lcus_mr
     ==> (z$1 <= &1 ==> moi_lsm_tm f g e z = f (g (moi_lsm_rho e z))) /\
         (&2 <= z$1 ==> moi_lsm_tm f g e z = f (g (moi_lsm_rho e z))) /\
         (&1 <= z$1 /\ z$1 <= &2 ==> moi_lsm_tm f g e z = f (g z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_lsm_tm; moi_lsm_psi] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The three parts of the model. *)

let MOI_LSM_PARTS = prove
 (`!z:real^2.
     (z IN interval[vector[&0; &0],vector[&1; &1]] <=> z IN moi_lcus_mr /\ z$1 <= &1) /\
     (z IN interval[vector[&1; &0],vector[&2; &1]] <=>
      z IN moi_lcus_mr /\ &1 <= z$1 /\ z$1 <= &2) /\
     (z IN interval[vector[&2; &0],vector[&3; &1]] <=> z IN moi_lcus_mr /\ &2 <= z$1)`,
  GEN_TAC THEN REWRITE_TAC[IN_INTERVAL; MOI_LSM_IN_MR; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_LSM_TM_PL = prove
 (`!(f:real^2->real^N) (g:real^2->real^2) e.
     pl_map_on std_triangle f /\ pl_map_on moi_lcus_mr g /\
     (!z. z IN moi_lcus_mr ==> g z IN std_triangle) /\
     (!z. z IN moi_lcus_mr /\ (z$1 = &1 \/ z$1 = &2)
          ==> f (g (moi_lsm_rho e z)) = f (g z))
     ==> pl_map_on moi_lcus_mr (moi_lsm_tm f g e) /\
         moi_lsm_tm f g e continuous_on moi_lcus_mr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]] THEN
  (* f o g o rho and f o g are PL on any locally polyhedral subset of the model *)
  SUBGOAL_THEN
   `!s:real^2->bool. s SUBSET moi_lcus_mr /\ locally_polyhedral s
      ==> pl_map_on s ((f:real^2->real^N) o (g:real^2->real^2)) /\
          pl_map_on s (f o g o moi_lsm_rho e)`
  (LABEL_TAC "PLS") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pl_map_on s ((f:real^2->real^N) o (g:real^2->real^2))` ASSUME_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_lcus_mr` THEN
    ASM_SIMP_TAC[MOI_LSM_RHO_PL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET; MOI_LSM_RHO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval[vector[&0; &0]:real^2,vector[&1; &1]] SUBSET moi_lcus_mr /\
    interval[vector[&1; &0]:real^2,vector[&2; &1]] SUBSET moi_lcus_mr /\
    interval[vector[&2; &0]:real^2,vector[&3; &1]] SUBSET moi_lcus_mr /\
    locally_polyhedral (interval[vector[&0; &0]:real^2,vector[&1; &1]]) /\
    locally_polyhedral (interval[vector[&1; &0]:real^2,vector[&2; &1]]) /\
    locally_polyhedral (interval[vector[&2; &0]:real^2,vector[&3; &1]])`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
    REWRITE_TAC[SUBSET; MOI_LSM_PARTS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_LSM_MR_EQ] THEN
  MATCH_MP_TAC MOI_LC0_RECT_PASTE THEN EXISTS_TAC `&2` THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_LC0_RECT_PASTE THEN EXISTS_TAC `&1` THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; REAL_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(f:real^2->real^N) o (g:real^2->real^2) o moi_lsm_rho e` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MOI_LSM_PARTS; o_THM] THEN REPEAT STRIP_TAC THEN
        CONV_TAC SYM_CONV THEN
        MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`; `x:real^2`]
          MOI_LSM_TM_PIECES) THEN
        ASM_SIMP_TAC[];
        USE_THEN "PLS" (MP_TAC o SPEC `interval[vector[&0; &0]:real^2,vector[&1; &1]]`) THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(f:real^2->real^N) o (g:real^2->real^2)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MOI_LSM_PARTS; o_THM] THEN REPEAT STRIP_TAC THEN
        CONV_TAC SYM_CONV THEN
        MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`; `x:real^2`]
          MOI_LSM_TM_PIECES) THEN
        ASM_SIMP_TAC[];
        USE_THEN "PLS" (MP_TAC o SPEC `interval[vector[&1; &0]:real^2,vector[&2; &1]]`) THEN
        ASM_SIMP_TAC[]]];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `(f:real^2->real^N) o (g:real^2->real^2) o moi_lsm_rho e` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MOI_LSM_PARTS; o_THM] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`; `x:real^2`]
        MOI_LSM_TM_PIECES) THEN
      ASM_SIMP_TAC[];
      USE_THEN "PLS" (MP_TAC o SPEC `interval[vector[&2; &0]:real^2,vector[&3; &1]]`) THEN
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: the model setup and the touching map.  moi_lsm_setup collects    *)
(* the consequences of the model (MOI_LSM_MODEL) used below.  psi is an     *)
(* involution off the chords; the touching map sends the chords into k and *)
(* nothing else, the frontier into the boundary of c and nothing else; two  *)
(* points with the same image are either a double point of f off k, or one *)
(* point on each chord.                                                     *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_setup = new_definition
 `moi_lsm_setup (c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k <=>
    moi_lt_normal2_disk c f /\
    pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g') /\
    (!z. z IN moi_lcus_mr ==> g z IN std_triangle /\ g' (g z) = z) /\
    (!x. x IN std_triangle ==> g' x IN moi_lcus_mr /\ g (g' x) = x) /\
    (!z. z IN moi_lcus_mr
         ==> (g z IN relative_frontier std_triangle <=> z IN frontier moi_lcus_mr)) /\
    k IN components (moi_lt_double_image f) /\
    {x | x IN std_triangle /\ f x IN k} =
    IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
             segment[vector[&2; &0],vector[&2; &1]]) /\
    (!z. z IN moi_lcus_mr ==> (f (g z) IN k <=> z$1 = &1 \/ z$1 = &2)) /\
    (!z. z IN moi_lcus_mr /\ (z$1 = &1 \/ z$1 = &2)
         ==> f (g (moi_lsm_rho e z)) = f (g z)) /\
    (!z z'. z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\
            (z$1 = &1 \/ z$1 = &2) /\ z'$1 = z$1 /\ f (g z) = f (g z')
            ==> z = z')`;;

let MOI_LSM_SETUP_EXISTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) e.
     moi_lt_normal2_disk c f /\ moi_lcus_model c f g e
     ==> ?g' k. moi_lsm_setup c f g g' e k /\ ~(k INTER complex_boundary c = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LSM_MODEL) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* psi is an involution off the chords. *)

let MOI_LSM_PSI_INV = prove
 (`!e z:real^2.
     z IN moi_lcus_mr /\ ~(z$1 = &1) /\ ~(z$1 = &2)
     ==> moi_lsm_psi e z IN moi_lcus_mr /\
         ~(moi_lsm_psi e z $1 = &1) /\ ~(moi_lsm_psi e z $1 = &2) /\
         moi_lsm_psi e (moi_lsm_psi e z) = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:bool`; `z:real^2`] MOI_LSM_PSI) THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= &1 \/ &2 <= z$1` THENL
   [SUBGOAL_THEN `moi_lsm_psi e z = moi_lsm_rho e (z:real^2)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_lsm_psi e (moi_lsm_rho e z) = moi_lsm_rho e (moi_lsm_rho e (z:real^2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_lsm_psi; MOI_LSM_RHO] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[MOI_LSM_RHO]];
    SUBGOAL_THEN `moi_lsm_psi e z = (z:real^2)` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The touching map: image, the chords, the boundary. *)

let MOI_LSM_TM_FACTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k z.
     moi_lsm_setup c f g g' e k /\ z IN moi_lcus_mr
     ==> g (moi_lsm_psi e z) IN std_triangle /\
         moi_lsm_tm f g e z IN IMAGE f std_triangle /\
         moi_lsm_tm f g e z IN UNIONS c /\
         (moi_lsm_tm f g e z IN k <=> z$1 = &1 \/ z$1 = &2) /\
         (moi_lsm_tm f g e z IN complex_boundary c <=> z IN frontier moi_lcus_mr)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:bool`; `z:real^2`] MOI_LSM_PSI) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^2) (moi_lsm_psi e z) IN std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o
              MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_lsm_tm] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    ASM_MESON_TAC[];
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^2) (moi_lsm_psi e z)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]]);;

(* Two points with the same image under the touching map. *)

let MOI_LSM_TM_DOUBLE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k z z' y.
     moi_lsm_setup c f g g' e k /\ z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\
     ~(z = z') /\ moi_lsm_tm f g e z = y /\ moi_lsm_tm f g e z' = y
     ==> (~(y IN k) /\ y IN moi_lt_double_image f) \/
         (y IN k /\ ((z$1 = &1 /\ z'$1 = &2) \/ (z$1 = &2 /\ z'$1 = &1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
    MOI_LSM_TM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
    `moi_lsm_tm (f:real^2->real^N) g e z = y`]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z':real^2`]
    MOI_LSM_TM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
    `moi_lsm_tm (f:real^2->real^N) g e z' = y`]) THEN
  UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
  REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(y:real^N) IN k` THENL
   [(* both on chords, not on the same chord *)
    DISJ2_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `((z:real^2)$1 = &1 \/ z$1 = &2) /\ ((z':real^2)$1 = &1 \/ z'$1 = &2)`
    (CONJUNCTS_THEN ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e z = f (g z) /\
                  moi_lsm_tm f g e z' = f (g z')` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      W(fun (_,w) -> MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`;
          rand(lhand w)] MOI_LSM_TM_PIECES)) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^2)$1 = (z':real^2)$1)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(z:real^2 = z')` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        length (fst(strip_forall (concl th))) = 2)) THEN
      ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    (* off the chords: a double point of f *)
    DISJ1_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
    SUBGOAL_THEN `~((z:real^2)$1 = &1) /\ ~(z$1 = &2) /\
                  ~((z':real^2)$1 = &1) /\ ~(z'$1 = &2)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`(g:real^2->real^2) (moi_lsm_psi e z)`;
                          `(g:real^2->real^2) (moi_lsm_psi e z')`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(z:real^2 = z')` THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`e:bool`; `z:real^2`] MOI_LSM_PSI_INV) THEN
      MP_TAC(SPECL [`e:bool`; `z':real^2`] MOI_LSM_PSI_INV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[moi_lsm_tm];
      ASM_MESON_TAC[moi_lsm_tm]]]);;

(* Double points of f off k come from two points off the chords. *)

let MOI_LSM_TM_ONTO_DI = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k y.
     moi_lsm_setup c f g g' e k /\ y IN moi_lt_double_image f /\ ~(y IN k)
     ==> ?z z'. z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\ ~(z = z') /\
                ~(z$1 = &1) /\ ~(z$1 = &2) /\ ~(z'$1 = &1) /\ ~(z'$1 = &2) /\
                moi_lsm_tm f g e z = y /\ moi_lsm_tm f g e z' = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_setup; moi_lt_double_image; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!x:real^2. x IN std_triangle /\ (f:real^2->real^N) x = y
       ==> (g':real^2->real^2) x IN moi_lcus_mr /\ ~((g' x)$1 = &1) /\ ~((g' x)$1 = &2) /\
           moi_lsm_psi e (g' x) IN moi_lcus_mr /\
           ~(moi_lsm_psi e (g' x) $1 = &1) /\ ~(moi_lsm_psi e (g' x) $1 = &2) /\
           moi_lsm_tm f g e (moi_lsm_psi e (g' x)) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g':real^2->real^2) x IN moi_lcus_mr /\ g (g' x) = x` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(((g':real^2->real^2) x)$1 = &1) /\ ~((g' x)$1 = &2)` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`e:bool`; `(g':real^2->real^2) x`] MOI_LSM_PSI_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_lsm_tm];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`moi_lsm_psi e ((g':real^2->real^2) x1)`;
                        `moi_lsm_psi e ((g':real^2->real^2) x2)`] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x1:real^2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x2:real^2`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(x1:real^2 = x2)` THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`e:bool`; `(g':real^2->real^2) x1`] MOI_LSM_PSI_INV) THEN
  MP_TAC(SPECL [`e:bool`; `(g':real^2->real^2) x2`] MOI_LSM_PSI_INV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* Off k the fibres of the touching map have at most two points. *)

let MOI_LSM_TM_FIBRE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k y z1 z2 z3.
     moi_lsm_setup c f g g' e k /\ ~(y IN k) /\
     z1 IN moi_lcus_mr /\ z2 IN moi_lcus_mr /\ z3 IN moi_lcus_mr /\
     moi_lsm_tm f g e z1 = y /\ moi_lsm_tm f g e z2 = y /\ moi_lsm_tm f g e z3 = y
     ==> z1 = z2 \/ z1 = z3 \/ z2 = z3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq (concl th) && rhs (concl th) = `y:real^N`))) THEN
  ASM_CASES_TAC `z1:real^2 = z2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z1:real^2 = z3` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z2:real^2 = z3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z:real^2. z IN moi_lcus_mr /\ moi_lsm_tm (f:real^2->real^N) g e z = moi_lsm_tm f g e z1
       ==> ~(z$1 = &1) /\ ~(z$1 = &2) /\
           (g:real^2->real^2) (moi_lsm_psi e z) IN std_triangle /\
           f (g (moi_lsm_psi e z)) = moi_lsm_tm f g e z1`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
      MOI_LSM_TM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_lsm_tm];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
  REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o
              MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN
  DISCH_THEN(MP_TAC o SPEC `moi_lsm_tm (f:real^2->real^N) g e z1` o last o CONJUNCTS) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z1:real^2`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `z2:real^2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z3:real^2`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL
   [`{x | x IN std_triangle /\ (f:real^2->real^N) x = moi_lsm_tm f g e z1}`;
    `(g:real^2->real^2) (moi_lsm_psi e z1)`; `(g:real^2->real^2) (moi_lsm_psi e z2)`;
    `(g:real^2->real^2) (moi_lsm_psi e z3)`] MOI_LSM_THREE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(SPECL [`e:bool`; `z1:real^2`] MOI_LSM_PSI_INV) THEN
  MP_TAC(SPECL [`e:bool`; `z2:real^2`] MOI_LSM_PSI_INV) THEN
  MP_TAC(SPECL [`e:bool`; `z3:real^2`] MOI_LSM_PSI_INV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: the pushed map.  moi_lsm_pdata collects the properties of the    *)
(* push H = hh(1) given by MOI_LSM_PUSH; moi_lsm_pm H f g e is H o tm on    *)
(* the seam-1 side (x <= 3/2) and tm on the other side.  A band around the *)
(* middle line x = 3/2 is sent off S by tm, so pm = H o tm left of the band *)
(* and pm = tm right of it; pm is PL, keeps the frontier on the boundary of *)
(* c and the rest off it.                                                   *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_pdata = new_definition
 `moi_lsm_pdata (c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) k
                (H:real^N->real^N) S <=>
    closed S /\ k SUBSET S /\
    DISJOINT S (moi_lt_double_image f DIFF k) /\
    DISJOINT S (IMAGE (f o g) (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]])) /\
    (!z. z IN UNIONS c
         ==> H z IN UNIONS c /\
             (H z IN complex_boundary c <=> z IN complex_boundary c) /\
             (~(z IN S) ==> H z = z) /\ (z IN S ==> H z IN S)) /\
    pl_map_on (UNIONS c) H /\
    (!z z'. z IN UNIONS c /\ z' IN UNIONS c /\ H z = H z' ==> z = z') /\
    (!x. x IN IMAGE g (interval[vector[&1; &0],vector[&3 / &2; &1]] UNION
                       interval[vector[&2; &0],vector[&3; &1]])
         ==> H (f x) = f x \/ ~(H (f x) IN IMAGE f std_triangle)) /\
    (!y. y IN k ==> ~(H y IN IMAGE f std_triangle))`;;

let moi_lsm_pm = new_definition
 `moi_lsm_pm (H:real^N->real^N) (f:real^2->real^N) (g:real^2->real^2) e (z:real^2) =
    if z$1 <= &3 / &2 then H (moi_lsm_tm f g e z) else moi_lsm_tm f g e z`;;

(* The seam-1 side of the model is carried by psi into the region of K1. *)

let MOI_LSM_PSI_SIDE1 = prove
 (`!e z:real^2.
     z IN moi_lcus_mr /\ z$1 <= &3 / &2
     ==> moi_lsm_psi e z IN interval[vector[&1; &0],vector[&3 / &2; &1]] UNION
                            interval[vector[&2; &0],vector[&3; &1]]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LSM_IN_MR] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_lsm_psi; moi_lsm_rho; IN_UNION; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_2] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VECTOR_2] THEN
  TRY(COND_CASES_TAC) THEN ASM_REAL_ARITH_TAC);;

(* A band around the middle line is sent off S. *)

let MOI_LSM_BAND = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k S.
     moi_lsm_setup c f g g' e k /\ closed S /\
     DISJOINT S (IMAGE (f o g) (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]]))
     ==> ?d. &0 < d /\
             !z. z IN moi_lcus_mr /\ abs(z$1 - &3 / &2) < d
                 ==> ~(moi_lsm_tm f g e z IN S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e continuous_on moi_lcus_mr` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`] MOI_LSM_TM_PL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup; pl_homeomorphism; moi_lt_normal2_disk; moi_lt_normal_disk;
                moi_lt_singular_disk] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = {z:real^2 | z IN moi_lcus_mr /\ moi_lsm_tm (f:real^2->real^N) g e z IN S}` THEN
  SUBGOAL_THEN `compact (K:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC CLOSED_IN_COMPACT THEN
    EXISTS_TAC `moi_lcus_mr` THEN REWRITE_TAC[MOI_LSM_MR_FACTS] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ABBREV_TAC `L = {z:real^2 | z$1 = &3 / &2}` THEN
  SUBGOAL_THEN `closed (L:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (K:real^2->bool) L` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "L"] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    UNDISCH_TAC `DISJOINT S (IMAGE ((f:real^2->real^N) o (g:real^2->real^2))
                   (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]]))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `moi_lsm_tm (f:real^2->real^N) g e z`) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `z:real^2` THEN
    REWRITE_TAC[MOI_LSM_CHORDS; IN_ELIM_THM] THEN
    UNDISCH_TAC `(z:real^2) IN moi_lcus_mr` THEN REWRITE_TAC[MOI_LSM_IN_MR] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_lsm_tm; moi_lsm_psi] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `K:real^2->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    UNDISCH_TAC `K:real^2->bool = {}` THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^2->bool`; `L:real^2->bool`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM DISJOINT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^2`; `vector[&3 / &2; (z:real^2)$2]:real^2`]) THEN
  MATCH_MP_TAC(TAUT `(p /\ q) /\ ~r ==> (p /\ q ==> r) ==> F`) THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_2];
    REWRITE_TAC[REAL_NOT_LE; dist] THEN
    SUBGOAL_THEN `(z:real^2) - vector[&3 / &2; z$2] = (z$1 - &3 / &2) % basis 1`
    SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
               VECTOR_2; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[]]]);;

(* pm is H o tm left of the band and tm right of it. *)

let MOI_LSM_PM_SIDES = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S d z.
     moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\
     (!z. z IN moi_lcus_mr /\ abs(z$1 - &3 / &2) < d ==> ~(moi_lsm_tm f g e z IN S)) /\
     z IN moi_lcus_mr
     ==> (z$1 < &3 / &2 + d ==> moi_lsm_pm H f g e z = H (moi_lsm_tm f g e z)) /\
         (&3 / &2 - d < z$1 ==> moi_lsm_pm H f g e z = moi_lsm_tm f g e z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e z IN UNIONS c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
      MOI_LSM_TM_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lsm_pdata c (f:real^2->real^N) g k H S` THEN
  REWRITE_TAC[moi_lsm_pdata] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_lsm_pm] THEN CONJ_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `~(moi_lsm_tm (f:real^2->real^N) g e z IN S)` ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     ASM_MESON_TAC[]]));;

(* pm is PL, maps into the manifold, and keeps the boundary. *)

let MOI_LSM_PM_PL = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S d.
     moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\ &0 < d /\
     (!z. z IN moi_lcus_mr /\ abs(z$1 - &3 / &2) < d ==> ~(moi_lsm_tm f g e z IN S))
     ==> pl_map_on moi_lcus_mr (moi_lsm_pm H f g e) /\
         moi_lsm_pm H f g e continuous_on moi_lcus_mr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]] THEN
  SUBGOAL_THEN `pl_map_on moi_lcus_mr (moi_lsm_tm (f:real^2->real^N) g e)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`] MOI_LSM_TM_PL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup; pl_homeomorphism; moi_lt_normal2_disk; moi_lt_normal_disk;
                moi_lt_singular_disk] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN moi_lcus_mr
                  ==> moi_lsm_tm (f:real^2->real^N) g e z IN UNIONS c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
      MOI_LSM_TM_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (UNIONS c) (H:real^N->real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_pdata c (f:real^2->real^N) g k H S` THEN
    SIMP_TAC[moi_lsm_pdata];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval[vector[&0; &0]:real^2,vector[&3 / &2; &1]] SUBSET moi_lcus_mr /\
    interval[vector[&3 / &2; &0]:real^2,vector[&3; &1]] SUBSET moi_lcus_mr /\
    locally_polyhedral (interval[vector[&0; &0]:real^2,vector[&3 / &2; &1]]) /\
    locally_polyhedral (interval[vector[&3 / &2; &0]:real^2,vector[&3; &1]])`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; MOI_LSM_IN_MR; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_LSM_MR_EQ] THEN
  MATCH_MP_TAC MOI_LC0_RECT_PASTE THEN EXISTS_TAC `&3 / &2` THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC;
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `(H:real^N->real^N) o moi_lsm_tm (f:real^2->real^N) g e` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^2` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; o_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[moi_lsm_pm];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]]];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `moi_lsm_tm (f:real^2->real^N) g e` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                     `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                     `S:real^N->bool`; `d:real`; `z:real^2`] MOI_LSM_PM_SIDES) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        UNDISCH_TAC `(z:real^2) IN interval[vector[&3 / &2; &0],vector[&3; &1]]` THEN
        REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_LSM_PM_FACTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S z.
     moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\ z IN moi_lcus_mr
     ==> moi_lsm_pm H f g e z IN UNIONS c /\
         (moi_lsm_pm H f g e z IN complex_boundary c <=> z IN frontier moi_lcus_mr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
    MOI_LSM_TM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_lsm_pdata c (f:real^2->real^N) g k H S` THEN
  REWRITE_TAC[moi_lsm_pdata] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_lsm_pm] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: local injectivity.  The other double components form a closed   *)
(* set missing k.  Near a point whose image is not a double point off k,   *)
(* two points with the same image would be one on each chord (TM_DOUBLE),  *)
(* impossible in a thin strip; near a double point off k the touching map  *)
(* is f o g o rho or f o g on an open half-plane or strip and f is locally *)
(* injective.  The pushed map is H o tm or tm on two open sets covering   *)
(* the model, with H injective.                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_DI_REST_CLOSED = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k.
     moi_lsm_setup c f g g' e k
     ==> closed (moi_lt_double_image f DIFF k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o
              MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`; `k:real^N->bool`]
    MOI_LA1_COMPONENT_CLOPEN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_LT2D_NORMAL2_FINITE]; STRIP_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
  EXISTS_TAC `moi_lt_double_image (f:real^2->real^N)` THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL]);;

let MOI_LSM_OPEN_STRIP = prove
 (`!a b. open {z:real^2 | a < z$1 /\ z$1 < b} /\ open {z:real^2 | a < z$1} /\
         open {z:real^2 | z$1 < b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{z:real^2 | a < z$1} = {z | z$1 > a}` SUBST1_TAC THENL
   [REWRITE_TAC[real_gt]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT] THEN
  SUBGOAL_THEN `{z:real^2 | a < z$1 /\ z$1 < b} = {z | z$1 > a} INTER {z | z$1 < b}`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_INTER THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT]);;

let MOI_LSM_TM_LOCINJ = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k z0.
     moi_lsm_setup c f g g' e k /\ z0 IN moi_lcus_mr
     ==> ?n. open n /\ z0 IN n /\
             !z z'. z IN n /\ z' IN n /\ z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\
                    moi_lsm_tm f g e z = moi_lsm_tm f g e z'
                    ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e continuous_on moi_lcus_mr` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`] MOI_LSM_TM_PL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup; pl_homeomorphism; moi_lt_normal2_disk; moi_lt_normal_disk;
                moi_lt_singular_disk] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `moi_lsm_tm (f:real^2->real^N) g e z0 IN moi_lt_double_image f DIFF k` THENL
   [ALL_TAC;
    (* not a double point off k: a thin strip *)
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`] MOI_LSM_DI_REST_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`moi_lsm_tm (f:real^2->real^N) g e`; `moi_lcus_mr`;
                   `(:real^N) DIFF (moi_lt_double_image f DIFF k)`]
      CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM closed] THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `o1 INTER {z:real^2 | (z0:real^2)$1 - &1 / &2 < z$1 /\
                                     z$1 < z0$1 + &1 / &2}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[MOI_LSM_OPEN_STRIP];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(z0:real^2) IN {x | x IN moi_lcus_mr /\
                        moi_lsm_tm (f:real^2->real^N) g e x IN
                        (:real^N) DIFF (moi_lt_double_image f DIFF k)}` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
          UNDISCH_TAC `~(moi_lsm_tm (f:real^2->real^N) g e z0 IN
                         moi_lt_double_image f DIFF k)` THEN SET_TAC[];
          ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `z:real^2 = z'` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`; `z':real^2`;
                   `moi_lsm_tm (f:real^2->real^N) g e z`] MOI_LSM_TM_DOUBLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(moi_lsm_tm (f:real^2->real^N) g e z IN moi_lt_double_image f DIFF k)`
    MP_TAC THENL
     [SUBGOAL_THEN `(z:real^2) IN {x | x IN moi_lcus_mr /\
                       moi_lsm_tm (f:real^2->real^N) g e x IN
                       (:real^N) DIFF (moi_lt_double_image f DIFF k)}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER]; REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN
    MATCH_MP_TAC(TAUT `(c ==> F) ==> ~(a /\ ~b) ==> ~(~b /\ a \/ b /\ c)`) THEN
    MAP_EVERY UNDISCH_TAC
     [`(z0:real^2)$1 - &1 / &2 < (z:real^2)$1`; `(z:real^2)$1 < (z0:real^2)$1 + &1 / &2`;
      `(z0:real^2)$1 - &1 / &2 < (z':real^2)$1`; `(z':real^2)$1 < (z0:real^2)$1 + &1 / &2`] THEN
    REAL_ARITH_TAC] THEN
  (* a double point off k: f is locally injective at the source point *)
  SUBGOAL_THEN `~((z0:real^2)$1 = &1) /\ ~(z0$1 = &2)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z0:real^2`]
      MOI_LSM_TM_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `moi_lsm_tm (f:real^2->real^N) g e z0 IN moi_lt_double_image f DIFF k` THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?(phi:real^2->real^2) W.
      open W /\ z0 IN W /\ phi continuous_on moi_lcus_mr /\
      (!z. z IN moi_lcus_mr ==> phi z IN moi_lcus_mr) /\
      (!z z'. z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\ phi z = phi z' ==> z = z') /\
      (!z. z IN W INTER moi_lcus_mr ==> moi_lsm_psi e z = phi z)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&1 < (z0:real^2)$1 /\ z0$1 < &2` THENL
     [MAP_EVERY EXISTS_TAC [`\z:real^2. z`; `{z:real^2 | &1 < z$1 /\ z$1 < &2}`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; CONTINUOUS_ON_ID; IN_INTER; MOI_LSM_OPEN_STRIP] THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `z:real^2` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      REWRITE_TAC[moi_lsm_psi] THEN
      SUBGOAL_THEN `~((z:real^2)$1 <= &1 \/ &2 <= z$1)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `&1 < (z:real^2)$1 /\ z$1 < &2` THEN REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC
       [`moi_lsm_rho e`; `{z:real^2 | z$1 < &1} UNION {z:real^2 | &2 < z$1}`] THEN
      REWRITE_TAC[MOI_LSM_RHO_CONTINUOUS; IN_UNION; IN_ELIM_THM; IN_INTER] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_UNION THEN REWRITE_TAC[MOI_LSM_OPEN_STRIP];
        MAP_EVERY UNDISCH_TAC [`~((z0:real^2)$1 = &1)`; `~((z0:real^2)$1 = &2)`;
                               `~(&1 < (z0:real^2)$1 /\ z0$1 < &2)`] THEN REAL_ARITH_TAC;
        REWRITE_TAC[MOI_LSM_RHO];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `moi_lsm_rho e`) THEN
        REWRITE_TAC[MOI_LSM_RHO];
        X_GEN_TAC `z:real^2` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
        REWRITE_TAC[moi_lsm_psi] THEN
        SUBGOAL_THEN `(z:real^2)$1 <= &1 \/ &2 <= z$1` (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `(z:real^2)$1 < &1 \/ &2 < z$1` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
  REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o
              MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^2->real^2) ((phi:real^2->real^2) z0)` o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `open:(real^2->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(g:real^2->real^2) o (phi:real^2->real^2)`; `moi_lcus_mr`; `n0:real^2->bool`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^2. x IN moi_lcus_mr /\ x IN o1
                  ==> (g:real^2->real^2) ((phi:real^2->real^2) x) IN n0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN {x | x IN moi_lcus_mr /\
                    ((g:real^2->real^2) o (phi:real^2->real^2)) x IN n0}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; REWRITE_TAC[IN_ELIM_THM; o_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `o1 INTER W:real^2->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(z0:real^2) IN {x | x IN moi_lcus_mr /\
                    ((g:real^2->real^2) o (phi:real^2->real^2)) x IN n0}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; o_THM]; ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^2) ((phi:real^2->real^2) z) IN n0 /\ g (phi z') IN n0 /\
                phi z IN moi_lcus_mr /\ phi z' IN moi_lcus_mr /\
                g (phi z) IN std_triangle /\ g (phi z') IN std_triangle`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lsm_psi e z = (phi:real^2->real^2) z /\ moi_lsm_psi e z' = phi z'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `W:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) ((g:real^2->real^2) ((phi:real^2->real^2) z)) =
                f (g (phi z'))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_tm (f:real^2->real^N) g e z = moi_lsm_tm f g e z'` THEN
    ASM_REWRITE_TAC[moi_lsm_tm];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2) ((phi:real^2->real^2) z) = g (phi z')` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `n0:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^2->real^2) z = phi z'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `g':real^2->real^2`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `phi:real^2->real^2`)) (concl th) &&
    length (fst(strip_forall (concl th))) = 2)) THEN
  ASM_REWRITE_TAC[]);;

(* The pushed map is locally injective. *)

let MOI_LSM_PM_LOCINJ = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S d z0.
     moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\ &0 < d /\
     (!z. z IN moi_lcus_mr /\ abs(z$1 - &3 / &2) < d ==> ~(moi_lsm_tm f g e z IN S)) /\
     z0 IN moi_lcus_mr
     ==> ?n. open n /\ z0 IN n /\
             !z z'. z IN n /\ z' IN n /\ z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\
                    moi_lsm_pm H f g e z = moi_lsm_pm H f g e z'
                    ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z0:real^2`]
    MOI_LSM_TM_LOCINJ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:real^2. z IN moi_lcus_mr
                  ==> moi_lsm_tm (f:real^2->real^N) g e z IN UNIONS c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
      MOI_LSM_TM_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z z':real^N. z IN UNIONS c /\ z' IN UNIONS c /\
                              (H:real^N->real^N) z = H z' ==> z = z'` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_pdata c (f:real^2->real^N) g k H S` THEN
    REWRITE_TAC[moi_lsm_pdata] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(z0:real^2)$1 < &3 / &2 + d` THENL
   [EXISTS_TAC `n INTER {z:real^2 | z$1 < &3 / &2 + d}` THEN
    ASM_SIMP_TAC[OPEN_INTER; MOI_LSM_OPEN_STRIP; IN_INTER; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                   `S:real^N->bool`; `d:real`] MOI_LSM_PM_SIDES) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `n INTER {z:real^2 | &3 / &2 - d < z$1}` THEN
    ASM_SIMP_TAC[OPEN_INTER; MOI_LSM_OPEN_STRIP; IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                   `S:real^N->bool`; `d:real`] MOI_LSM_PM_SIDES) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 8: the double points of the pushed map.  Two distinct points with   *)
(* the same image under pm have the same image under tm, and it is a double *)
(* point of f off k: on the same side by injectivity of H and because the  *)
(* chords lie on different sides of x = 3/2; across x = 3/2 by K1 (a moved *)
(* point leaves the image of f) and K2 (k is moved).  Conversely every      *)
(* double point of f off k is double for pm (it is not moved).  Fibres of   *)
(* pm have at most two points.                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_PM_DOUBLE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S z z' y.
     moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\
     z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\ ~(z = z') /\
     moi_lsm_pm H f g e z = y /\ moi_lsm_pm H f g e z' = y
     ==> y IN moi_lt_double_image f /\ ~(y IN k) /\
         moi_lsm_tm f g e z = y /\ moi_lsm_tm f g e z' = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w:real^2. w IN moi_lcus_mr
       ==> moi_lsm_tm (f:real^2->real^N) g e w IN UNIONS c /\
           moi_lsm_tm f g e w IN IMAGE f std_triangle /\
           (moi_lsm_tm f g e w IN k <=> w$1 = &1 \/ w$1 = &2)`
  (LABEL_TAC "TF") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `w:real^2`]
      MOI_LSM_TM_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the double point lemma for tm, packaged *)
  SUBGOAL_THEN
   `!w w' y0. w IN moi_lcus_mr /\ w' IN moi_lcus_mr /\ ~(w = w') /\
              moi_lsm_tm (f:real^2->real^N) g e w = y0 /\ moi_lsm_tm f g e w' = y0
              ==> (~(y0 IN k) /\ y0 IN moi_lt_double_image f) \/
                  (y0 IN k /\ ((w$1 = &1 /\ w'$1 = &2) \/ (w$1 = &2 /\ w'$1 = &1)))`
  (LABEL_TAC "TD") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                         `g':real^2->real^2`; `e:bool`; `k:real^N->bool`] MOI_LSM_TM_DOUBLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lsm_pdata c (f:real^2->real^N) g k H S` THEN
  REWRITE_TAC[moi_lsm_pdata] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HM") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "HI") (CONJUNCTS_THEN2 (LABEL_TAC "K1")
       (LABEL_TAC "K2"))))))))) THEN
  (* K1 for the seam-1 side of the model *)
  SUBGOAL_THEN
   `!w:real^2. w IN moi_lcus_mr /\ w$1 <= &3 / &2
       ==> (H:real^N->real^N) (moi_lsm_tm f g e w) = moi_lsm_tm f g e w \/
           ~(H (moi_lsm_tm f g e w) IN IMAGE f std_triangle)`
  (LABEL_TAC "K1M") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lsm_tm] THEN
    USE_THEN "K1" MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `moi_lsm_psi e w` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LSM_PSI_SIDE1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* points off S are fixed; double points off k are off S *)
  SUBGOAL_THEN `!y0:real^N. y0 IN moi_lt_double_image f /\ ~(y0 IN k) /\ y0 IN UNIONS c
                            ==> (H:real^N->real^N) y0 = y0`
  (LABEL_TAC "FIX") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "HM" (MP_TAC o C MP (ASSUME `(y0:real^N) IN UNIONS c`) o SPEC `y0:real^N`) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    UNDISCH_TAC `DISJOINT S (moi_lt_double_image (f:real^2->real^N) DIFF k)` THEN
    UNDISCH_TAC `(y0:real^N) IN moi_lt_double_image f` THEN
    UNDISCH_TAC `~((y0:real^N) IN k)` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `y:real^N`))) THEN
  REWRITE_TAC[moi_lsm_pm] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= &3 / &2` THEN
  ASM_CASES_TAC `(z':real^2)$1 <= &3 / &2` THEN ASM_REWRITE_TAC[] THENL
   [(* both on the seam-1 side *)
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e z = moi_lsm_tm f g e z'` ASSUME_TAC THENL
     [USE_THEN "HI" MATCH_MP_TAC THEN USE_THEN "TF" (fun th ->
        ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "TD" (MP_TAC o SPECL [`z:real^2`; `z':real^2`;
                                   `moi_lsm_tm (f:real^2->real^N) g e z`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(b ==> F) /\ (a ==> c) ==> (a \/ b ==> c)`) THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(H:real^N->real^N) (moi_lsm_tm f g e z) = moi_lsm_tm f g e z`
    ASSUME_TAC THENL
     [USE_THEN "FIX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "TF" (fun th ->
        ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^N = moi_lsm_tm (f:real^2->real^N) g e z` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* z on the seam-1 side, z' on the other *)
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(H:real^N->real^N) (moi_lsm_tm f g e z) = moi_lsm_tm f g e z`
    ASSUME_TAC THENL
     [USE_THEN "K1M" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `b ==> (a \/ ~b ==> a)`) THEN
      SUBGOAL_THEN `(H:real^N->real^N) (moi_lsm_tm f g e z) = moi_lsm_tm f g e z'`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "TF" (MP_TAC o SPEC `z':real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(moi_lsm_tm (f:real^2->real^N) g e z IN k)` ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `moi_lsm_tm (f:real^2->real^N) g e z`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `(H:real^N->real^N) (moi_lsm_tm f g e z) = moi_lsm_tm f g e z`] THEN
      USE_THEN "TF" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "TD" (MP_TAC o SPECL [`z:real^2`; `z':real^2`;
                                   `moi_lsm_tm (f:real^2->real^N) g e z`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    (* z on the other side, z' on the seam-1 side *)
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(H:real^N->real^N) (moi_lsm_tm f g e z') = moi_lsm_tm f g e z'`
    ASSUME_TAC THENL
     [USE_THEN "K1M" (MP_TAC o SPEC `z':real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `b ==> (a \/ ~b ==> a)`) THEN
      SUBGOAL_THEN `(H:real^N->real^N) (moi_lsm_tm f g e z') = moi_lsm_tm f g e z`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "TF" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(moi_lsm_tm (f:real^2->real^N) g e z' IN k)` ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "K2" (MP_TAC o SPEC `moi_lsm_tm (f:real^2->real^N) g e z'`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `(H:real^N->real^N) (moi_lsm_tm f g e z') = moi_lsm_tm f g e z'`] THEN
      USE_THEN "TF" (MP_TAC o SPEC `z':real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "TD" (MP_TAC o SPECL [`z:real^2`; `z':real^2`;
                                   `moi_lsm_tm (f:real^2->real^N) g e z'`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    (* both on the other side *)
    REPEAT DISCH_TAC THEN
    USE_THEN "TD" (MP_TAC o SPECL [`z:real^2`; `z':real^2`;
                                   `moi_lsm_tm (f:real^2->real^N) g e z`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(b ==> F) /\ (a ==> c) ==> (a \/ b ==> c)`) THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `y:real^N = moi_lsm_tm (f:real^2->real^N) g e z` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Every double point of f off k is double for pm. *)

let MOI_LSM_PM_ONTO = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S y.
     moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\
     y IN moi_lt_double_image f /\ ~(y IN k)
     ==> ?z z'. z IN moi_lcus_mr /\ z' IN moi_lcus_mr /\ ~(z = z') /\
                moi_lsm_pm H f g e z = y /\ moi_lsm_pm H f g e z' = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `y:real^N`]
    MOI_LSM_TM_ONTO_DI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_lsm_pm] THEN
  SUBGOAL_THEN `(H:real^N->real^N) y = y` (fun th -> REWRITE_TAC[th; COND_ID]) THEN
  UNDISCH_TAC `moi_lsm_pdata c (f:real^2->real^N) g k H S` THEN
  REWRITE_TAC[moi_lsm_pdata] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
      MOI_LSM_TM_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `complex_boundary c:real^N->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `DISJOINT S (moi_lt_double_image (f:real^2->real^N) DIFF k)` THEN
  ASM SET_TAC[]);;

(* Fibres of pm have at most two points. *)

let MOI_LSM_PM_FIBRE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S y z1 z2 z3.
     moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\
     z1 IN moi_lcus_mr /\ z2 IN moi_lcus_mr /\ z3 IN moi_lcus_mr /\
     moi_lsm_pm H f g e z1 = y /\ moi_lsm_pm H f g e z2 = y /\ moi_lsm_pm H f g e z3 = y
     ==> z1 = z2 \/ z1 = z3 \/ z2 = z3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `z1:real^2 = z2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z1:real^2 = z3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                 `S:real^N->bool`; `z1:real^2`; `z2:real^2`; `y:real^N`] MOI_LSM_PM_DOUBLE) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                 `S:real^N->bool`; `z1:real^2`; `z3:real^2`; `y:real^N`] MOI_LSM_PM_DOUBLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `y:real^N`;
                 `z1:real^2`; `z2:real^2`; `z3:real^2`] MOI_LSM_TM_FIBRE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 9: the boundary loop of the D_2 model.  moi_lsm_loop e runs around  *)
(* the model through rho(A_s) on the right part, the middle top or bottom  *)
(* edge, rho(A_u) on the left part and the other middle edge, in the       *)
(* direction that makes the touching map trace exactly the D_2 word of     *)
(* MOI_LCUS_SEAM.  It is a simple loop onto the frontier of the model.     *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_loop = new_definition
 `moi_lsm_loop e =
    (moi_lsm_rho e o moi_lcus_as) ++
    (if e then moi_lcus_av else reversepath moi_lcus_at) ++
    (moi_lsm_rho e o moi_lcus_au) ++
    (if e then moi_lcus_at else reversepath moi_lcus_av)`;;

(* The four model arcs. *)

let MOI_LSM_ARCS = prove
 (`arc moi_lcus_as /\ arc moi_lcus_at /\ arc moi_lcus_au /\ arc moi_lcus_av /\
   path_image moi_lcus_as =
   {x:real^2 | (x$1 = &0 /\ &0 <= x$2 /\ x$2 <= &1) \/
               ((x$2 = &0 \/ x$2 = &1) /\ &0 <= x$1 /\ x$1 <= &1)} /\
   path_image moi_lcus_au =
   {x:real^2 | (x$1 = &3 /\ &0 <= x$2 /\ x$2 <= &1) \/
               ((x$2 = &0 \/ x$2 = &1) /\ &2 <= x$1 /\ x$1 <= &3)} /\
   path_image moi_lcus_at = {x:real^2 | x$2 = &0 /\ &1 <= x$1 /\ x$1 <= &2} /\
   path_image moi_lcus_av = {x:real^2 | x$2 = &1 /\ &1 <= x$1 /\ x$1 <= &2} /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_as /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_at /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_au /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_av`,
  SUBGOAL_THEN `moi_lcus_as = moi_lc0_larc (&0) (&1) /\ moi_lcus_au = moi_lc0_rarc (&2) (&3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_lcus_as; moi_lcus_au; moi_lc0_larc; moi_lc0_rarc]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&0`; `&1`] MOI_LC0_LARC) THEN
  MP_TAC(SPECL [`&2`; `&3`] MOI_LC0_RARC) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 /\ &2 < &3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_lcus_at; moi_lcus_av; ARC_LINEPATH_EQ; MOI_LC0_VECTOR2_INJ;
              PATH_IMAGE_LINEPATH] THEN
  SIMP_TAC[MOI_LC0_HSEG; REAL_ARITH `&1 <= &2`] THEN
  SIMP_TAC[MOI_PL2_PL_LINEPATH; LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* rho exchanges the images of A_s and A_u and fixes those of A_t, A_v. *)

let MOI_LSM_RHO_IMAGES = prove
 (`!e. IMAGE (moi_lsm_rho e) (path_image moi_lcus_as) = path_image moi_lcus_au /\
       IMAGE (moi_lsm_rho e) (path_image moi_lcus_au) = path_image moi_lcus_as`,
  GEN_TAC THEN REWRITE_TAC[MOI_LSM_ARCS] THEN CONJ_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[MOI_LSM_RHO] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `moi_lsm_rho e (x:real^2)` THEN
    REWRITE_TAC[MOI_LSM_RHO] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[MOI_LSM_RHO] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `moi_lsm_rho e (x:real^2)` THEN
    REWRITE_TAC[MOI_LSM_RHO] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_LSM_RHO_ARC = prove
 (`!e g:real^1->real^2. arc g ==> arc (moi_lsm_rho e o g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[MOI_LSM_RHO_CONTINUOUS] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `moi_lsm_rho e`) THEN
  REWRITE_TAC[MOI_LSM_RHO]);;

(* The loop is a simple closed path onto the frontier of the model. *)

let MOI_LSM_LOOP_SIMPLE = prove
 (`!e. simple_path (moi_lsm_loop e) /\
       pathfinish (moi_lsm_loop e) = pathstart (moi_lsm_loop e) /\
       path_image (moi_lsm_loop e) = frontier moi_lcus_mr`,
  GEN_TAC THEN
  MP_TAC(SPECL [`&0`; `&1`; `&2`; `&3`] MOI_LC0_RECT_ARCS) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `moi_lc0_larc (&0) (&1) = moi_lcus_as /\ moi_lc0_rarc (&2) (&3) = moi_lcus_au /\
                linepath(vector[&1; &0]:real^2,vector[&2; &0]) = moi_lcus_at /\
                linepath(vector[&2; &1]:real^2,vector[&1; &1]) = moi_lcus_av /\
                interval[vector[&0; &0]:real^2,vector[&3; &1]] = moi_lcus_mr`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[moi_lcus_as; moi_lcus_au; moi_lcus_at; moi_lcus_av; moi_lc0_larc;
                moi_lc0_rarc; MOI_LSM_MR_EQ];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image (moi_lsm_rho e o moi_lcus_as) = path_image moi_lcus_au /\
    path_image (moi_lsm_rho e o moi_lcus_au) = path_image moi_lcus_as /\
    arc (moi_lsm_rho e o moi_lcus_as) /\ arc (moi_lsm_rho e o moi_lcus_au)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_COMPOSE; MOI_LSM_RHO_IMAGES; MOI_LSM_RHO_ARC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart (moi_lsm_rho e o moi_lcus_as) = moi_lsm_rho e (vector[&1; &1]) /\
    pathfinish (moi_lsm_rho e o moi_lcus_as) = moi_lsm_rho e (vector[&1; &0]) /\
    pathstart (moi_lsm_rho e o moi_lcus_au) = moi_lsm_rho e (vector[&2; &0]) /\
    pathfinish (moi_lsm_rho e o moi_lcus_au) = moi_lsm_rho e (vector[&2; &1]) /\
    pathstart moi_lcus_at = vector[&1; &0] /\ pathfinish moi_lcus_at = vector[&2; &0] /\
    pathstart moi_lcus_av = vector[&2; &1] /\ pathfinish moi_lcus_av = vector[&1; &1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; MOI_LCUS_SAN_ENDS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_lsm_rho e (vector[&1; &1]) = (if e then vector[&2; &0] else vector[&2; &1]) /\
    moi_lsm_rho e (vector[&1; &0]) = (if e then vector[&2; &1] else vector[&2; &0]) /\
    moi_lsm_rho e (vector[&2; &0]) = (if e then vector[&1; &1] else vector[&1; &0]) /\
    moi_lsm_rho e (vector[&2; &1]) = (if e then vector[&1; &0] else vector[&1; &1])`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_lsm_rho; VECTOR_2] THEN BOOL_CASES_TAC `e:bool` THEN
    REWRITE_TAC[MOI_LC0_VECTOR2_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_loop] THEN
  ASM_CASES_TAC `e:bool` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`moi_lsm_rho T o moi_lcus_as`; `moi_lcus_av`;
                   `moi_lsm_rho T o moi_lcus_au`; `moi_lcus_at`] MOI_LC0_FOUR_ARCS);
    MP_TAC(ISPECL [`moi_lsm_rho F o moi_lcus_as`; `reversepath moi_lcus_at`;
                   `moi_lsm_rho F o moi_lcus_au`; `reversepath moi_lcus_av`]
      MOI_LC0_FOUR_ARCS)] THEN
  ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                  ARC_REVERSEPATH_EQ] THEN
  (ANTS_TAC THENL [REPEAT CONJ_TAC THEN ASM_MESON_TAC[INTER_COMM]; ALL_TAC]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 10: small tools for the assembly.  A set without three distinct     *)
(* points is finite with at most two; psi is continuous off the chords; the *)
(* push keeps the buffer.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_NO_THREE = prove
 (`!s:A->bool. (!a b c. a IN s /\ b IN s /\ c IN s ==> a = b \/ a = c \/ b = c)
               ==> FINITE s /\ CARD s <= 2`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; LE_0] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_CASES_TAC `?b:A. b IN s /\ ~(b = a)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:A->bool) SUBSET {a,b}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `c:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`; `c:A`]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `FINITE (s:A->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a:A,b}` THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {a:A,b}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC];
    SUBGOAL_THEN `s = {a:A}` SUBST1_TAC THENL
     [ASM SET_TAC[];
      SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES; NOT_IN_EMPTY] THEN ARITH_TAC]]);;

let MOI_LSM_PSI_CONT = prove
 (`!e. moi_lsm_psi e continuous_on {z:real^2 | ~(z$1 = &1) /\ ~(z$1 = &2)}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{z:real^2 | ~(z$1 = &1) /\ ~(z$1 = &2)} =
                ({z | z$1 < &1} UNION {z | &2 < z$1}) UNION {z | &1 < z$1 /\ z$1 < &2}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION_OPEN THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNION THEN REWRITE_TAC[MOI_LSM_OPEN_STRIP];
    REWRITE_TAC[MOI_LSM_OPEN_STRIP];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `moi_lsm_rho e` THEN
    REWRITE_TAC[MOI_LSM_RHO_CONTINUOUS; IN_UNION; IN_ELIM_THM; moi_lsm_psi] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\z:real^2. z` THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; IN_ELIM_THM; moi_lsm_psi] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The push keeps the buffer. *)

let MOI_LSM_PDATA_W = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) k H S w.
     moi_lsm_pdata c f g k H S /\ S INTER complex_boundary c SUBSET w /\
     w SUBSET complex_boundary c /\ complex_boundary c SUBSET UNIONS c
     ==> !y. y IN w ==> H y IN w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_pdata] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `complex_boundary c:real^N->bool`)) (concl th) &&
    can (find_term (fun t -> t = `S:real^N->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(y:real^N) IN S` THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 11: the boundary loop.  On [0,1] the touching map traces exactly    *)
(* the D_2 word along moi_lsm_loop e; the pushed map is homotopic to it in *)
(* the buffer through the family hh.                                        *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_d2word = new_definition
 `moi_lsm_d2word (f:real^2->real^N) (g:real^2->real^2) e =
    if e then (f o g o moi_lcus_as) ++ (f o g o moi_lcus_av) ++
              (f o g o moi_lcus_au) ++ (f o g o moi_lcus_at)
    else (f o g o moi_lcus_as) ++ reversepath (f o g o moi_lcus_at) ++
         (f o g o moi_lcus_au) ++ reversepath (f o g o moi_lcus_av)`;;

let MOI_LSM_TM_WORD = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k.
     moi_lsm_setup c f g g' e k
     ==> !t. t IN interval[vec 0,vec 1]
             ==> (moi_lsm_tm f g e o moi_lsm_loop e) t = moi_lsm_d2word f g e t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. z IN moi_lcus_mr /\ (z$1 = &1 \/ z$1 = &2)
                    ==> (f:real^2->real^N) ((g:real^2->real^2) (moi_lsm_rho e z)) = f (g z)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    SIMP_TAC[moi_lsm_setup];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(p:real^1->real^2) t. t IN interval[vec 0,vec 1] ==> p t IN path_image p`
  ASSUME_TAC THENL [REWRITE_TAC[path_image] THEN SET_TAC[]; ALL_TAC] THEN
  (* the four pieces *)
  SUBGOAL_THEN
   `(!t. t IN interval[vec 0,vec 1]
         ==> (moi_lsm_tm f g e o moi_lsm_rho e o moi_lcus_as) t =
             ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcus_as) t) /\
    (!t. t IN interval[vec 0,vec 1]
         ==> (moi_lsm_tm f g e o moi_lsm_rho e o moi_lcus_au) t =
             (f o g o moi_lcus_au) t) /\
    (!t. t IN interval[vec 0,vec 1]
         ==> (moi_lsm_tm f g e o moi_lcus_at) t = (f o g o moi_lcus_at) t) /\
    (!t. t IN interval[vec 0,vec 1]
         ==> (moi_lsm_tm f g e o moi_lcus_av) t = (f o g o moi_lcus_av) t)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `moi_lsm_rho e (moi_lcus_as t) IN path_image moi_lcus_au` MP_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT1(SPEC `e:bool` MOI_LSM_RHO_IMAGES))] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[MOI_LSM_ARCS; IN_ELIM_THM] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`;
                     `moi_lsm_rho e (moi_lcus_as t)`] MOI_LSM_TM_PIECES) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MOI_LSM_IN_MR] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[MOI_LSM_RHO]];
      SUBGOAL_THEN `moi_lsm_rho e (moi_lcus_au t) IN path_image moi_lcus_as` MP_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT2(SPEC `e:bool` MOI_LSM_RHO_IMAGES))] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[MOI_LSM_ARCS; IN_ELIM_THM] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`;
                     `moi_lsm_rho e (moi_lcus_au t)`] MOI_LSM_TM_PIECES) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MOI_LSM_IN_MR] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[MOI_LSM_RHO]];
      SUBGOAL_THEN `moi_lcus_at t IN path_image moi_lcus_at` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_LSM_ARCS; IN_ELIM_THM] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`;
                     `moi_lcus_at t`] MOI_LSM_TM_PIECES) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MOI_LSM_IN_MR] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      SUBGOAL_THEN `moi_lcus_av t IN path_image moi_lcus_av` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_LSM_ARCS; IN_ELIM_THM] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`;
                     `moi_lcus_av t`] MOI_LSM_TM_PIECES) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MOI_LSM_IN_MR] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* reversed pieces *)
  SUBGOAL_THEN
   `(!t. t IN interval[vec 0,vec 1]
         ==> (moi_lsm_tm f g e o reversepath moi_lcus_at) t =
             reversepath ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcus_at) t) /\
    (!t. t IN interval[vec 0,vec 1]
         ==> (moi_lsm_tm f g e o reversepath moi_lcus_av) t =
             reversepath (f o g o moi_lcus_av) t)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PATH_COMPOSE_REVERSEPATH] THEN
    REWRITE_TAC[reversepath; o_THM] THEN CONJ_TAC THEN X_GEN_TAC `t:real^1` THEN
    DISCH_TAC THEN
    (SUBGOAL_THEN `vec 1 - t IN interval[vec 0:real^1,vec 1]` ASSUME_TAC THENL
      [UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
       REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC;
       ALL_TAC]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_THM]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_loop; moi_lsm_d2word] THEN
  ASM_CASES_TAC `e:bool` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
  REPEAT(MATCH_MP_TAC JOIN_PATHS_EQ THEN CONJ_TAC) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 12: the push homotopy of the boundary loop.  The frontier of the    *)
(* model goes into the buffer under tm; the family hh carries tm o loop to  *)
(* pm o loop through loops in the buffer (it is the identity near the      *)
(* middle line, so the two cases paste).                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_TM_FRONTIER_W = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k w z.
     moi_lsm_setup c f g g' e k /\ IMAGE f (relative_frontier std_triangle) SUBSET w /\
     z IN frontier moi_lcus_mr
     ==> moi_lsm_tm f g e z IN w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^2) IN frontier moi_lcus_mr` THEN
    REWRITE_TAC[MOI_LSM_MR_FRONTIER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
    MOI_LSM_TM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
  REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o
              MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^2) (moi_lsm_psi e z) IN relative_frontier std_triangle`
  ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[GSYM moi_lsm_tm];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_tm] THEN ASM SET_TAC[]);;

let MOI_LSM_PUSH_HOM = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k
    (hh:real^1->real^N->real^N) S w d.
     moi_lsm_setup c f g g' e k /\
     (\z. hh (fstcart z) (sndcart z)) continuous_on (interval[vec 0,vec 1] PCROSS UNIONS c) /\
     (!z. z IN UNIONS c ==> hh (vec 0) z = z) /\
     (!t z. t IN interval[vec 0,vec 1] /\ z IN UNIONS c
            ==> hh t z IN UNIONS c /\
                (hh t z IN complex_boundary c <=> z IN complex_boundary c) /\
                (~(z IN S) ==> hh t z = z) /\ (z IN S ==> hh t z IN S)) /\
     S INTER complex_boundary c SUBSET w /\ w SUBSET complex_boundary c /\
     IMAGE f (relative_frontier std_triangle) SUBSET w /\ &0 < d /\
     (!z. z IN moi_lcus_mr /\ abs(z$1 - &3 / &2) < d ==> ~(moi_lsm_tm f g e z IN S))
     ==> homotopic_loops w (moi_lsm_pm (hh (vec 1)) f g e o moi_lsm_loop e)
                           (moi_lsm_tm f g e o moi_lsm_loop e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = moi_lsm_loop e` THEN
  SUBGOAL_THEN `path (L:real^1->real^2) /\ pathfinish L = pathstart L /\
                path_image L = frontier moi_lcus_mr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MESON_TAC[MOI_LSM_LOOP_SIMPLE; SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN interval[vec 0,vec 1] ==> (L:real^1->real^2) s IN frontier moi_lcus_mr`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `path_image (L:real^1->real^2) = frontier moi_lcus_mr` THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN interval[vec 0,vec 1] ==> (L:real^1->real^2) s IN moi_lcus_mr`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(L:real^1->real^2) s IN frontier moi_lcus_mr` MP_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[MOI_LSM_MR_FRONTIER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN interval[vec 0,vec 1]
                    ==> moi_lsm_tm (f:real^2->real^N) g e ((L:real^1->real^2) s) IN w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LSM_TM_FRONTIER_W THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g':real^2->real^2`; `k:real^N->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[complex_boundary] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t y. t IN interval[vec 0,vec 1] /\ y IN w ==> (hh:real^1->real^N->real^N) t y IN w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^1`; `y:real^N`] o check (fun th ->
      is_forall (concl th) && length (fst(strip_forall (concl th))) = 2 &&
      can (find_term (fun t -> t = `S:real^N->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN S` THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN REWRITE_TAC[HOMOTOPIC_LOOPS] THEN
  EXISTS_TAC
   `\z:real^(1,1)finite_sum.
      if ((L:real^1->real^2) (sndcart z))$1 <= &3 / &2
      then (hh:real^1->real^N->real^N) (fstcart z)
             (moi_lsm_tm (f:real^2->real^N) g e (L (sndcart z)))
      else moi_lsm_tm f g e (L (sndcart z))` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; o_THM] THEN
  SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e continuous_on moi_lcus_mr` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`] MOI_LSM_TM_PL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup; pl_homeomorphism; moi_lt_normal2_disk; moi_lt_normal_disk;
                moi_lt_singular_disk] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^1->real^2) continuous_on interval[vec 0,vec 1]` ASSUME_TAC THENL
   [ASM_MESON_TAC[path]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,1)finite_sum. moi_lsm_tm (f:real^2->real^N) g e ((L:real^1->real^2) (sndcart z)))
    continuous_on (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; CONTINUOUS_ON_EMPTY];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* continuity *)
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      SUBGOAL_THEN
       `(\z:real^(1,1)finite_sum. (hh:real^1->real^N->real^N) (fstcart z)
          (moi_lsm_tm (f:real^2->real^N) g e ((L:real^1->real^2) (sndcart z)))) =
        (\z:real^(1,N)finite_sum. hh (fstcart z) (sndcart z)) o
        (\z:real^(1,1)finite_sum. pastecart (fstcart z) (moi_lsm_tm f g e (L (sndcart z))))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS UNIONS (c:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                    SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; CONTINUOUS_ON_EMPTY];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART;
                  FSTCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(L:real^1->real^2) y IN moi_lcus_mr /\
                    moi_lsm_tm (f:real^2->real^N) g e (L y) IN UNIONS c /\
                    ~(moi_lsm_tm f g e (L y) IN S)` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `(L:real^1->real^2) y IN moi_lcus_mr` ASSUME_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e ((L:real^1->real^2) y) IN w`
          MP_TAC THENL [ASM_SIMP_TAC[]; ASM SET_TAC[]];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
            can (find_term (fun t -> t = `abs`)) (concl th))) THEN
          ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`;
        `moi_lsm_tm (f:real^2->real^N) g e ((L:real^1->real^2) y)`] o check (fun th ->
        is_forall (concl th) && length (fst(strip_forall (concl th))) = 2 &&
        can (find_term (fun t -> t = `S:real^N->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      FIRST_ASSUM ACCEPT_TAC];
    (* in the buffer *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    (* time 0 *)
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e ((L:real^1->real^2) s) IN UNIONS c`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    (* time 1 *)
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[moi_lsm_pm];
    (* loops *)
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[pathstart; pathfinish; o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    UNDISCH_TAC `pathfinish (L:real^1->real^2) = pathstart L` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 13: the new disk f2 = pm o p, for a PL homeomorphism p of           *)
(* std_triangle onto the model, boundary onto frontier.  It is a singular   *)
(* disk, its double image is that of f minus k, the crossing2 charts pass   *)
(* to it by MOI_LC0_CROSSING2_TRANSFER, it is normal2, and its complexity   *)
(* is smaller.                                                              *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_f2data = new_definition
 `moi_lsm_f2data (c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k
                 (H:real^N->real^N) S d (p:real^2->real^2) q <=>
    moi_lsm_setup c f g g' e k /\ moi_lsm_pdata c f g k H S /\ &0 < d /\
    (!z. z IN moi_lcus_mr /\ abs(z$1 - &3 / &2) < d ==> ~(moi_lsm_tm f g e z IN S)) /\
    pl_homeomorphism (std_triangle,moi_lcus_mr) (p,q) /\
    IMAGE p (relative_frontier std_triangle) = frontier moi_lcus_mr`;;

(* Basic facts on p. *)

let MOI_LSM_P_FACTS = prove
 (`!(p:real^2->real^2) q.
     pl_homeomorphism (std_triangle,moi_lcus_mr) (p,q) /\
     IMAGE p (relative_frontier std_triangle) = frontier moi_lcus_mr
     ==> pl_map_on std_triangle p /\ p continuous_on std_triangle /\
         (!x. x IN std_triangle ==> p x IN moi_lcus_mr /\ q (p x) = x) /\
         (!z. z IN moi_lcus_mr ==> q z IN std_triangle /\ p (q z) = z) /\
         (!x. x IN std_triangle
              ==> (p x IN frontier moi_lcus_mr <=> x IN relative_frontier std_triangle))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `relative_frontier std_triangle SUBSET std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    MESON_TAC[SIMPLEX_IMP_CLOSED; MOI_LTD_STD_TRIANGLE_SIMPLEX];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (p:real^2->real^2) (relative_frontier std_triangle) =
                 frontier moi_lcus_mr` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^2 = x0` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[SUBSET]]);;

(* (A) a singular disk *)

let MOI_LSM_F2_SINGULAR = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S d p q.
     moi_lsm_f2data c f g g' e k H S d p q
     ==> moi_lt_singular_disk c (moi_lsm_pm H f g e o p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_f2data] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^2->real^2`; `q:real^2->real^2`] MOI_LSM_P_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                 `S:real^N->bool`; `d:real`] MOI_LSM_PM_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z:real^2. z IN moi_lcus_mr
       ==> moi_lsm_pm (H:real^N->real^N) f g e z IN UNIONS c /\
           (moi_lsm_pm H f g e z IN complex_boundary c <=> z IN frontier moi_lcus_mr)`
  (LABEL_TAC "PF") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                         `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                         `S:real^N->bool`] MOI_LSM_PM_FACTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lt_singular_disk; o_THM] THEN REPEAT CONJ_TAC THENL
   [(* PL *)
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_lcus_mr` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* image *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
    (* boundary *)
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^2->real^2) x IN frontier moi_lcus_mr` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
        SUBGOAL_THEN `relative_frontier std_triangle SUBSET std_triangle` MP_TAC THENL
         [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
          MESON_TAC[SIMPLEX_IMP_CLOSED; MOI_LTD_STD_TRIANGLE_SIMPLEX];
          SET_TAC[]];
        ALL_TAC] THEN
      ASM_MESON_TAC[]];
    (* local injectivity *)
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                   `S:real^N->bool`; `d:real`; `(p:real^2->real^2) x`] MOI_LSM_PM_LOCINJ) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real^2->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`p:real^2->real^2`; `std_triangle`; `n:real^2->bool`]
      CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `o1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!x':real^2. x' IN std_triangle /\ x' IN o1 ==> (p:real^2->real^2) x' IN n`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x':real^2) IN {x | x IN std_triangle /\ (p:real^2->real^2) x IN n}`
      MP_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; SIMP_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (p:real^2->real^2) x IN n}`
      MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `z:real^2`] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^2->real^2) y = p z` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `n:real^2->bool`)) (concl th) &&
      length (fst(strip_forall (concl th))) = 2)) THEN
    ASM_SIMP_TAC[];
    (* fibres *)
    X_GEN_TAC `y:real^N` THEN MATCH_MP_TAC MOI_LSM_NO_THREE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c':real^2`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                   `S:real^N->bool`; `y:real^N`; `(p:real^2->real^2) a`;
                   `(p:real^2->real^2) b`; `(p:real^2->real^2) c'`] MOI_LSM_PM_FIBRE) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]);;

(* (B) the double image *)

let MOI_LSM_F2_DI = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S d p q.
     moi_lsm_f2data c f g g' e k H S d p q
     ==> moi_lt_double_image (moi_lsm_pm H f g e o p) = moi_lt_double_image f DIFF k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_f2data]) THEN
  MP_TAC(ISPECL [`p:real^2->real^2`; `q:real^2->real^2`] MOI_LSM_P_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_DIFF] THEN EQ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [moi_lt_double_image] THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                   `S:real^N->bool`; `(p:real^2->real^2) x`; `(p:real^2->real^2) x'`;
                   `y:real^N`] MOI_LSM_PM_DOUBLE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                   `S:real^N->bool`; `y:real^N`] MOI_LSM_PM_ONTO) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `z':real^2` STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM; o_THM] THEN
    MAP_EVERY EXISTS_TAC [`(q:real^2->real^2) z`; `(q:real^2->real^2) z'`] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 14: the crossing2 charts of f2 (MOI_LC0_CROSSING2_TRANSFER with the  *)
(* source map g o psi o p over the complement of S), normality, and the    *)
(* drop of complexity.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_F2_CROSSING2 = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S d p q y.
     moi_lsm_f2data c f g g' e k H S d p q /\
     y IN moi_lt_double_image (moi_lsm_pm H f g e o p)
     ==> moi_lt_crossing2_at c (moi_lsm_pm H f g e o p) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                 `S:real^N->bool`; `d:real`; `p:real^2->real^2`; `q:real^2->real^2`]
    MOI_LSM_F2_DI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_f2data]) THEN
  MP_TAC(ISPECL [`p:real^2->real^2`; `q:real^2->real^2`] MOI_LSM_P_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_setup]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_pdata]) THEN
  SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f /\ ~(y IN k)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LC0_CROSSING2_TRANSFER THEN
  MAP_EVERY EXISTS_TAC
   [`f:real^2->real^N`; `\x:real^2. (g:real^2->real^2) (moi_lsm_psi e ((p:real^2->real^2) x))`;
    `(:real^N) DIFF S`] THEN
  (* facts used below *)
  SUBGOAL_THEN `!z:real^2. z IN moi_lcus_mr
                  ==> (g:real^2->real^2) (moi_lsm_psi e z) IN std_triangle /\
                      moi_lsm_tm (f:real^2->real^N) g e z IN UNIONS c /\
                      (moi_lsm_tm f g e z IN k <=> z$1 = &1 \/ z$1 = &2)`
  (LABEL_TAC "TF") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `z:real^2`]
      MOI_LSM_TM_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* on the preimage of the complement of S, f2 = tm o p *)
  SUBGOAL_THEN
   `!x:real^2. x IN std_triangle /\
               (moi_lsm_pm (H:real^N->real^N) f g e o p) x IN (:real^N) DIFF S
       ==> (moi_lsm_pm H f g e o p) x = moi_lsm_tm f g e (p x) /\
           ~(moi_lsm_tm f g e (p x) IN S)`
  (LABEL_TAC "OFF") THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[o_THM; IN_DIFF; IN_UNIV; moi_lsm_pm] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e ((p:real^2->real^2) x) IN UNIONS c`
    ASSUME_TAC THENL [USE_THEN "TF" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
    UNDISCH_TAC `~((if ((p:real^2->real^2) x)$1 <= &3 / &2
                    then (H:real^N->real^N) (moi_lsm_tm f g e (p x))
                    else moi_lsm_tm f g e (p x)) IN S)` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(moi_lsm_tm (f:real^2->real^N) g e ((p:real^2->real^2) x) IN S)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* crossing2 for f *)
    UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_normal2_disk] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    (* open *)
    REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[];
    (* y off S *)
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    UNDISCH_TAC `DISJOINT S (moi_lt_double_image (f:real^2->real^N) DIFF k)` THEN
    ASM SET_TAC[];
    (* the source map *)
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    USE_THEN "OFF" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "TF" (fun th -> ASM_SIMP_TAC[th]) THEN REWRITE_TAC[moi_lsm_tm];
    (* continuity *)
    SUBGOAL_THEN
     `!x:real^2. x IN std_triangle /\
                 (moi_lsm_pm (H:real^N->real^N) f g e o p) x IN (:real^N) DIFF S
         ==> (p:real^2->real^2) x IN moi_lcus_mr /\ ~((p x)$1 = &1) /\ ~((p x)$1 = &2)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      USE_THEN "OFF" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(p:real^2->real^2) x IN moi_lcus_mr` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(moi_lsm_tm (f:real^2->real^N) g e ((p:real^2->real^2) x) IN k)` MP_TAC THENL
       [UNDISCH_TAC `~(moi_lsm_tm (f:real^2->real^N) g e ((p:real^2->real^2) x) IN S)` THEN
        UNDISCH_TAC `(k:real^N->bool) SUBSET S` THEN SET_TAC[];
        USE_THEN "TF" (fun th -> ASM_SIMP_TAC[th]) THEN CONV_TAC TAUT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x:real^2. (g:real^2->real^2) (moi_lsm_psi e ((p:real^2->real^2) x))) =
                  g o moi_lsm_psi e o p`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{z:real^2 | ~(z$1 = &1) /\ ~(z$1 = &2)}` THEN
        REWRITE_TAC[MOI_LSM_PSI_CONT] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
          can (find_term (fun t -> t = `(:real^N) DIFF S`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `pl_homeomorphism (moi_lcus_mr,std_triangle) (g:real^2->real^2,g')` THEN
        SIMP_TAC[pl_homeomorphism; homeomorphism];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`e:bool`; `(p:real^2->real^2) x`] MOI_LSM_PSI_INV) THEN
        ANTS_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
            can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
            can (find_term (fun t -> t = `(:real^N) DIFF S`)) (concl th))) THEN
          ASM_REWRITE_TAC[o_THM];
          SIMP_TAC[]]]];
    (* surjectivity *)
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g':real^2->real^2) z IN moi_lcus_mr /\ g (g' z) = z` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(((g':real^2->real^2) z)$1 = &1) /\ ~((g' z)$1 = &2)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~((f:real^2->real^N) ((g:real^2->real^2) ((g':real^2->real^2) z)) IN k)`
      MP_TAC THENL
       [UNDISCH_TAC `~((f:real^2->real^N) z IN S)` THEN
        UNDISCH_TAC `(k:real^N->bool) SUBSET S` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        ASM_SIMP_TAC[] THEN CONV_TAC TAUT];
      ALL_TAC] THEN
    MP_TAC(SPECL [`e:bool`; `(g':real^2->real^2) z`] MOI_LSM_PSI_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `(q:real^2->real^2) (moi_lsm_psi e ((g':real^2->real^2) z))` THEN
    ASM_SIMP_TAC[o_THM] THEN
    SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e (moi_lsm_psi e ((g':real^2->real^2) z)) =
                  f z` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_lsm_tm]; ALL_TAC] THEN
    SUBGOAL_THEN `(H:real^N->real^N) ((f:real^2->real^N) z) = f z` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^2->real^N) z` o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `complex_boundary c:real^N->bool`)) (concl th) &&
        can (find_term (fun t -> t = `S:real^N->bool`)) (concl th))) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
        REWRITE_TAC[moi_lt_normal2_disk; moi_lt_normal_disk; moi_lt_singular_disk] THEN
        ASM SET_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_lsm_pm] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    (* the double images agree off S *)
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* (D) normal2 and (E) the complexity. *)

let MOI_LSM_F2_NORMAL2 = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k H S d p q.
     moi_lsm_f2data c f g g' e k H S d p q
     ==> moi_lt_normal2_disk c (moi_lsm_pm H f g e o p) /\
         moi_lt_disk_complexity (moi_lsm_pm H f g e o p) < moi_lt_disk_complexity f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                 `S:real^N->bool`; `d:real`; `p:real^2->real^2`; `q:real^2->real^2`]
    MOI_LSM_F2_DI) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `H:real^N->real^N`;
                 `S:real^N->bool`; `d:real`; `p:real^2->real^2`; `q:real^2->real^2`]
    MOI_LSM_F2_SINGULAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN moi_lt_double_image (moi_lsm_pm H f g e o (p:real^2->real^2))
                    ==> moi_lt_crossing2_at c (moi_lsm_pm H f g e o p) (y:real^N)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LSM_F2_CROSSING2 THEN
    MAP_EVERY EXISTS_TAC [`g':real^2->real^2`; `k:real^N->bool`; `S:real^N->bool`;
                          `d:real`; `q:real^2->real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_f2data]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_setup]) THEN
  (* every component is inside or outside DI(f) minus k *)
  SUBGOAL_THEN
   `!k'. k' IN components (moi_lt_double_image (f:real^2->real^N))
         ==> k' SUBSET moi_lt_double_image f DIFF k \/
             DISJOINT k' (moi_lt_double_image f DIFF k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k':real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k':real^N->bool = k` THENL
     [DISJ2_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISJ1_TAC THEN
    SUBGOAL_THEN `DISJOINT (k':real^N->bool) k` MP_TAC THENL
     [ASM_MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT];
      MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`; `k':real^N->bool`]
        IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_lt_normal2_disk; moi_lt_normal_disk] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
      REWRITE_TAC[moi_lt_normal2_disk; moi_lt_normal_disk] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:(real^N->bool)->bool` STRIP_ASSUME_TAC)
          ASSUME_TAC)) ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_LA2_SUBCOMPLEX_MANIFOLD THEN
      EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LT2D_CROSSING2_IMP THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the complexity drops *)
  REWRITE_TAC[moi_lt_disk_complexity] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (components (moi_lt_double_image (f:real^2->real^N)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `components (moi_lt_double_image (f:real^2->real^N) DIFF k) SUBSET
                components (moi_lt_double_image f) DELETE k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`;
                   `moi_lt_double_image (f:real^2->real^N) DIFF k`]
      MOI_LA2_UNION_COMPONENTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((k:real^N->bool) IN components (moi_lt_double_image f DIFF k))` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `~(k:real^N->bool = {}) /\ k SUBSET moi_lt_double_image f DIFF k`
      MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC IN_COMPONENTS_NONEMPTY THEN
          EXISTS_TAC `moi_lt_double_image (f:real^2->real^N) DIFF k` THEN
          FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
        SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `CARD (components (moi_lt_double_image (f:real^2->real^N)) DELETE k) + 1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `a <= b ==> a < b + 1`) THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_DELETE];
    ASM_SIMP_TAC[CARD_DELETE] THEN
    SUBGOAL_THEN `~(CARD (components (moi_lt_double_image (f:real^2->real^N))) = 0)`
    MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
      ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Part 15: the assembly.  SEAM_FROM_PUSH : |- MOI_LSM_PUSH ==>             *)
(* MOI_LCUS_SEAM.  From the model, the setup and the double arc k; the push *)
(* family hh and its support S; the band; a PL homeomorphism p from         *)
(* std_triangle onto the model whose boundary loop is the D_2 model loop     *)
(* (MOI_LC0_DISK_LOOP); the new disk f2 = pm o p is normal2 of smaller      *)
(* complexity, and its boundary loop is homotopic in w, through pm o loop   *)
(* and tm o loop, to the D_2 word.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_SEAM_FROM_PUSH = prove
 (mk_imp(MOI_LSM_PUSH, MOI_LCUS_SEAM),
  DISCH_THEN(LABEL_TAC "PUSH") THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`;
                       `g:real^2->real^2`; `e:bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LSM_SETUP_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `k IN components (moi_lt_double_image (f:real^2->real^N)) /\
    {x | x IN std_triangle /\ f x IN k} =
    IMAGE (g:real^2->real^2) (segment[vector[&1; &0],vector[&1; &1]] UNION
                              segment[vector[&2; &0],vector[&2; &1]])`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the push *)
  USE_THEN "PUSH" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `w:real^N->bool`; `g:real^2->real^2`; `e:bool`; `k:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:real^1->real^N->real^N` (X_CHOOSE_THEN `S:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(vec 1:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lsm_pdata c (f:real^2->real^N) g k ((hh:real^1->real^N->real^N) (vec 1)) S`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_lsm_pdata] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`vec 1:real^1`; `z:real^N`] o check (fun th ->
      is_forall (concl th) && length (fst(strip_forall (concl th))) = 2 &&
      can (find_term (fun t -> t = `S:real^N->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the band *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `S:real^N->bool`]
    MOI_LSM_BAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  (* the parametrization of the model *)
  MP_TAC(ISPECL [`moi_lcus_mr`; `moi_lsm_loop e`] MOI_LC0_DISK_LOOP) THEN
  ANTS_TAC THENL [REWRITE_TAC[MOI_LSM_MR_FACTS; MOI_LSM_LOOP_SIMPLE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^2` (X_CHOOSE_THEN `q:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_lsm_f2data c (f:real^2->real^N) g g' e k
                  ((hh:real^1->real^N->real^N) (vec 1)) S d p q`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_lsm_f2data]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`;
                 `(hh:real^1->real^N->real^N) (vec 1)`; `S:real^N->bool`; `d:real`;
                 `p:real^2->real^2`; `q:real^2->real^2`] MOI_LSM_F2_NORMAL2) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  EXISTS_TAC `moi_lsm_pm ((hh:real^1->real^N->real^N) (vec 1)) f g e o (p:real^2->real^2)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM moi_lsm_d2word] THEN
  (* facts for the loops *)
  SUBGOAL_THEN `(w:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `complex_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[complex_boundary] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN frontier moi_lcus_mr
                  ==> moi_lsm_tm (f:real^2->real^N) g e z IN w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LSM_TM_FRONTIER_W THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g':real^2->real^2`; `k:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN w ==> (hh:real^1->real^N->real^N) (vec 1) y IN w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                         `k:real^N->bool`; `(hh:real^1->real^N->real^N) (vec 1)`;
                         `S:real^N->bool`; `w:real^N->bool`] MOI_LSM_PDATA_W) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier moi_lcus_mr SUBSET moi_lcus_mr` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_LSM_MR_FRONTIER] THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`;
                 `(hh:real^1->real^N->real^N) (vec 1)`; `S:real^N->bool`; `d:real`]
    MOI_LSM_PM_PL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_lsm_tm (f:real^2->real^N) g e continuous_on moi_lcus_mr` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `e:bool`] MOI_LSM_TM_PL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup; pl_homeomorphism; moi_lt_normal2_disk; moi_lt_normal_disk;
                moi_lt_singular_disk] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `e:bool` MOI_LSM_LOOP_SIMPLE) THEN STRIP_TAC THEN
  (* p o loop ~ the model loop, under pm *)
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `moi_lsm_pm ((hh:real^1->real^N->real^N) (vec 1)) f g e o moi_lsm_loop e` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM o_ASSOC] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `frontier moi_lcus_mr` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[moi_lsm_pm] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `moi_lsm_tm (f:real^2->real^N) g e o moi_lsm_loop e` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                         `g':real^2->real^2`; `e:bool`; `k:real^N->bool`;
                         `hh:real^1->real^N->real^N`; `S:real^N->bool`; `w:real^N->bool`;
                         `d:real`] MOI_LSM_PUSH_HOM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* tm o loop is the word *)
  MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE];
    MATCH_MP_TAC MOI_LSM_TM_WORD THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g':real^2->real^2`; `k:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 16: the model push in real^3.  moi_lsm_sn is the sup norm,          *)
(* moi_lsm_bump c r a tent of height r on the cube of centre c and half    *)
(* side r, and moi_lsm_p3 t c r z = z + (t/4) bump(z) (-1,1,0): for t in    *)
(* [0,1] it is injective (the bump is 1-Lipschitz for the sup norm), the    *)
(* identity off the open cube, keeps the open cube and the third           *)
(* coordinate, keeps the open quadrant z1 < 0 < z2, and for t > 0 sends    *)
(* the seam-1 half-planes inside the open cube into that quadrant.  It is  *)
(* PL for fixed t and jointly continuous in (t,z).                          *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_sn = new_definition
 `moi_lsm_sn (z:real^3) = max (abs(z$1)) (max (abs(z$2)) (abs(z$3)))`;;

let moi_lsm_bump = new_definition
 `moi_lsm_bump (c:real^3) r (z:real^3) = max (&0) (r - moi_lsm_sn (z - c))`;;

let moi_lsm_p3 = new_definition
 `moi_lsm_p3 t (c:real^3) r (z:real^3) =
    z + ((t / &4) * moi_lsm_bump c r z) % vector[--(&1); &1; &0]:real^3`;;

let MOI_LSM_SN = prove
 (`!z z':real^3.
     &0 <= moi_lsm_sn z /\
     abs(z$1) <= moi_lsm_sn z /\ abs(z$2) <= moi_lsm_sn z /\ abs(z$3) <= moi_lsm_sn z /\
     abs(moi_lsm_sn z - moi_lsm_sn z') <= moi_lsm_sn (z - z') /\
     (moi_lsm_sn z = &0 <=> z = vec 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_lsm_sn; VECTOR_SUB_COMPONENT; CART_EQ; DIMINDEX_3; FORALL_3;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_LSM_BUMP = prove
 (`!(c:real^3) r z z'.
     &0 <= moi_lsm_bump c r z /\
     (moi_lsm_sn (z - c) < r ==> moi_lsm_bump c r z = r - moi_lsm_sn (z - c)) /\
     (r <= moi_lsm_sn (z - c) ==> moi_lsm_bump c r z = &0) /\
     abs(moi_lsm_bump c r z - moi_lsm_bump c r z') <= moi_lsm_sn (z - z')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_bump] THEN
  MP_TAC(ISPECL [`z - c:real^3`; `z' - c:real^3`] MOI_LSM_SN) THEN
  REWRITE_TAC[VECTOR_ARITH `(z - c) - (z' - c):real^3 = z - z'`] THEN REAL_ARITH_TAC);;

let MOI_LSM_P3_COMPONENTS = prove
 (`!t (c:real^3) r z.
     moi_lsm_p3 t c r z $1 = z$1 - (t / &4) * moi_lsm_bump c r z /\
     moi_lsm_p3 t c r z $2 = z$2 + (t / &4) * moi_lsm_bump c r z /\
     moi_lsm_p3 t c r z $3 = z$3`,
  REWRITE_TAC[moi_lsm_p3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  REAL_ARITH_TAC);;

let MOI_LSM_P3_INJ = prove
 (`!t (c:real^3) r z z'.
     &0 <= t /\ t <= &1 /\ moi_lsm_p3 t c r z = moi_lsm_p3 t c r z' ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[CART_EQ; DIMINDEX_3; FORALL_3;
                                       MOI_LSM_P3_COMPONENTS]) THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2
    (ISPECL [`c:real^3`; `r:real`; `z:real^3`; `z':real^3`] MOI_LSM_BUMP)))) THEN
  REWRITE_TAC[moi_lsm_sn; VECTOR_SUB_COMPONENT] THEN
  ABBREV_TAC `b = moi_lsm_bump c r (z:real^3)` THEN
  ABBREV_TAC `b' = moi_lsm_bump c r (z':real^3)` THEN
  SUBGOAL_THEN `abs(t / &4 * b - t / &4 * b') <= abs(b - b') / &4` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(t / &4) = t / &4` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(t * inv(&4)) * x = (t * x) * inv(&4)`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ABBREV_TAC `pp = t / &4 * b` THEN ABBREV_TAC `pp' = t / &4 * b'` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN REAL_ARITH_TAC);;

let MOI_LSM_P3_FIX = prove
 (`!t (c:real^3) r z. r <= moi_lsm_sn (z - c) ==> moi_lsm_p3 t c r z = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lsm_p3] THEN
  MP_TAC(ISPECL [`c:real^3`; `r:real`; `z:real^3`; `z:real^3`] MOI_LSM_BUMP) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_LSM_P3_CUBE = prove
 (`!t (c:real^3) r z.
     &0 <= t /\ t <= &1 /\ moi_lsm_sn (z - c) < r
     ==> moi_lsm_sn (moi_lsm_p3 t c r z - c) < r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3`; `r:real`; `z:real^3`; `z:real^3`] MOI_LSM_BUMP) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_lsm_sn; VECTOR_SUB_COMPONENT; MOI_LSM_P3_COMPONENTS] THEN
  UNDISCH_TAC `moi_lsm_sn (z - c) < r` THEN
  REWRITE_TAC[moi_lsm_sn; VECTOR_SUB_COMPONENT] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= t / &4 * (r - moi_lsm_sn (z - c)) /\
                t / &4 * (r - moi_lsm_sn (z - c)) <= (r - moi_lsm_sn (z - c)) / &4`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `t * inv(&4) * x = (t * x) * inv(&4)`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[moi_lsm_sn; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC]);;

let MOI_LSM_P3_SIDES = prove
 (`!t (c:real^3) r z.
     &0 <= t
     ==> ((z$1 < &0 ==> moi_lsm_p3 t c r z $1 < &0) /\
          (&0 < z$2 ==> &0 < moi_lsm_p3 t c r z $2)) /\
         (&0 < t /\ moi_lsm_sn (z - c) < r /\
          ((z$1 = &0 /\ &0 <= z$2) \/ (z$2 = &0 /\ z$1 <= &0))
          ==> moi_lsm_p3 t c r z $1 < &0 /\ &0 < moi_lsm_p3 t c r z $2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MOI_LSM_P3_COMPONENTS] THEN
  MP_TAC(ISPECL [`c:real^3`; `r:real`; `z:real^3`; `z:real^3`] MOI_LSM_BUMP) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t / &4 * moi_lsm_bump c r (z:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < t / &4 * moi_lsm_bump c r (z:real^3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* PL for fixed t and joint continuity. *)

let MOI_LSM_SN_PL = prove
 (`!(c:real^3). pl_map_on (:real^3) (\z. lift(moi_lsm_sn (z - c)))`,
  GEN_TAC THEN REWRITE_TAC[moi_lsm_sn] THEN
  SUBGOAL_THEN `!i. pl_map_on (:real^3) (\z:real^3. lift((z - c)$i))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^3. (\x:real^3. lift(x$i)) z + (--(lift((c:real^3)$i)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_COMPONENT; LIFT_SUB; IN_UNIV] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. pl_map_on (:real^3) (\z:real^3. lift(abs((z - c)$i)))` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\z:real^3. lift(abs((z - c)$i))) =
                  (\z. lift(max (drop(lift((z - c)$i))) (drop(--(lift((z - c)$i))))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; DROP_NEG; LIFT_DROP; LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_LIFT_MAX THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `--x:real^1 = --(&1) % x`] THEN
    MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]);;

let MOI_LSM_BUMP_PL = prove
 (`!(c:real^3) r. pl_map_on (:real^3) (\z. lift(moi_lsm_bump c r z))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (:real^3)` ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_bump] THEN MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[PL_MAP_ON_CONST];
    REWRITE_TAC[LIFT_SUB] THEN
    SUBGOAL_THEN `(\z:real^3. lift r - lift(moi_lsm_sn (z - c))) =
                  (\z. --(&1) % lift(moi_lsm_sn (z - c)) + lift r)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_SIMP_TAC[PL_MAP_ON_CONST] THEN
    MATCH_MP_TAC PL_MAP_ON_CMUL THEN REWRITE_TAC[MOI_LSM_SN_PL]]);;

let MOI_LSM_P3_PL = prove
 (`!t (c:real^3) r. pl_map_on (:real^3) (moi_lsm_p3 t c r)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (:real^3) /\ locally_polyhedral (:real^1)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real^3`; `r:real`] MOI_LSM_BUMP_PL) THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_lsm_p3 t c r =
                (\z:real^3. z + (\x:real^1. drop x % vector[--(&1); &1; &0]:real^3)
                                  ((t / &4) % lift(moi_lsm_bump c r z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_lsm_p3; DROP_CMUL; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(\x:real^1. drop x % vector[--(&1); &1; &0]:real^3) =
                  (\x. (\x. drop x % vector[--(&1); &1; &0]) x + vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC]);;

let MOI_LSM_BUMP_CONT = prove
 (`!(c:real^3) r. (\z. lift(moi_lsm_bump c r z)) continuous_on (:real^3)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[MOI_LSM_BUMP_PL]);;

let MOI_LSM_P3_CONT = prove
 (`!(c:real^3) r s.
     (\w:real^(1,3)finite_sum. moi_lsm_p3 (drop(fstcart w)) c r (sndcart w))
     continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_p3] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; REAL_ARITH `!x. x / &4 = inv(&4) * x`; LIFT_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    SUBGOAL_THEN `(\w:real^(1,3)finite_sum. lift(moi_lsm_bump c r (sndcart w))) =
                  (\z. lift(moi_lsm_bump c r z)) o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV; MOI_LSM_BUMP_CONT]]);;

(* ------------------------------------------------------------------------- *)
(* Part 17: the push in one chart.  moi_lsm_chart c u h h' is a crossing   *)
(* chart domain without the sheets: u open in UNIONS c, h a PL             *)
(* homeomorphism onto the unit ball (u off the boundary) or onto the half  *)
(* ball with the boundary going to z3 = 0.  moi_lsm_cube cc r: a cube of   *)
(* centre cc and half side r whose closure is in the unit ball.  The push  *)
(* moi_lsm_cp is h' o P o h on u and the identity elsewhere; it keeps      *)
(* UNIONS c and the boundary, is the identity off the open cube, is        *)
(* injective, PL, and jointly continuous in the time.                       *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_chart = new_definition
 `moi_lsm_chart (c:(real^N->bool)->bool) u (h:real^N->real^3) h' <=>
    open_in (subtopology euclidean (UNIONS c)) u /\
    pl_homeomorphism (u,IMAGE h u) (h,h') /\
    ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
     (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
      IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0}))`;;

let moi_lsm_cube = new_definition
 `moi_lsm_cube (cc:real^3) r <=>
    &0 < r /\ !z. moi_lsm_sn (z - cc) <= r ==> z IN ball(vec 0:real^3,&1)`;;

let moi_lsm_cp = new_definition
 `moi_lsm_cp (u:real^N->bool) (h:real^N->real^3) h' cc r (t:real^1) z =
    if z IN u then h' (moi_lsm_p3 (drop t) cc r (h z)) else z`;;

let MOI_LSM_P3_ZERO = prove
 (`!(cc:real^3) r z. moi_lsm_p3 (&0) cc r z = z`,
  REWRITE_TAC[moi_lsm_p3; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_LSM_CHART_FACTS = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h'.
     moi_lsm_chart c u h h'
     ==> u SUBSET UNIONS c /\
         (!z. z IN u ==> h z IN IMAGE h u /\ h' (h z) = z) /\
         (!w. w IN IMAGE h u ==> h' w IN u /\ h (h' w) = w) /\
         h continuous_on u /\ h' continuous_on IMAGE h u /\
         pl_map_on u h /\ pl_map_on (IMAGE h u) h' /\
         IMAGE h u SUBSET ball(vec 0,&1) /\
         (!w w'. w IN IMAGE h u /\ w' IN ball(vec 0,&1) /\ w'$3 = w$3 ==> w' IN IMAGE h u) /\
         (!z z'. z IN u /\ z' IN u /\ (h z)$3 = (h z')$3
                 ==> (z IN complex_boundary c <=> z' IN complex_boundary c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_chart; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "D"))) THEN
  SUBGOAL_THEN `u SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) u SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [USE_THEN "D" (DISJ_CASES_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Da") (LABEL_TAC "Db"))) THENL
     [USE_THEN "Db" (fun th -> REWRITE_TAC[th; SUBSET_REFL]);
      USE_THEN "Da" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w w':real^3. w IN IMAGE (h:real^N->real^3) u /\ w' IN ball(vec 0,&1) /\
                              w'$3 = w$3 ==> w' IN IMAGE h u`
  ASSUME_TAC THENL
   [USE_THEN "D" (DISJ_CASES_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Da") (LABEL_TAC "Db"))) THENL
     [USE_THEN "Db" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
      USE_THEN "Da" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z z'. z IN u /\ z' IN u /\ ((h:real^N->real^3) z)$3 = (h z')$3
                       ==> (z IN complex_boundary c <=> z' IN complex_boundary c)`
  ASSUME_TAC THENL
   [USE_THEN "D" (DISJ_CASES_THEN (CONJUNCTS_THEN2 (LABEL_TAC "Da") (LABEL_TAC "Db"))) THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC `u INTER complex_boundary (c:(real^N->bool)->bool) = {}` THEN
      UNDISCH_TAC `(z:real^N) IN u` THEN UNDISCH_TAC `(z':real^N) IN u` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!z. z IN u ==> (z IN complex_boundary c <=> ((h:real^N->real^3) z)$3 = &0)`
      (fun th -> SIMP_TAC[th]) THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(h:real^N->real^3) z IN IMAGE h (u INTER complex_boundary c)` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[];
        USE_THEN "Db" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[IN_INTER; IN_ELIM_THM]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(h:real^N->real^3) z IN IMAGE h (u INTER complex_boundary c)` MP_TAC THENL
       [USE_THEN "Db" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE; ALL_TAC] THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z':real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^N = z'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `IMAGE (h':real^3->real^N) (IMAGE h u) = u` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

(* The push keeps the chart image. *)

let MOI_LSM_CP_DOM = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r s w.
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r /\ &0 <= s /\ s <= &1 /\ w IN IMAGE h u
     ==> moi_lsm_p3 s cc r w IN IMAGE h u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  ASM_CASES_TAC `moi_lsm_sn (w - cc) < r` THENL
   [ALL_TAC; ASM_SIMP_TAC[MOI_LSM_P3_FIX; GSYM REAL_NOT_LT]] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`w:real^3`; `moi_lsm_p3 s cc r (w:real^3)`] o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
    can (find_term (fun t -> t = `ball(vec 0:real^3,&1)`)) (concl th))) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOI_LSM_P3_COMPONENTS] THEN
  UNDISCH_TAC `moi_lsm_cube cc r` THEN REWRITE_TAC[moi_lsm_cube] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MATCH_MP_TAC MOI_LSM_P3_CUBE THEN ASM_REWRITE_TAC[]);;

let MOI_LSM_CP_BASIC = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r t z.
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r /\ t IN interval[vec 0,vec 1] /\
     z IN UNIONS c
     ==> moi_lsm_cp u h h' cc r t z IN UNIONS c /\
         (z IN u ==> moi_lsm_cp u h h' cc r t z IN u /\
                     h (moi_lsm_cp u h h' cc r t z) = moi_lsm_p3 (drop t) cc r (h z)) /\
         (moi_lsm_cp u h h' cc r t z IN complex_boundary c <=> z IN complex_boundary c) /\
         (~(z IN u /\ moi_lsm_sn (h z - cc) < r) ==> moi_lsm_cp u h h' cc r t z = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC]; ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_cp] THEN ASM_CASES_TAC `(z:real^N) IN u` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_lsm_p3 (drop t) cc r ((h:real^N->real^3) z) IN IMAGE h u` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LSM_CP_DOM THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `h':real^3->real^N`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^3->real^N) (moi_lsm_p3 (drop t) cc r ((h:real^N->real^3) z)) IN u /\
                h (h' (moi_lsm_p3 (drop t) cc r (h z))) = moi_lsm_p3 (drop t) cc r (h z)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `complex_boundary c:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[MOI_LSM_P3_COMPONENTS];
    DISCH_TAC THEN
    SUBGOAL_THEN `moi_lsm_p3 (drop t) cc r ((h:real^N->real^3) z) = h z` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LSM_P3_FIX THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]]);;

let MOI_LSM_CP_ZERO = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r z.
     moi_lsm_chart c u h h' ==> moi_lsm_cp u h h' cc r (vec 0) z = z`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  REWRITE_TAC[moi_lsm_cp; DROP_VEC; MOI_LSM_P3_ZERO] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let MOI_LSM_CP_INJ = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r t z z'.
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r /\ t IN interval[vec 0,vec 1] /\
     z IN UNIONS c /\ z' IN UNIONS c /\
     moi_lsm_cp u h h' cc r t z = moi_lsm_cp u h h' cc r t z'
     ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `cc:real^3`; `r:real`; `t:real^1`; `z:real^N`]
    MOI_LSM_CP_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "Z1")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "Z2")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `cc:real^3`; `r:real`; `t:real^1`; `z':real^N`]
    MOI_LSM_CP_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "W1")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "W2")))) THEN
  ASM_CASES_TAC `(z:real^N) IN u` THEN ASM_CASES_TAC `(z':real^N) IN u` THENL
   [USE_THEN "Z1" (MP_TAC o C MP (ASSUME `(z:real^N) IN u`)) THEN
    USE_THEN "W1" (MP_TAC o C MP (ASSUME `(z':real^N) IN u`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) z = h z'` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC MOI_LSM_P3_INJ THEN
    MAP_EVERY EXISTS_TAC [`drop t`; `cc:real^3`; `r:real`] THEN ASM_MESON_TAC[];
    USE_THEN "Z1" (MP_TAC o C MP (ASSUME `(z:real^N) IN u`)) THEN
    USE_THEN "W2" MP_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    USE_THEN "W1" (MP_TAC o C MP (ASSUME `(z':real^N) IN u`)) THEN
    USE_THEN "Z2" MP_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    USE_THEN "Z2" MP_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "W2" MP_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* The closed support is compact. *)

let MOI_LSM_CCUBE = prove
 (`!(cc:real^3) r. {z | moi_lsm_sn (z - cc) <= r} = interval[cc - r % vec 1,cc + r % vec 1]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
  X_GEN_TAC `z:real^3` THEN
  REWRITE_TAC[moi_lsm_sn; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_LSM_CHART_CUBE = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r.
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r
     ==> compact (IMAGE h u INTER {w | moi_lsm_sn (w - cc) <= r}) /\
         {z | z IN u /\ moi_lsm_sn (h z - cc) <= r} =
         IMAGE h' (IMAGE h u INTER {w | moi_lsm_sn (w - cc) <= r}) /\
         compact {z | z IN u /\ moi_lsm_sn (h z - cc) <= r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^N->real^3) u INTER {w | moi_lsm_sn (w - cc) <= r})`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_chart c u (h:real^N->real^3) h'` THEN
    REWRITE_TAC[moi_lsm_chart] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `ball(vec 0:real^3,&1) INTER {w | moi_lsm_sn (w - cc) <= r} =
                    {w | moi_lsm_sn (w - cc) <= r}` SUBST1_TAC THENL
       [UNDISCH_TAC `moi_lsm_cube cc r` THEN REWRITE_TAC[moi_lsm_cube] THEN SET_TAC[];
        REWRITE_TAC[MOI_LSM_CCUBE; COMPACT_INTERVAL]];
      SUBGOAL_THEN `(ball(vec 0:real^3,&1) INTER {z:real^3 | &0 <= z$3}) INTER
                    {w | moi_lsm_sn (w - cc) <= r} =
                    {w | moi_lsm_sn (w - cc) <= r} INTER {z:real^3 | z$3 >= &0}`
      SUBST1_TAC THENL
       [UNDISCH_TAC `moi_lsm_cube cc r` THEN REWRITE_TAC[moi_lsm_cube; real_ge] THEN SET_TAC[];
        MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC[MOI_LSM_CCUBE; COMPACT_INTERVAL; CLOSED_HALFSPACE_COMPONENT_GE]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{z | z IN u /\ moi_lsm_sn ((h:real^N->real^3) z - cc) <= r} =
                IMAGE h' (IMAGE h u INTER {w | moi_lsm_sn (w - cc) <= r})` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THENL
     [X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `z:real^N = h' ((h:real^N->real^3) z)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM; FUN_IN_IMAGE];
      X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN
  ASM_REWRITE_TAC[INTER_SUBSET]);;

(* Joint continuity in the time and the point. *)

let MOI_LSM_CP_CONT = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r.
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r
     ==> (\p. moi_lsm_cp u h h' cc r (fstcart p) (sndcart p)) continuous_on
         (interval[vec 0,vec 1] PCROSS UNIONS c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `cc:real^3`; `r:real`] MOI_LSM_CHART_CUBE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS (c:(real^N->bool)->bool))) u`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_lsm_chart]; ALL_TAC] THEN
  ABBREV_TAC `K = {z | z IN u /\ moi_lsm_sn ((h:real^N->real^3) z - cc) <= r}` THEN
  SUBGOAL_THEN `(K:real^N->bool) SUBSET u` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `u UNION (UNIONS c DIFF K) = UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[vec 0:real^1,vec 1] PCROSS UNIONS (c:(real^N->bool)->bool) =
                (interval[vec 0,vec 1] PCROSS u) UNION
                (interval[vec 0,vec 1] PCROSS (UNIONS c DIFF K))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM PCROSS_UNION]; ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_cp] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL_OPEN THEN
  REWRITE_TAC[GSYM PCROSS_UNION] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_PCROSS THEN ASM_REWRITE_TAC[OPEN_IN_REFL];
    MATCH_MP_TAC OPEN_IN_PCROSS THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `(K:real^N->bool) SUBSET u` THEN
    UNDISCH_TAC `(u:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[];
    SUBGOAL_THEN
     `(\p:real^(1,N)finite_sum. (h':real^3->real^N)
         (moi_lsm_p3 (drop(fstcart p)) cc r ((h:real^N->real^3) (sndcart p)))) =
      h' o (\q:real^(1,3)finite_sum. moi_lsm_p3 (drop(fstcart q)) cc r (sndcart q)) o
      (\p. pastecart (fstcart p) (h (sndcart p)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[MOI_LSM_P3_CONT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; FORALL_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_LSM_CP_DOM THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `h':real^3->real^N`] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      UNDISCH_TAC `(a:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC];
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^N`] THEN
    MATCH_MP_TAC(TAUT `(q ==> r) ==> ((p0 /\ p) /\ ~p \/ q ==> r)`) THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_lsm_p3 (drop a) cc r ((h:real^N->real^3) b) = h b` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LSM_P3_FIX THEN
      UNDISCH_TAC `~((b:real^N) IN K)` THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

(* PL for each time. *)

let MOI_LSM_CP_PL = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r t.
     combinatorial_manifold_with_boundary 3 c /\
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r /\ t IN interval[vec 0,vec 1]
     ==> pl_map_on (UNIONS c) (moi_lsm_cp u h h' cc r t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `cc:real^3`; `r:real`] MOI_LSM_CHART_CUBE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC]; ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (UNIONS (c:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS (c:(real^N->bool)->bool))) u`
  MP_TAC THENL [ASM_MESON_TAC[moi_lsm_chart]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  ABBREV_TAC `K = {z | z IN u /\ moi_lsm_sn ((h:real^N->real^3) z - cc) <= r}` THEN
  GEN_REWRITE_TAC I [PL_MAP_ON_LOCAL] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN u` THENL
   [EXISTS_TAC `g0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `(h':real^3->real^N) o moi_lsm_p3 (drop t) cc r o (h:real^N->real^3)` THEN
    CONJ_TAC THENL [SIMP_TAC[moi_lsm_cp; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[MOI_LSM_P3_PL; SUBSET_UNIV];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MOI_LSM_CP_DOM THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `h':real^3->real^N`] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    EXISTS_TAC `(:real^N) DIFF K` THEN REWRITE_TAC[GSYM closed] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\z:real^N. z` THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                     `h':real^3->real^N`; `cc:real^3`; `r:real`; `t:real^1`; `z:real^N`]
        MOI_LSM_CP_BASIC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `~((z:real^N) IN K)` THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[GSYM closed] THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]]);;

(* The push of a seam point and of a quadrant point. *)

let MOI_LSM_CP_SIDES = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r t z.
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r /\ t IN interval[vec 0,vec 1] /\
     &0 < drop t /\ z IN u
     ==> moi_lsm_cp u h h' cc r t z IN u /\
         ((h z)$1 < &0 /\ &0 < (h z)$2
          ==> (h (moi_lsm_cp u h h' cc r t z))$1 < &0 /\
              &0 < (h (moi_lsm_cp u h h' cc r t z))$2) /\
         (moi_lsm_sn (h z - cc) < r /\
          (((h z)$1 = &0 /\ &0 <= (h z)$2) \/ ((h z)$2 = &0 /\ (h z)$1 <= &0))
          ==> (h (moi_lsm_cp u h h' cc r t z))$1 < &0 /\
              &0 < (h (moi_lsm_cp u h h' cc r t z))$2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `cc:real^3`; `r:real`; `t:real^1`; `z:real^N`]
    MOI_LSM_CP_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(z:real^N) IN u`) o CONJUNCT1 o CONJUNCT2) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`drop t`; `cc:real^3`; `r:real`; `(h:real^N->real^3) z`] MOI_LSM_P3_SIDES) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 18: the composite of finitely many chart pushes.  moi_lsm_fam:      *)
(* the charts and cubes of indices below m; moi_lsm_comp applies the pushes *)
(* of indices 0, 1, ..., n-1 in this order.  moi_lsm_supp, moi_lsm_ocov and  *)
(* moi_lsm_omega are the unions of the closed cubes, of the open cubes and  *)
(* of the open quadrants z1 < 0 < z2 inside the open cubes.  The composite  *)
(* keeps UNIONS c and the boundary, is the identity off the support and     *)
(* keeps the support, is the identity at time 0, is injective, PL, and      *)
(* jointly continuous in the time.                                          *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_comp = define
 `moi_lsm_comp (U:num->real^N->bool) (Hh:num->real^N->real^3) (Hi:num->real^3->real^N)
               (Cc:num->real^3) (R:num->real) (t:real^1) 0 (z:real^N) = z /\
  moi_lsm_comp U Hh Hi Cc R t (SUC n) z =
     moi_lsm_cp (U n) (Hh n) (Hi n) (Cc n) (R n) t (moi_lsm_comp U Hh Hi Cc R t n z)`;;

let moi_lsm_fam = new_definition
 `moi_lsm_fam (c:(real^N->bool)->bool) U (Hh:num->real^N->real^3) Hi Cc R m <=>
    !i. i < m ==> moi_lsm_chart c (U i) (Hh i) (Hi i) /\ moi_lsm_cube (Cc i) (R i)`;;

let moi_lsm_supp = new_definition
 `moi_lsm_supp (U:num->real^N->bool) (Hh:num->real^N->real^3) Cc R n =
    {z | ?i. i < n /\ z IN U i /\ moi_lsm_sn (Hh i z - Cc i) <= R i}`;;

let moi_lsm_ocov = new_definition
 `moi_lsm_ocov (U:num->real^N->bool) (Hh:num->real^N->real^3) Cc R n =
    {z | ?i. i < n /\ z IN U i /\ moi_lsm_sn (Hh i z - Cc i) < R i}`;;

let moi_lsm_omega = new_definition
 `moi_lsm_omega (U:num->real^N->bool) (Hh:num->real^N->real^3) Cc R n =
    {z | ?i. i < n /\ z IN U i /\ moi_lsm_sn (Hh i z - Cc i) < R i /\
             (Hh i z)$1 < &0 /\ &0 < (Hh i z)$2}`;;

let MOI_LSM_SUPP_ZERO = prove
 (`!(U:num->real^N->bool) (Hh:num->real^N->real^3) Cc R.
     moi_lsm_supp U Hh Cc R 0 = {} /\ moi_lsm_ocov U Hh Cc R 0 = {} /\
     moi_lsm_omega U Hh Cc R 0 = {}`,
  REWRITE_TAC[moi_lsm_supp; moi_lsm_ocov; moi_lsm_omega; LT; EXTENSION; NOT_IN_EMPTY;
              IN_ELIM_THM]);;

let MOI_LSM_SUPP_SUC = prove
 (`!(U:num->real^N->bool) (Hh:num->real^N->real^3) Cc R n.
     moi_lsm_supp U Hh Cc R (SUC n) =
     moi_lsm_supp U Hh Cc R n UNION {z | z IN U n /\ moi_lsm_sn (Hh n z - Cc n) <= R n} /\
     moi_lsm_ocov U Hh Cc R (SUC n) =
     moi_lsm_ocov U Hh Cc R n UNION {z | z IN U n /\ moi_lsm_sn (Hh n z - Cc n) < R n} /\
     moi_lsm_omega U Hh Cc R (SUC n) =
     moi_lsm_omega U Hh Cc R n UNION
     {z | z IN U n /\ moi_lsm_sn (Hh n z - Cc n) < R n /\ (Hh n z)$1 < &0 /\ &0 < (Hh n z)$2}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_lsm_supp; moi_lsm_ocov; moi_lsm_omega; EXTENSION; IN_UNION; IN_ELIM_THM;
              LT] THEN
  MESON_TAC[]);;

let MOI_LSM_FAM_AT = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m i.
     moi_lsm_fam c U Hh Hi Cc R m /\ i < m
     ==> moi_lsm_chart c (U i) (Hh i) (Hi i) /\ moi_lsm_cube (Cc i) (R i)`,
  REWRITE_TAC[moi_lsm_fam] THEN MESON_TAC[]);;

let MOI_LSM_CP_OCUBE = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' cc r t z.
     moi_lsm_chart c u h h' /\ moi_lsm_cube cc r /\ t IN interval[vec 0,vec 1] /\
     z IN u /\ moi_lsm_sn (h z - cc) < r
     ==> moi_lsm_cp u h h' cc r t z IN u /\
         moi_lsm_sn (h (moi_lsm_cp u h h' cc r t z) - cc) < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `cc:real^3`; `r:real`; `t:real^1`; `z:real^N`]
    MOI_LSM_CP_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(z:real^N) IN u`) o CONJUNCT1 o CONJUNCT2) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_LSM_P3_CUBE THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC);;

let MOI_LSM_COMP_BASIC = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m t.
     moi_lsm_fam c U Hh Hi Cc R m /\ t IN interval[vec 0,vec 1]
     ==> !n z. n <= m /\ z IN UNIONS c
               ==> moi_lsm_comp U Hh Hi Cc R t n z IN UNIONS c /\
                   (moi_lsm_comp U Hh Hi Cc R t n z IN complex_boundary c <=>
                    z IN complex_boundary c) /\
                   (~(z IN moi_lsm_supp U Hh Cc R n) ==> moi_lsm_comp U Hh Hi Cc R t n z = z) /\
                   (z IN moi_lsm_supp U Hh Cc R n
                    ==> moi_lsm_comp U Hh Hi Cc R t n z IN moi_lsm_supp U Hh Cc R n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[moi_lsm_comp; MOI_LSM_SUPP_ZERO; NOT_IN_EMPTY]; ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT2 moi_lsm_comp; MOI_LSM_SUPP_SUC; IN_UNION; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w = moi_lsm_comp U Hh Hi Cc R t n (z:real^N)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "F") (LABEL_TAC "S")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `n:num`]
    MOI_LSM_FAM_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                 `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                 `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `w:real^N`]
    MOI_LSM_CP_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "IN")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FX")))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[TAUT `~(a \/ b) <=> ~a /\ ~b`] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `w:real^N = z` SUBST_ALL_TAC THENL
     [USE_THEN "F" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "FX" MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `(w:real^N) IN (U:num->real^N->bool) n /\
                 moi_lsm_sn ((Hh:num->real^N->real^3) n w - (Cc:num->real^3) n) <
                 (R:num->real) n` THENL
   [DISJ2_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                   `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                   `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `w:real^N`]
      MOI_LSM_CP_OCUBE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  USE_THEN "FX" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `~((w:real^N) IN (U:num->real^N->bool) n /\
       moi_lsm_sn ((Hh:num->real^N->real^3) n w - (Cc:num->real^3) n) <
       (R:num->real) n)`)]) THEN
  ASM_CASES_TAC `(z:real^N) IN moi_lsm_supp U (Hh:num->real^N->real^3) Cc R n` THENL
   [DISJ1_TAC THEN USE_THEN "S" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `w:real^N = z` SUBST_ALL_TAC THENL
     [USE_THEN "F" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let MOI_LSM_COMP_ZERO = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m n z.
     moi_lsm_fam c U Hh Hi Cc R m /\ n <= m ==> moi_lsm_comp U Hh Hi Cc R (vec 0) n z = z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. n <= m ==> !z:real^N. moi_lsm_comp U Hh Hi Cc R (vec 0) n z = z`
    (fun th -> SIMP_TAC[th]) THEN
  INDUCT_TAC THEN REWRITE_TAC[moi_lsm_comp] THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_LSM_CP_ZERO THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `n:num`]
    MOI_LSM_FAM_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]);;

let MOI_LSM_COMP_INJ = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m t.
     moi_lsm_fam c U Hh Hi Cc R m /\ t IN interval[vec 0,vec 1]
     ==> !n z z'. n <= m /\ z IN UNIONS c /\ z' IN UNIONS c /\
                  moi_lsm_comp U Hh Hi Cc R t n z = moi_lsm_comp U Hh Hi Cc R t n z'
                  ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[moi_lsm_comp] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT2 moi_lsm_comp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `n:num`]
    MOI_LSM_FAM_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `t:real^1`]
    MOI_LSM_COMP_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "B") THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    length (fst(strip_forall (concl th))) = 2)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LSM_CP_INJ THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
    `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`; `(Cc:num->real^3) n`;
    `(R:num->real) n`; `t:real^1`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "B" (MP_TAC o SPECL [`n:num`; `z:real^N`]);
    USE_THEN "B" (MP_TAC o SPECL [`n:num`; `z':real^N`])] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]));;

let MOI_LSM_COMP_CONT = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m n.
     moi_lsm_fam c U Hh Hi Cc R m /\ n <= m
     ==> (\p. moi_lsm_comp U Hh Hi Cc R (fstcart p) n (sndcart p)) continuous_on
         (interval[vec 0,vec 1] PCROSS UNIONS c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[moi_lsm_comp] THEN DISCH_TAC THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[CONJUNCT2 moi_lsm_comp] THEN
  SUBGOAL_THEN
   `(\p:real^(1,N)finite_sum. moi_lsm_cp ((U:num->real^N->bool) n) ((Hh:num->real^N->real^3) n)
       ((Hi:num->real^3->real^N) n) ((Cc:num->real^3) n) ((R:num->real) n) (fstcart p)
       (moi_lsm_comp U Hh Hi Cc R (fstcart p) n (sndcart p))) =
    (\q. moi_lsm_cp (U n) (Hh n) (Hi n) (Cc n) (R n) (fstcart q) (sndcart q)) o
    (\p. pastecart (fstcart p) (moi_lsm_comp U Hh Hi Cc R (fstcart p) n (sndcart p)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `n:num`]
    MOI_LSM_FAM_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS UNIONS (c:(real^N->bool)->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LSM_CP_CONT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^N`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                     `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`;
                     `Cc:num->real^3`; `R:num->real`; `m:num`; `a:real^1`] MOI_LSM_COMP_BASIC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `b:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]]]);;

let MOI_LSM_COMP_PL = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m t n.
     combinatorial_manifold_with_boundary 3 c /\
     moi_lsm_fam c U Hh Hi Cc R m /\ t IN interval[vec 0,vec 1] /\ n <= m
     ==> pl_map_on (UNIONS c) (moi_lsm_comp U Hh Hi Cc R t n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `moi_lsm_comp U Hh Hi Cc R t 0 = (\z:real^N. z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; moi_lsm_comp]; ALL_TAC] THEN
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `moi_lsm_comp U Hh Hi Cc R t (SUC n) =
                moi_lsm_cp ((U:num->real^N->bool) n) ((Hh:num->real^N->real^3) n)
                  ((Hi:num->real^3->real^N) n) ((Cc:num->real^3) n) ((R:num->real) n) t o
                moi_lsm_comp U Hh Hi Cc R t n` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; moi_lsm_comp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `n:num`]
    MOI_LSM_FAM_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `UNIONS (c:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LSM_CP_PL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                   `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`;
                   `Cc:num->real^3`; `R:num->real`; `m:num`; `t:real^1`] MOI_LSM_COMP_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 19: the invariant of the composite at a positive time.  X is a set  *)
(* of seam points: in every chart they lie on the seam z1 = 0 <= z2 or      *)
(* z2 = 0 >= z1.  The consistency hypothesis says that a point of the       *)
(* quadrant z1 < 0 < z2 of an earlier open cube is in the same quadrant of  *)
(* a later open cube containing it.  Then after the first n pushes a point  *)
(* of X is fixed if it is in no open cube, and is in omega n otherwise.    *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_OMEGA_STEP = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m t n w.
     moi_lsm_fam c U Hh Hi Cc R m /\ t IN interval[vec 0,vec 1] /\ &0 < drop t /\ n < m /\
     (!i z. i < n /\ z IN U i /\ z IN U n /\
            moi_lsm_sn (Hh i z - Cc i) < R i /\ moi_lsm_sn (Hh n z - Cc n) < R n /\
            (Hh i z)$1 < &0 /\ &0 < (Hh i z)$2
            ==> (Hh n z)$1 < &0 /\ &0 < (Hh n z)$2) /\
     w IN UNIONS c /\ w IN moi_lsm_omega U Hh Cc R n
     ==> moi_lsm_cp (U n) (Hh n) (Hi n) (Cc n) (R n) t w IN moi_lsm_omega U Hh Cc R (SUC n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `n:num`]
    MOI_LSM_FAM_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[MOI_LSM_SUPP_SUC; IN_UNION; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(w:real^N) IN (U:num->real^N->bool) n /\
                 moi_lsm_sn ((Hh:num->real^N->real^3) n w - (Cc:num->real^3) n) <
                 (R:num->real) n` THENL
   [DISJ2_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `((Hh:num->real^N->real^3) n w)$1 < &0 /\ &0 < (Hh n w)$2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^N) IN moi_lsm_omega U (Hh:num->real^N->real^3) Cc R n` THEN
      REWRITE_TAC[moi_lsm_omega; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        length (fst(strip_forall (concl th))) = 2)) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                   `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                   `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `w:real^N`]
      MOI_LSM_CP_SIDES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                   `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                   `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `w:real^N`]
      MOI_LSM_CP_OCUBE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                   `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                   `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `w:real^N`]
      MOI_LSM_CP_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let MOI_LSM_COMP_INV = prove
 (`!(c:(real^N->bool)->bool) U Hh Hi Cc R m t X.
     moi_lsm_fam c U Hh Hi Cc R m /\ t IN interval[vec 0,vec 1] /\ &0 < drop t /\
     X SUBSET UNIONS c /\
     (!i y. i < m /\ y IN X /\ y IN U i
            ==> ((Hh i y)$1 = &0 /\ &0 <= (Hh i y)$2) \/
                ((Hh i y)$2 = &0 /\ (Hh i y)$1 <= &0)) /\
     (!i j z. i < j /\ j < m /\ z IN U i /\ z IN U j /\
              moi_lsm_sn (Hh i z - Cc i) < R i /\ moi_lsm_sn (Hh j z - Cc j) < R j /\
              (Hh i z)$1 < &0 /\ &0 < (Hh i z)$2
              ==> (Hh j z)$1 < &0 /\ &0 < (Hh j z)$2)
     ==> !n y. n <= m /\ y IN X
               ==> (~(y IN moi_lsm_ocov U Hh Cc R n) ==> moi_lsm_comp U Hh Hi Cc R t n y = y) /\
                   (y IN moi_lsm_ocov U Hh Cc R n
                    ==> moi_lsm_comp U Hh Hi Cc R t n y IN moi_lsm_omega U Hh Cc R n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[moi_lsm_comp; MOI_LSM_SUPP_ZERO; NOT_IN_EMPTY]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F") (LABEL_TAC "O")) THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`; `n:num`]
    MOI_LSM_FAM_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[CONJUNCT2 moi_lsm_comp] THEN
  ASM_CASES_TAC `(y:real^N) IN moi_lsm_ocov U (Hh:num->real^N->real^3) Cc R n` THENL
   [(* y was already in an earlier open cube *)
    USE_THEN "O" (MP_TAC o C MP (ASSUME
      `(y:real^N) IN moi_lsm_ocov U (Hh:num->real^N->real^3) Cc R n`)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `moi_lsm_comp U Hh Hi Cc R t n (y:real^N) IN UNIONS c` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                     `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`;
                     `Cc:num->real^3`; `R:num->real`; `m:num`; `t:real^1`] MOI_LSM_COMP_BASIC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                   `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`;
                   `t:real^1`; `n:num`; `moi_lsm_comp U Hh Hi Cc R t n (y:real^N)`]
      MOI_LSM_OMEGA_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `z:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `n:num`; `z:real^N`] o check (fun th ->
        is_forall (concl th) && length (fst(strip_forall (concl th))) = 3)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOI_LSM_SUPP_SUC; IN_UNION] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* y is fixed by the first n pushes *)
  USE_THEN "F" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `~((y:real^N) IN moi_lsm_ocov U (Hh:num->real^N->real^3) Cc R n)`)]) THEN
  REWRITE_TAC[MOI_LSM_SUPP_SUC; IN_UNION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(y:real^N) IN (U:num->real^N->bool) n /\
                 moi_lsm_sn ((Hh:num->real^N->real^3) n y - (Cc:num->real^3) n) <
                 (R:num->real) n` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN DISJ2_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                   `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                   `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `y:real^N`]
      MOI_LSM_CP_OCUBE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(((Hh:num->real^N->real^3) n y)$1 = &0 /\ &0 <= (Hh n y)$2) \/
                  ((Hh n y)$2 = &0 /\ (Hh n y)$1 <= &0)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        length (fst(strip_forall (concl th))) = 2 &&
        can (find_term (fun t -> t = `X:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                   `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                   `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `y:real^N`]
      MOI_LSM_CP_SIDES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) n`;
                   `(Hh:num->real^N->real^3) n`; `(Hi:num->real^3->real^N) n`;
                   `(Cc:num->real^3) n`; `(R:num->real) n`; `t:real^1`; `y:real^N`]
      MOI_LSM_CP_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 20: consistency of the quadrants of two charts.  moi_lsm_lab u h    *)
(* P1 P2 ff: in the chart, the points of P1 are those of the half plane     *)
(* z1 = 0 < z2, the points of P2 those of z2 = 0 > z1, and the points of ff *)
(* (the image of the disk) those of the two planes.  If the open cube of   *)
(* chart i (centred on the axis) lies in the domain of chart j and both    *)
(* charts are labelled by the same P1, P2, ff, then the quadrant           *)
(* z1 < 0 < z2 of the open cube of chart i lies in the same quadrant of    *)
(* chart j: the second (first) coordinate of chart j has a constant sign    *)
(* on the convex set z1 <= 0 < z2 (z1 < 0 <= z2) of the cube of chart i,   *)
(* fixed by its value on the half plane P1 (P2).                            *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_lab = new_definition
 `moi_lsm_lab (u:real^N->bool) (h:real^N->real^3) P1 P2 ff <=>
    !z. z IN u
        ==> (z IN P1 <=> (h z)$1 = &0 /\ &0 < (h z)$2) /\
            (z IN P2 <=> (h z)$2 = &0 /\ (h z)$1 < &0) /\
            (z IN ff <=> (h z)$1 = &0 \/ (h z)$2 = &0)`;;

let MOI_LSM_OCUBE = prove
 (`!(cc:real^3) r. {z | moi_lsm_sn (z - cc) < r} = interval(cc - r % vec 1,cc + r % vec 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
  X_GEN_TAC `z:real^3` THEN
  REWRITE_TAC[moi_lsm_sn; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_LSM_SIGN = prove
 (`!(s:real^3->bool) phi a b.
     convex s /\ (\w. lift(phi w)) continuous_on s /\ a IN s /\ b IN s /\
     (!w. w IN s ==> ~(phi w = &0))
     ==> (&0 < phi a <=> &0 < phi b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `connected (IMAGE (\w. lift(phi w)) (s:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[CONVEX_CONNECTED]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~(p <=> q) ==> F) ==> (p <=> q)`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x y:real^3. x IN s /\ y IN s /\ phi x <= &0 /\ &0 <= phi y`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < phi(a:real^3)` THENL
     [MAP_EVERY EXISTS_TAC [`b:real^3`; `a:real^3`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift(phi(x:real^3)) IN IMAGE (\w. lift(phi w)) s /\
                lift(phi(y:real^3)) IN IMAGE (\w. lift(phi w)) s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\w. lift(phi w)) (s:real^3->bool)`; `lift(phi(x:real^3))`;
                 `lift(phi(y:real^3))`; `&0`; `1`] CONNECTED_IVT_COMPONENT) THEN
  ASM_REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; GSYM drop; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let MOI_LSM_CHART_CONVEX = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h'.
     moi_lsm_chart c u h h' ==> convex (IMAGE h u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_chart] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[CONVEX_BALL] THEN MATCH_MP_TAC CONVEX_INTER THEN
  REWRITE_TAC[CONVEX_BALL; GSYM real_ge; CONVEX_HALFSPACE_COMPONENT_GE]);;

let MOI_LSM_LAB_PTS = prove
 (`!ui (hi:real^N->real^3) uj (hj:real^N->real^3) P1 P2 ff y.
     moi_lsm_lab ui hi P1 P2 ff /\ moi_lsm_lab uj hj P1 P2 ff /\ y IN ui /\ y IN uj
     ==> ((hi y)$1 < &0 /\ &0 < (hi y)$2 ==> ~((hj y)$1 = &0) /\ ~((hj y)$2 = &0)) /\
         ((hi y)$1 = &0 /\ &0 < (hi y)$2 ==> (hj y)$1 = &0 /\ &0 < (hj y)$2) /\
         ((hi y)$2 = &0 /\ (hi y)$1 < &0 ==> (hj y)$2 = &0 /\ (hj y)$1 < &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_lab] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `y:real^N`) (CONJUNCTS_THEN2
    (MP_TAC o SPEC `y:real^N`) STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[REAL_LT_IMP_NE; REAL_LT_IMP_NZ]);;

let MOI_LSM_CONSIST = prove
 (`!(c:(real^N->bool)->bool) ui (hi:real^N->real^3) hi' uj (hj:real^N->real^3) hj' cc r
    P1 P2 ff z.
     moi_lsm_chart c ui hi hi' /\ moi_lsm_chart c uj hj hj' /\ moi_lsm_cube cc r /\
     cc IN IMAGE hi ui /\ cc$1 = &0 /\ cc$2 = &0 /\
     (!z. z IN ui /\ moi_lsm_sn (hi z - cc) < r ==> z IN uj) /\
     moi_lsm_lab ui hi P1 P2 ff /\ moi_lsm_lab uj hj P1 P2 ff /\
     z IN ui /\ moi_lsm_sn (hi z - cc) < r /\ (hi z)$1 < &0 /\ &0 < (hi z)$2
     ==> (hj z)$1 < &0 /\ &0 < (hj z)$2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ui:real^N->bool`; `hi:real^N->real^3`;
                 `hi':real^3->real^N`] MOI_LSM_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(hj:real^N->real^3) continuous_on uj` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LSM_CHART_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (IMAGE (hi:real^N->real^3) ui)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LSM_CHART_CONVEX]; ALL_TAC] THEN
  ABBREV_TAC `D = IMAGE (hi:real^N->real^3) ui INTER {w | moi_lsm_sn (w - cc) < r}` THEN
  SUBGOAL_THEN `convex (D:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC CONVEX_INTER THEN
    ASM_REWRITE_TAC[MOI_LSM_OCUBE; CONVEX_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN D ==> (hi':real^3->real^N) w IN ui /\ hi (hi' w) = w /\ hi' w IN uj`
  (LABEL_TAC "D") THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(hi':real^3->real^N) w IN ui /\ hi (hi' w) = w` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. (\w. lift(((hj:real^N->real^3) ((hi':real^3->real^N) w))$k))
                    continuous_on D`
  (LABEL_TAC "C") THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (hi:real^N->real^3) ui` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[INTER_SUBSET];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `uj:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* pointwise facts *)
  SUBGOAL_THEN
   `!w. w IN D
        ==> (w$1 < &0 /\ &0 < w$2
             ==> ~(((hj:real^N->real^3) ((hi':real^3->real^N) w))$1 = &0) /\
                 ~((hj (hi' w))$2 = &0)) /\
            (w$1 = &0 /\ &0 < w$2 ==> &0 < (hj (hi' w))$2) /\
            (w$2 = &0 /\ w$1 < &0 ==> (hj (hi' w))$1 < &0)`
  (LABEL_TAC "Q") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "D" (MP_TAC o C MP (ASSUME `(w:real^3) IN D`) o SPEC `w:real^3`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`ui:real^N->bool`; `hi:real^N->real^3`; `uj:real^N->bool`;
                   `hj:real^N->real^3`; `P1:real^N->bool`; `P2:real^N->bool`;
                   `ff:real^N->bool`; `(hi':real^3->real^N) w`] MOI_LSM_LAB_PTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the point and the two anchors *)
  SUBGOAL_THEN `(hi:real^N->real^3) z IN D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hi':real^3->real^N) (hi z) = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. moi_lsm_sn v < r /\ v$3 = &0 ==> cc + v IN D` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_ARITH `(cc + v) - cc:real^3 = v`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `ball(vec 0:real^3,&1)`)) (concl th))) THEN
    EXISTS_TAC `cc:real^3` THEN ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_ADD_RID] THEN
    UNDISCH_TAC `moi_lsm_cube cc r` THEN REWRITE_TAC[moi_lsm_cube] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[VECTOR_ARITH `(cc + v) - cc:real^3 = v`; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lsm_cube]; ALL_TAC] THEN
  SUBGOAL_THEN `cc + vector[&0; r / &2; &0] IN (D:real^3->bool) /\
                cc + vector[--(r / &2); &0; &0] IN D` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[moi_lsm_sn; VECTOR_3] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the first coordinate, on z1 < 0 <= z2 *)
    SUBGOAL_THEN `(cc + vector[--(r / &2); &0; &0]:real^3) IN
                  D INTER {w:real^3 | w$1 < &0} INTER {w:real^3 | w$2 >= &0} /\
                  (hi:real^N->real^3) z IN
                  D INTER {w:real^3 | w$1 < &0} INTER {w:real^3 | w$2 >= &0}`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_3; real_ge] THEN
      UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < ((hi:real^N->real^3) z)$2` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`D INTER {w:real^3 | w$1 < &0} INTER {w:real^3 | w$2 >= &0}`;
                   `\w. ((hj:real^N->real^3) ((hi':real^3->real^N) w))$1`;
                   `cc + vector[--(r / &2); &0; &0]:real^3`; `(hi:real^N->real^3) z`]
      MOI_LSM_SIGN) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT; CONVEX_HALFSPACE_COMPONENT_GE];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^3->bool` THEN
        USE_THEN "C" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_ge] THEN STRIP_TAC THEN
      USE_THEN "Q" (MP_TAC o C MP (ASSUME `(w:real^3) IN D`) o SPEC `w:real^3`) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(w:real^3)$2 = &0` THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < (w:real^3)$2` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    USE_THEN "Q" (MP_TAC o SPEC `cc + vector[--(r / &2); &0; &0]:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_3] THEN
    USE_THEN "Q" (MP_TAC o C MP (ASSUME `(hi:real^N->real^3) z IN D`) o
                  SPEC `(hi:real^N->real^3) z`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    (* the second coordinate, on z1 <= 0 < z2 *)
    SUBGOAL_THEN `(cc + vector[&0; r / &2; &0]:real^3) IN
                  D INTER {w:real^3 | w$1 <= &0} INTER {w:real^3 | w$2 > &0} /\
                  (hi:real^N->real^3) z IN
                  D INTER {w:real^3 | w$1 <= &0} INTER {w:real^3 | w$2 > &0}`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_3; real_gt] THEN
      UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `((hi:real^N->real^3) z)$1 < &0` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`D INTER {w:real^3 | w$1 <= &0} INTER {w:real^3 | w$2 > &0}`;
                   `\w. ((hj:real^N->real^3) ((hi':real^3->real^N) w))$2`;
                   `cc + vector[&0; r / &2; &0]:real^3`; `(hi:real^N->real^3) z`]
      MOI_LSM_SIGN) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GT];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^3->bool` THEN
        USE_THEN "C" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN STRIP_TAC THEN
      USE_THEN "Q" (MP_TAC o C MP (ASSUME `(w:real^3) IN D`) o SPEC `w:real^3`) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(w:real^3)$1 = &0` THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `(w:real^3)$1 < &0` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    USE_THEN "Q" (MP_TAC o SPEC `cc + vector[&0; r / &2; &0]:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_3] THEN
    USE_THEN "Q" (MP_TAC o C MP (ASSUME `(hi:real^N->real^3) z IN D`) o
                  SPEC `(hi:real^N->real^3) z`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 20b: the cover of k by finitely many pushes, the statement           *)
(* MOI_LSM_COVER_STMT and its proof MOI_LSM_COVER.  For each point of k a    *)
(* chart from the hypothesis; finitely many small cubes centred on k in      *)
(* charts whose domains contain a Lebesgue ball; meeting cubes lie in each   *)
(* other's chart domains.                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_COVER_STMT =
 `!(c:(real^N->bool)->bool) (k:real^N->bool) V0 X P1 P2 ff.
     compact k /\ open V0 /\ k SUBSET V0 /\
     (!y. y IN k
          ==> ?u (H:real^N->real^3) H'.
                moi_lsm_chart c u H H' /\ y IN u /\ u SUBSET V0 /\
                moi_lsm_lab u H P1 P2 ff /\
                (!z. z IN u /\ z IN X
                     ==> ((H z)$1 = &0 /\ &0 <= (H z)$2) \/
                         ((H z)$2 = &0 /\ (H z)$1 <= &0)) /\
                (!z. z IN u /\ z IN k ==> (H z)$1 = &0 /\ (H z)$2 = &0))
     ==> ?m U (Hh:num->real^N->real^3) Hi Cc R.
           moi_lsm_fam c U Hh Hi Cc R m /\
           (!i. i < m
                ==> U i SUBSET V0 /\ moi_lsm_lab (U i) (Hh i) P1 P2 ff /\
                    (!z. z IN U i /\ z IN X
                         ==> ((Hh i z)$1 = &0 /\ &0 <= (Hh i z)$2) \/
                             ((Hh i z)$2 = &0 /\ (Hh i z)$1 <= &0)) /\
                    Cc i IN IMAGE (Hh i) (U i) /\ (Cc i)$1 = &0 /\ (Cc i)$2 = &0) /\
           (!i j z. i < m /\ j < m /\ z IN U i /\ z IN U j /\
                    moi_lsm_sn (Hh i z - Cc i) < R i /\ moi_lsm_sn (Hh j z - Cc j) < R j
                    ==> !z'. z' IN U i /\ moi_lsm_sn (Hh i z' - Cc i) < R i
                             ==> z' IN U j) /\
           k SUBSET moi_lsm_ocov U Hh Cc R m`;;

(* ------------------------------------------------------------------------- *)
(* The proof MOI_LSM_COVER of MOI_LSM_COVER_STMT, using Parts 16 to 20.      *)
(* Route: Skolem functions for the charts and for open sets G with u =       *)
(* UNIONS c INTER G; a Lebesgue number e of the G along k                    *)
(* (HEINE_BOREL_LEMMA); at each x in k the chart of a point whose G contains *)
(* ball(x,e), centred at the chart image of x (on the axis), with a radius   *)
(* making the closed cube lie in the unit ball and the open pulled-back cube *)
(* lie in ball(x,e/3); a finite subcover of k by the open pulled-back cubes  *)
(* (COMPACT_IMP_HEINE_BOREL) enumerated by HAS_SIZE_INDEX; two open cubes    *)
(* that meet are within 2e/3 of each other's centres, so the open cube of i  *)
(* lies in ball(x_j,e), hence in U j.                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_LSMCV_NORM3 = prove
 (`!v:real^3. norm v <= &3 * moi_lsm_sn v`,
  GEN_TAC THEN MP_TAC(ISPEC `v:real^3` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3; moi_lsm_sn] THEN REAL_ARITH_TAC);;

let MOI_LSMCV_SN0 = prove
 (`moi_lsm_sn (vec 0) = &0`,
  REWRITE_TAC[moi_lsm_sn; VEC_COMPONENT; REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

(* A radius at a point of a chart domain: the closed cube lies in the unit *)
(* ball and the open pulled-back cube lies in ball(x,e).                   *)

let MOI_LSMCV_RADIUS = prove
 (`!(c:(real^N->bool)->bool) u (H:real^N->real^3) H' x e.
     moi_lsm_chart c u H H' /\ x IN u /\ &0 < e
     ==> ?r. moi_lsm_cube (H x) r /\
             !z. z IN u /\ moi_lsm_sn (H z - H x) < r ==> dist(z,x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  SUBGOAL_THEN `norm((H:real^N->real^3) x) < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(H:real^N->real^3) x IN ball(vec 0,&1)` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  UNDISCH_TAC `(H':real^3->real^N) continuous_on IMAGE (H:real^N->real^3) u` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `(H:real^N->real^3) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
  EXISTS_TAC `min ((&1 - norm((H:real^N->real^3) x)) / &4) (d / &4)` THEN
  REWRITE_TAC[moi_lsm_cube] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
    MP_TAC(ISPEC `w - (H:real^N->real^3) x` MOI_LSMCV_NORM3) THEN
    MP_TAC(ISPECL [`w:real^3`; `(H:real^N->real^3) x`] NORM_TRIANGLE_SUB) THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    USE_THEN "d" (MP_TAC o SPEC `(H:real^N->real^3) z`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[dist] THEN
      MP_TAC(ISPEC `(H:real^N->real^3) z - H x` MOI_LSMCV_NORM3) THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

(* The open pulled-back cube is open in UNIONS c. *)

let MOI_LSMCV_OPEN = prove
 (`!(c:(real^N->bool)->bool) u (H:real^N->real^3) H' cc r.
     moi_lsm_chart c u H H'
     ==> ?G. open G /\
             {z | z IN u /\ moi_lsm_sn (H z - cc) < r} = UNIONS c INTER G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM OPEN_IN_OPEN] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`H:real^N->real^3`; `u:real^N->bool`;
                   `{w:real^3 | moi_lsm_sn (w - cc) < r}`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    REWRITE_TAC[IN_ELIM_THM; MOI_LSM_OCUBE; OPEN_INTERVAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lsm_chart]) THEN MESON_TAC[]]);;

(* Two open cubes that meet: the second domain contains the first cube. *)

let MOI_LSMCV_OVERLAP = prove
 (`!(Ui:real^N->bool) Uj Gj cc xi xj z z' e.
     Ui SUBSET cc /\ Uj = cc INTER Gj /\ ball(xj,e) SUBSET Gj /\
     z' IN Ui /\ dist(z',xi) < e / &3 /\ dist(z,xi) < e / &3 /\ dist(z,xj) < e / &3
     ==> z' IN Uj`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z':real^N) IN ball(xj,e)` MP_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `dist(z':real^N,xi) < e / &3` THEN
    UNDISCH_TAC `dist(z:real^N,xi) < e / &3` THEN
    UNDISCH_TAC `dist(z:real^N,xj) < e / &3` THEN
    CONV_TAC NORM_ARITH;
    ASM SET_TAC[]]);;

(* The cover lemma. *)

let MOI_LSM_COVER = prove
 (MOI_LSM_COVER_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^N->real^N->bool`
   (X_CHOOSE_THEN `HH:real^N->real^N->real^3`
    (X_CHOOSE_THEN `HI:real^N->real^3->real^N` (LABEL_TAC "ch")))) THEN
  SUBGOAL_THEN `k SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "ch" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN k`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1 o MATCH_MP MOI_LSM_CHART_FACTS)
                               STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^N) IN uu y` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN k
                 ==> ?G. open G /\ uu y = UNIONS (c:(real^N->bool)->bool) INTER G`
  MP_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM OPEN_IN_OPEN] THEN
    USE_THEN "ch" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN k`))) THEN
    REWRITE_TAC[moi_lsm_chart] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT1);
    DISCH_THEN(X_CHOOSE_THEN `GG:real^N->real^N->bool` (LABEL_TAC "gg") o
               REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  MP_TAC(MATCH_MP HEINE_BOREL_LEMMA (ASSUME `compact(k:real^N->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (GG:real^N->real^N->bool) k`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `y:real^N` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "ch" (fun th ->
        MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP th (ASSUME `(y:real^N) IN k`))))) THEN
      USE_THEN "gg" (fun th ->
        MP_TAC(CONJUNCT2(MATCH_MP th (ASSUME `(y:real^N) IN k`)))) THEN
      SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "gg" (fun th -> MESON_TAC[th])];
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `yy:real^N->real^N` (LABEL_TAC "leb") o
               REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
               REWRITE_RULE[EXISTS_IN_IMAGE])] THEN
  SUBGOAL_THEN `!x:real^N. x IN k ==> x IN uu((yy:real^N->real^N) x)` (LABEL_TAC "xin") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "leb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`))) THEN
    USE_THEN "gg" (fun th ->
      MP_TAC(CONJUNCT2(MATCH_MP th (ASSUME `(yy:real^N->real^N) x IN k`)))) THEN
    SUBGOAL_THEN `(x:real^N) IN ball(x,e)` MP_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    UNDISCH_TAC `k SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(x:real^N) IN k` THEN
    UNDISCH_TAC `ball(x:real^N,e) SUBSET (GG:real^N->real^N->bool)((yy:real^N->real^N) x)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN k
       ==> ?r. moi_lsm_cube ((HH:real^N->real^N->real^3) ((yy:real^N->real^N) x) x) r /\
               !z. z IN uu(yy x) /\ moi_lsm_sn (HH (yy x) z - HH (yy x) x) < r
                   ==> dist(z,x) < e / &3`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "leb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(uu:real^N->real^N->bool) ((yy:real^N->real^N) x)`;
                   `(HH:real^N->real^N->real^3) ((yy:real^N->real^N) x)`;
                   `(HI:real^N->real^3->real^N) ((yy:real^N->real^N) x)`;
                   `x:real^N`; `e / &3`] MOI_LSMCV_RADIUS) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "ch" (fun th ->
        ACCEPT_TAC(CONJUNCT1(MATCH_MP th (ASSUME `(yy:real^N->real^N) x IN k`))));
      USE_THEN "xin" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`)));
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `rr:real^N->real` (LABEL_TAC "rad") o
               REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN k
      ==> (yy:real^N->real^N) x IN k /\ x IN uu(yy x) /\
          moi_lsm_chart c (uu(yy x)) ((HH:real^N->real^N->real^3) (yy x))
                        ((HI:real^N->real^3->real^N) (yy x)) /\
          uu(yy x) SUBSET V0 /\ moi_lsm_lab (uu(yy x)) (HH(yy x)) P1 P2 ff /\
          (!z. z IN uu(yy x) /\ z IN X
               ==> ((HH (yy x) z)$1 = &0 /\ &0 <= (HH (yy x) z)$2) \/
                   ((HH (yy x) z)$2 = &0 /\ (HH (yy x) z)$1 <= &0)) /\
          HH (yy x) x IN IMAGE (HH (yy x)) (uu(yy x)) /\
          (HH (yy x) x)$1 = &0 /\ (HH (yy x) x)$2 = &0 /\
          moi_lsm_cube (HH (yy x) x) ((rr:real^N->real) x) /\
          ball(x,e) SUBSET (GG:real^N->real^N->bool)(yy x) /\
          uu(yy x) = UNIONS c INTER GG(yy x) /\
          uu(yy x) SUBSET UNIONS c /\
          (!z. z IN uu(yy x) /\ moi_lsm_sn (HH (yy x) z - HH (yy x) x) < rr x
               ==> dist(z,x) < e / &3)`
  (LABEL_TAC "px") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "leb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`))) THEN
    USE_THEN "xin" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`))) THEN
    USE_THEN "rad" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`))) THEN
    USE_THEN "gg" (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(yy:real^N->real^N) x IN k`))) THEN
    USE_THEN "ch" (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(yy:real^N->real^N) x IN k`))) THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP MOI_LSM_CHART_FACTS) THEN
    SUBGOAL_THEN
     `(HH:real^N->real^N->real^3) ((yy:real^N->real^N) x) x IN IMAGE (HH (yy x)) (uu(yy x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `((HH:real^N->real^N->real^3) ((yy:real^N->real^N) x) x)$1 = &0 /\ (HH (yy x) x)$2 = &0`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN k
       ==> ?G. open G /\
               {z | z IN (uu:real^N->real^N->bool)((yy:real^N->real^N) x) /\
                    moi_lsm_sn ((HH:real^N->real^N->real^3) (yy x) z - HH (yy x) x) <
                    (rr:real^N->real) x} =
               UNIONS (c:(real^N->bool)->bool) INTER G`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                         `(uu:real^N->real^N->bool)((yy:real^N->real^N) x)`;
                         `(HH:real^N->real^N->real^3) ((yy:real^N->real^N) x)`;
                         `(HI:real^N->real^3->real^N) ((yy:real^N->real^N) x)`;
                         `(HH:real^N->real^N->real^3) ((yy:real^N->real^N) x) x`;
                         `(rr:real^N->real) x`] MOI_LSMCV_OPEN) THEN
    USE_THEN "px" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`))) THEN
    MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `OG:real^N->real^N->bool` (LABEL_TAC "og") o
               REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  MP_TAC(MATCH_MP COMPACT_IMP_HEINE_BOREL (ASSUME `compact(k:real^N->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (OG:real^N->real^N->bool) k`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [USE_THEN "og" (fun th -> MESON_TAC[th]);
      REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `(x:real^N) IN {z | z IN (uu:real^N->real^N->bool)((yy:real^N->real^N) x) /\
                          moi_lsm_sn ((HH:real^N->real^N->real^3) (yy x) z - HH (yy x) x) <
                          (rr:real^N->real) x}`
      MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; VECTOR_SUB_REFL; MOI_LSMCV_SN0] THEN
        USE_THEN "px" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN k`))) THEN
        REWRITE_TAC[moi_lsm_cube] THEN MESON_TAC[];
        USE_THEN "og" (fun th ->
          REWRITE_TAC[CONJUNCT2(MATCH_MP th (ASSUME `(x:real^N) IN k`))]) THEN
        SET_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(MATCH_MP (fst(EQ_IMP_RULE(ISPECL [`OG:real^N->real^N->bool`; `k:real^N->bool`;
                                           `f':(real^N->bool)->bool`] FINITE_SUBSET_IMAGE)))
           (CONJ (ASSUME `FINITE(f':(real^N->bool)->bool)`)
                 (ASSUME `(f':(real^N->bool)->bool) SUBSET IMAGE (OG:real^N->real^N->bool) k`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `(xs:real^N->bool) HAS_SIZE CARD xs` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `px:num->real^N`
    (CONJUNCTS_THEN2 (LABEL_TAC "pxs") (LABEL_TAC "pxu")) o MATCH_MP HAS_SIZE_INDEX) THEN
  SUBGOAL_THEN `!i. i < CARD(xs:real^N->bool) ==> (px:num->real^N) i IN k` (LABEL_TAC "pk") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `(xs:real^N->bool) SUBSET k` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "pxs" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `i < CARD(xs:real^N->bool)`)));
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`CARD(xs:real^N->bool)`;
    `\i. (uu:real^N->real^N->bool) ((yy:real^N->real^N) ((px:num->real^N) i))`;
    `\i. (HH:real^N->real^N->real^3) ((yy:real^N->real^N) ((px:num->real^N) i))`;
    `\i. (HI:real^N->real^3->real^N) ((yy:real^N->real^N) ((px:num->real^N) i))`;
    `\i. (HH:real^N->real^N->real^3) ((yy:real^N->real^N) ((px:num->real^N) i)) (px i)`;
    `\i. (rr:real^N->real) ((px:num->real^N) i)`] THEN
  REWRITE_TAC[moi_lsm_fam] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "pk" (fun pk -> USE_THEN "px" (fun th ->
      MP_TAC(MATCH_MP th (MATCH_MP pk (ASSUME `i < CARD(xs:real^N->bool)`))))) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "pk" (fun pk -> USE_THEN "px" (fun th ->
      MP_TAC(MATCH_MP th (MATCH_MP pk (ASSUME `i < CARD(xs:real^N->bool)`))))) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `z:real^N`] THEN STRIP_TAC THEN
    X_GEN_TAC `z':real^N` THEN STRIP_TAC THEN
    USE_THEN "pk" (fun pk -> USE_THEN "px" (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP th (MATCH_MP pk (ASSUME `i < CARD(xs:real^N->bool)`))))) THEN
    USE_THEN "pk" (fun pk -> USE_THEN "px" (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP th (MATCH_MP pk (ASSUME `j < CARD(xs:real^N->bool)`))))) THEN
    MATCH_MP_TAC(ISPECL
      [`(uu:real^N->real^N->bool)((yy:real^N->real^N)((px:num->real^N) i))`;
       `(uu:real^N->real^N->bool)((yy:real^N->real^N)((px:num->real^N) j))`;
       `(GG:real^N->real^N->bool)((yy:real^N->real^N)((px:num->real^N) j))`;
       `UNIONS(c:(real^N->bool)->bool)`;
       `(px:num->real^N) i`; `(px:num->real^N) j`; `z:real^N`; `z':real^N`; `e:real`]
      MOI_LSMCV_OVERLAP) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[SUBSET; moi_lsm_ocov; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^N. x IN xs /\ z IN (OG:real^N->real^N->bool) x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `k SUBSET UNIONS(IMAGE (OG:real^N->real^N->bool) xs)` THEN
      UNDISCH_TAC `(z:real^N) IN k` THEN
      REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN k` ASSUME_TAC THENL
     [UNDISCH_TAC `(xs:real^N->bool) SUBSET k` THEN UNDISCH_TAC `(x:real^N) IN xs` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `k SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(z:real^N) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "og" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP th (ASSUME `(x:real^N) IN k`)))) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "pxu" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN xs`))) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 21: connected pieces of a sheet.  A sheet n of a crossing chart is  *)
(* closed in the preimage of the chart domain and h o f is injective on it; *)
(* over a segment of its image plane, its part is compact, hence            *)
(* homeomorphic to the segment by h o f, hence connected.  With a constant  *)
(* sign lemma for connected sets this transports signs along the sheet.     *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_SIGN_CONN = prove
 (`!(s:real^M->bool) phi a b.
     connected s /\ (\x. lift(phi x)) continuous_on s /\ a IN s /\ b IN s /\
     (!x. x IN s ==> ~(phi x = &0))
     ==> (&0 < phi a <=> &0 < phi b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `connected (IMAGE (\x. lift(phi x)) (s:real^M->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~(p <=> q) ==> F) ==> (p <=> q)`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x y:real^M. x IN s /\ y IN s /\ phi x <= &0 /\ &0 <= phi y`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < phi(a:real^M)` THENL
     [MAP_EVERY EXISTS_TAC [`b:real^M`; `a:real^M`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift(phi(x:real^M)) IN IMAGE (\x. lift(phi x)) s /\
                lift(phi(y:real^M)) IN IMAGE (\x. lift(phi x)) s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `y:real^M` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\x. lift(phi x)) (s:real^M->bool)`; `lift(phi(x:real^M))`;
                 `lift(phi(y:real^M))`; `&0`; `1`] CONNECTED_IVT_COMPONENT) THEN
  ASM_REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; GSYM drop; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let MOI_LSM_SHEET_SEG = prove
 (`!(f:real^2->real^N) (u:real^N->bool) (h:real^N->real^3) h' n a b.
     f continuous_on std_triangle /\ h continuous_on u /\ h' continuous_on IMAGE h u /\
     (!z. z IN u ==> h' (h z) = z) /\ (!w. w IN IMAGE h u ==> h' w IN u /\ h (h' w) = w) /\
     n SUBSET {x | x IN std_triangle /\ f x IN u} /\
     closed_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n /\
     (!x x'. x IN n /\ x' IN n /\ f x = f x' ==> x = x') /\
     segment[h(f a),h(f b)] SUBSET IMAGE (h o f) n /\ a IN n /\ b IN n
     ==> ?K. connected K /\ K SUBSET n /\ a IN K /\ b IN K /\
             (!x. x IN K ==> h (f x) IN segment[h(f a),h(f b)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sg = segment[(h:real^N->real^3) (f(a:real^2)),h (f b)]` THEN
  SUBGOAL_THEN `compact (sg:real^3->bool) /\ connected sg /\
                h (f(a:real^2)) IN sg /\ (h:real^N->real^3) (f(b:real^2)) IN sg`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REWRITE_TAC[COMPACT_SEGMENT; CONNECTED_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^3->bool) SUBSET IMAGE (h:real^N->real^3) u` ASSUME_TAC THENL
   [UNDISCH_TAC `sg SUBSET IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n` THEN
    UNDISCH_TAC `n SUBSET {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; o_THM; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = {x | x IN n /\ (h:real^N->real^3) (f(x:real^2)) IN sg}` THEN
  SUBGOAL_THEN `compact (K:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `closed_in (subtopology euclidean
                   {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}) n` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(K:real^2->bool) =
                  {x | x IN std_triangle /\ (f:real^2->real^N) x IN
                       IMAGE (h':real^3->real^N) sg} INTER C`
    SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN
      UNDISCH_TAC `n = {x | x IN std_triangle /\ (f:real^2->real^N) x IN u} INTER C` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN
      EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `(h:real^N->real^3) (f(x:real^2))` THEN ASM_SIMP_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
        SUBGOAL_THEN `(w:real^3) IN IMAGE (h:real^N->real^3) u` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      SIMP_TAC[COMPACT_IMP_BOUNDED; MOI_LTD_STD_TRIANGLE_BASIC] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^2->bool) SUBSET n` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) continuous_on K` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) K = sg` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; o_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[o_THM] THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^2->bool`; `(h:real^N->real^3) o (f:real^2->real^N)`;
                 `sg:real^3->bool`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      length (fst(strip_forall (concl th))) = 2 &&
      can (find_term (fun t -> t = `n:real^2->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN u /\ (f:real^2->real^N) x' IN u` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^3->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:real^2->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `K = IMAGE (g0:real^3->real^2) sg` SUBST1_TAC THENL
     [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[homeomorphism];
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

(* A sheet of a chart, with the model coordinates g' of the disk. *)

let moi_lsm_sheet = new_definition
 `moi_lsm_sheet (f:real^2->real^N) (g:real^2->real^2) g' u (h:real^N->real^3) h' n j <=>
    f continuous_on std_triangle /\ g continuous_on moi_lcus_mr /\
    g' continuous_on std_triangle /\
    (!z. z IN moi_lcus_mr ==> g z IN std_triangle /\ g' (g z) = z) /\
    (!x. x IN std_triangle ==> g' x IN moi_lcus_mr /\ g (g' x) = x) /\
    h continuous_on u /\ h' continuous_on IMAGE h u /\ convex (IMAGE h u) /\
    (!z. z IN u ==> h' (h z) = z) /\ (!w. w IN IMAGE h u ==> h' w IN u /\ h (h' w) = w) /\
    n SUBSET {x | x IN std_triangle /\ f x IN u} /\
    closed_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n /\
    open_in (subtopology euclidean std_triangle) n /\
    (!x x'. x IN n /\ x' IN n /\ f x = f x' ==> x = x') /\
    IMAGE (h o f) n = IMAGE h u INTER {z:real^3 | z$j = &0}`;;

let MOI_LSM_SHEET_SEG2 = prove
 (`!(f:real^2->real^N) g g' u (h:real^N->real^3) h' n j a b.
     moi_lsm_sheet f g g' u h h' n j /\ a IN n /\ b IN n
     ==> ?K. connected K /\ K SUBSET n /\ a IN K /\ b IN K /\
             (!x. x IN K ==> h (f x) IN segment[h(f a),h(f b)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_sheet] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_LSM_SHEET_SEG THEN
  MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `h':real^3->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{z:real^3 | z$j = &0} = {z | z$j <= &0} INTER {z | z$j >= &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GE]];
    UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n =
                 IMAGE h u INTER {z:real^3 | z$j = &0}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN
    EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n =
                 IMAGE h u INTER {z:real^3 | z$j = &0}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN
    EXISTS_TAC `b:real^2` THEN ASM_REWRITE_TAC[]]);;

(* A sheet meeting no point with first model coordinate 3/2 stays on one side. *)

let MOI_LSM_SHEET_SIDE = prove
 (`!(f:real^2->real^N) g g' u (h:real^N->real^3) h' n j x0 x.
     moi_lsm_sheet f g g' u h h' n j /\
     (!x. x IN n ==> ~((g' x)$1 = &3 / &2)) /\ x0 IN n /\ x IN n
     ==> ((g' x0)$1 < &3 / &2 <=> (g' x)$1 < &3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_sheet]) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `g':real^2->real^2`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `n:real^2->bool`; `j:num`; `x0:real^2`; `x:real^2`] MOI_LSM_SHEET_SEG2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:real^2->bool`; `\x:real^2. &3 / &2 - ((g':real^2->real^2) x)$1`;
                 `x0:real^2`; `x:real^2`] MOI_LSM_SIGN_CONN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(((g':real^2->real^2) y)$1 = &3 / &2)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; REAL_ARITH_TAC]];
    REAL_ARITH_TAC]);;

(* The side of the chord is the sign of the other coordinate, up to one sign. *)

let MOI_LSM_SHEET_SIGN = prove
 (`!(f:real^2->real^N) g g' u (h:real^N->real^3) h' n j i a x0.
     moi_lsm_sheet f g g' u h h' n j /\
     (!x. x IN n ==> (((h:real^N->real^3) (f x))$i = &0 <=> ((g':real^2->real^2) x)$1 = a)) /\
     &1 <= a /\ a <= &2 /\ x0 IN n /\ (g' x0)$1 = a
     ==> ?ep. (ep = &1 \/ ep = -- &1) /\
              !x. x IN n ==> (&0 < ep * (h(f x))$i <=> a < (g' x)$1) /\
                             (ep * (h(f x))$i < &0 <=> (g' x)$1 < a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lsm_sheet]) THEN
  (* same sign of the i-th coordinate gives the same side *)
  SUBGOAL_THEN
   `!x x'. x IN n /\ x' IN n /\
           ((&0 < ((h:real^N->real^3) (f(x:real^2)))$i /\ &0 < (h(f(x':real^2)))$i) \/
            ((h(f x))$i < &0 /\ (h(f x'))$i < &0))
           ==> (a < ((g':real^2->real^2) x)$1 <=> a < (g' x')$1)`
  (LABEL_TAC "SAME") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `g':real^2->real^2`;
                   `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                   `n:real^2->bool`; `j:num`; `x:real^2`; `x':real^2`] MOI_LSM_SHEET_SEG2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!y. y IN K ==> ~(((h:real^N->real^3) (f(y:real^2)))$i = &0)` ASSUME_TAC THENL
     [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `((h:real^N->real^3) (f(y:real^2))) IN
                    segment[h(f(x:real^2)),h(f(x':real^2))]` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [SUBGOAL_THEN `segment[(h:real^N->real^3) (f(x:real^2)),h(f(x':real^2))] SUBSET
                      {w:real^3 | w$i > &0}` MP_TAC THENL
         [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
          ASM_REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT; IN_ELIM_THM; real_gt];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN MESON_TAC[REAL_LT_REFL]];
        SUBGOAL_THEN `segment[(h:real^N->real^3) (f(x:real^2)),h(f(x':real^2))] SUBSET
                      {w:real^3 | w$i < &0}` MP_TAC THENL
         [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
          ASM_REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT; IN_ELIM_THM];
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_REFL]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:real^2->bool`; `\x:real^2. ((g':real^2->real^2) x)$1 - a`;
                   `x:real^2`; `x':real^2`] MOI_LSM_SIGN_CONN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~(((g':real^2->real^2) y)$1 = a)` MP_TAC THENL
         [SUBGOAL_THEN `(y:real^2) IN n` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `!x. x IN n ==> (((h:real^N->real^3) (f(x:real^2)))$i = &0 <=>
                                      ((g':real^2->real^2) x)$1 = a)` THEN
          DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
          REAL_ARITH_TAC]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* two points of the sheet on both sides of the chord near x0 *)
  SUBGOAL_THEN `?e. &0 < e /\ ball(x0:real^2,e) INTER std_triangle SUBSET n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean std_triangle) (n:real^2->bool)` THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z0 = (g':real^2->real^2) x0` THEN
  SUBGOAL_THEN `(z0:real^2) IN moi_lcus_mr /\ (g:real^2->real^2) z0 = x0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ !z. z IN moi_lcus_mr /\ dist(z,z0) < d
                                  ==> dist((g:real^2->real^2) z,x0) < e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^2->real^2) continuous_on moi_lcus_mr` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `z0:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `dl = min (d / &2) (&1 / &4)` THEN
  SUBGOAL_THEN `&0 < dl /\ dl < d /\ dl <= &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs s <= dl
        ==> (z0 + s % basis 1:real^2) IN moi_lcus_mr /\
            (g:real^2->real^2) (z0 + s % basis 1) IN n /\
            ((g':real^2->real^2) (g (z0 + s % basis 1)))$1 = a + s`
  (LABEL_TAC "PQ") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z0 + s % basis 1:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
     [UNDISCH_TAC `(z0:real^2) IN moi_lcus_mr` THEN
      REWRITE_TAC[MOI_LSM_IN_MR; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
      UNDISCH_TAC `abs s <= dl` THEN UNDISCH_TAC `dl <= &1 / &4` THEN
      UNDISCH_TAC `(z0:real^2)$1 = a` THEN
      UNDISCH_TAC `&1 <= a` THEN UNDISCH_TAC `a <= &2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `ball(x0:real^2,e)`)) (concl th))) THEN
      REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[dist; VECTOR_ARITH `(z0 + s % b) - z0:real^2 = s % b`] THEN
        SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[]];
      ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                   DIMINDEX_2; ARITH] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID]];
    ALL_TAC] THEN
  USE_THEN "PQ" (MP_TAC o SPEC `dl:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `p = (g:real^2->real^2) (z0 + dl % basis 1)` THEN STRIP_TAC THEN
  USE_THEN "PQ" (MP_TAC o SPEC `--dl:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = (g:real^2->real^2) (z0 + --dl % basis 1)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(((h:real^N->real^3) (f(p:real^2)))$i = &0) /\
                ~(((h:real^N->real^3) (f(q:real^2)))$i = &0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((&0 < ((h:real^N->real^3) (f(p:real^2)))$i /\ &0 < (h(f(q:real^2)))$i) \/
                  ((h(f p))$i < &0 /\ (h(f q))$i < &0))` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "SAME" (MP_TAC o SPECL [`p:real^2`; `q:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < ((h:real^N->real^3) (f(p:real^2)))$i` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_MUL_LID];
    EXISTS_TAC `-- &1` THEN REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_NEG_GT0;
                                         REAL_NEG_LT0]] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `((h:real^N->real^3) (f(x:real^2)))$i = &0` THENL
   [SUBGOAL_THEN `((g':real^2->real^2) x)$1 = a` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC;
    SUBGOAL_THEN `((g':real^2->real^2) x)$1 = a` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (SUBGOAL_THEN `~(((g':real^2->real^2) x)$1 = a)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_CASES_TAC `&0 < ((h:real^N->real^3) (f(x:real^2)))$i` THENL
   [USE_THEN "SAME" (MP_TAC o SPECL [`x:real^2`; `p:real^2`]);
    USE_THEN "SAME" (MP_TAC o SPECL [`x:real^2`; `q:real^2`]);
    USE_THEN "SAME" (MP_TAC o SPECL [`x:real^2`; `q:real^2`]);
    USE_THEN "SAME" (MP_TAC o SPECL [`x:real^2`; `p:real^2`])] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 22: normalized charts.  A1, A2 are the parts of the disk around    *)
(* the two chords (first model coordinate within 1/2 of 1, resp. of 2).    *)
(* A crossing chart at a point of k whose domain sees only A1 UNION A2 and  *)
(* no double point off k has one sheet in A1 and one in A2; composing the  *)
(* chart with a signed permutation of the first two coordinates puts the   *)
(* A1 sheet on z1 = 0 with z2 > 0 exactly to the right of the first chord,  *)
(* and the A2 sheet on z2 = 0 with z1 < 0 exactly to the right of the      *)
(* second chord.                                                            *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_a1 = new_definition
 `moi_lsm_a1 (g':real^2->real^2) =
    {x | x IN std_triangle /\ &1 / &2 < (g' x)$1 /\ (g' x)$1 < &3 / &2}`;;

let moi_lsm_a2 = new_definition
 `moi_lsm_a2 (g':real^2->real^2) =
    {x | x IN std_triangle /\ &3 / &2 < (g' x)$1 /\ (g' x)$1 < &5 / &2}`;;

let moi_lsm_lm = new_definition
 `moi_lsm_lm sw a b (z:real^3) =
    if sw then vector[a * z$2; b * z$1; z$3] else vector[a * z$1; b * z$2; z$3]:real^3`;;

let moi_lsm_lmi = new_definition
 `moi_lsm_lmi sw a b (z:real^3) =
    if sw then vector[b * z$2; a * z$1; z$3] else vector[a * z$1; b * z$2; z$3]:real^3`;;

let MOI_LSM_LM = prove
 (`!sw a b. (a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1)
            ==> linear (moi_lsm_lm sw a b) /\ linear (moi_lsm_lmi sw a b) /\
                (!z. moi_lsm_lmi sw a b (moi_lsm_lm sw a b z) = z) /\
                (!z. moi_lsm_lm sw a b (moi_lsm_lmi sw a b z) = z) /\
                (!z. norm (moi_lsm_lm sw a b z) = norm z) /\
                (!z. (moi_lsm_lm sw a b z)$3 = z$3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[linear; moi_lsm_lm; moi_lsm_lmi; NORM_EQ; DOT_3; CART_EQ; DIMINDEX_3;
              FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  BOOL_CASES_TAC `sw:bool` THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LSM_CHART_LIN = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' (L:real^3->real^3) L'.
     linear L /\ linear L' /\ (!z. L' (L z) = z) /\ (!z. L (L' z) = z) /\
     (!z. norm (L z) = norm z) /\ (!z. (L z)$3 = z$3) /\
     moi_lsm_chart c u h h'
     ==> moi_lsm_chart c u (L o h) (h' o L')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. norm ((L':real^3->real^3) w) = norm w /\ (L' w)$3 = w$3` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_chart c u (h:real^N->real^3) h'` THEN
    REWRITE_TAC[moi_lsm_chart] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!w. (L':real^3->real^3) w IN IMAGE (h:real^N->real^3) u <=> w IN IMAGE h u) /\
                (!w. (L:real^3->real^3) w IN IMAGE h u <=> w IN IMAGE h u)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_chart c u (h:real^N->real^3) h'` THEN
    REWRITE_TAC[moi_lsm_chart] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. IMAGE (L:real^3->real^3) s = {w | L' w IN s}` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(L':real^3->real^3) w` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((L:real^3->real^3) o (h:real^N->real^3)) u = IMAGE h u` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (:real^3) (L:real^3->real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3)`; `L:real^3->real^3`; `vec 0:real^3`] PL_MAP_ON_AFFINE) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; VECTOR_ADD_RID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on u ((L:real^3->real^3) o (h:real^N->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE (h:real^N->real^3) u)
                 ((L:real^3->real^3) o h,(h':real^3->real^N) o (L':real^3->real^3))`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphism; o_THM] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(L':real^3->real^3) w IN IMAGE (h:real^N->real^3) u` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `v:real^N` THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `(L':real^3->real^3) ((h:real^N->real^3) v) IN IMAGE h u` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `(L:real^3->real^3) ((h:real^N->real^3) z)` THEN
        REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_chart; pl_homeomorphism] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `(L:real^3->real^3) o (h:real^N->real^3)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lsm_chart c u (h:real^N->real^3) h'` THEN
  REWRITE_TAC[moi_lsm_chart] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_BALL_0] THEN ASM_REWRITE_TAC[]);;

(* Consequences of the setup used for the charts. *)

let MOI_LSM_SETUP_FACTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' e k.
     moi_lsm_setup c f g g' e k
     ==> f continuous_on std_triangle /\ IMAGE f std_triangle SUBSET UNIONS c /\
         (!y. FINITE {x | x IN std_triangle /\ f x = y} /\
              CARD {x | x IN std_triangle /\ f x = y} <= 2) /\
         g continuous_on moi_lcus_mr /\ g' continuous_on std_triangle /\
         (!z. z IN moi_lcus_mr ==> g z IN std_triangle /\ g' (g z) = z) /\
         (!x. x IN std_triangle ==> g' x IN moi_lcus_mr /\ g (g' x) = x) /\
         (!x. x IN std_triangle ==> (f x IN k <=> (g' x)$1 = &1 \/ (g' x)$1 = &2)) /\
         k SUBSET moi_lt_double_image f /\
         (!y. y IN moi_lt_double_image f ==> moi_lt_crossing2_at c f y) /\
         {x | x IN std_triangle /\ f x IN complex_boundary c} = relative_frontier std_triangle`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o
              MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_homeomorphism (moi_lcus_mr,std_triangle) (g:real^2->real^2,g')` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g':real^2->real^2) x IN moi_lcus_mr /\ g (g' x) = x` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g':real^2->real^2) x` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `k:real^N->bool`)) (concl th) &&
      length (fst(strip_forall (concl th))) = 1)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_normal2_disk] THEN SIMP_TAC[]]);;

let moi_lsm_xdata = new_definition
 `moi_lsm_xdata (c:(real^N->bool)->bool) (f:real^2->real^N) y u (h:real^N->real^3) h' n1 n2 <=>
    open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
    pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
    ((~(y IN complex_boundary c) /\ u INTER complex_boundary c = {} /\
      IMAGE h u = ball(vec 0,&1)) \/
     (y IN complex_boundary c /\
      IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
      IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
    {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
    IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
    IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
    IMAGE h (moi_lt_double_image f INTER u) =
    IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
    open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n1 /\
    open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n2`;;

let MOI_LSM_THREE_PTS = prove
 (`!s:A->bool a b d. FINITE s /\ CARD s <= 2 /\ a IN s /\ b IN s /\ d IN s
                     ==> a = b \/ a = d \/ b = d`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `a:A = b` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:A = d` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `b:A = d` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `CARD {a:A,b,d} <= CARD (s:A->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD {a:A,b,d} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_ARITH_TAC]);;

let MOI_LSM_XDATA_CHART = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) y u (h:real^N->real^3) h' n1 n2.
     moi_lsm_xdata c f y u h h' n1 n2 ==> moi_lsm_chart c u h h'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsm_xdata; moi_lsm_chart] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
  ASM_REWRITE_TAC[]);;

(* A sheet is mapped injectively: a double point of a sheet would also be on *)
(* the other sheet, giving three preimages.                                 *)

let MOI_LSM_SHEET_INJ = prove
 (`!(f:real^2->real^N) u (h:real^N->real^3) h' n n'.
     (!y. FINITE {x | x IN std_triangle /\ f x = y} /\
          CARD {x | x IN std_triangle /\ f x = y} <= 2) /\
     (!z. z IN u ==> h' (h z) = z) /\
     n SUBSET {x | x IN std_triangle /\ f x IN u} /\
     n' SUBSET {x | x IN std_triangle /\ f x IN u} /\ DISJOINT n n' /\
     (!x x'. x IN n /\ x' IN n /\ ~(x = x') /\ f x = f x' ==> h (f x) IN IMAGE (h o f) n')
     ==> !x x'. x IN n /\ x' IN n /\ f x = f x' ==> x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `x:real^2 = x'` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `x':real^2`] o check (fun th ->
    is_forall (concl th) && length (fst (strip_forall (concl th))) = 2 &&
    can (find_term (fun t -> t = `n':real^2->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_IMAGE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x'':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle /\ (f:real^2->real^N) x IN u /\
                (x':real^2) IN std_triangle /\
                (x'':real^2) IN std_triangle /\ (f:real^2->real^N) x'' IN u`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) x'' = f x` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h':real^3->real^N) ((h:real^N->real^3) (f(x'':real^2))) =
                  h' (h (f(x:real^2)))` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{z | z IN std_triangle /\ (f:real^2->real^N) z = f x}`; `x:real^2`;
                 `x':real^2`; `x'':real^2`] MOI_LSM_THREE_PTS) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]);;

let MOI_LSM_XDATA_SHEETS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' e k y u (h:real^N->real^3) h' n1 n2.
     moi_lsm_setup c f g g' e k /\ moi_lsm_xdata c f y u h h' n1 n2
     ==> moi_lsm_sheet f g g' u h h' n1 1 /\ moi_lsm_sheet f g g' u h h' n2 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_SETUP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LSM_XDATA_CHART) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  SUBGOAL_THEN `convex (IMAGE (h:real^N->real^3) u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LSM_CHART_CONVEX]; ALL_TAC] THEN
  UNDISCH_TAC `moi_lsm_xdata c (f:real^2->real^N) y u h h' n1 n2` THEN
  REWRITE_TAC[moi_lsm_xdata] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `S = (n1:real^2->bool) UNION n2`)) THEN
  REWRITE_TAC[EXTENSION] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean std_triangle) (S:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_OPEN]
      (ASSUME `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN G}` SUBST1_TAC THENL
     [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n1:real^2->bool) SUBSET S /\ (n2:real^2->bool) SUBSET S`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN u ==> (h':real^3->real^N) ((h:real^N->real^3) z) = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x x'. x IN S /\ x' IN S /\ ~(x = x') /\ (f:real^2->real^N) x = f x'
                       ==> (h:real^N->real^3) (f x) IN IMAGE h u /\ (h (f x))$1 = &0 /\
                           (h (f x))$2 = &0`
  (LABEL_TAC "DP") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) (f(x:real^2)) IN IMAGE h (moi_lt_double_image f INTER u)`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTER; moi_lt_double_image; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x x'. x IN n1 /\ x' IN n1 /\ (f:real^2->real^N) x = f x' ==> x = x'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LSM_SHEET_INJ THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                          `n2:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN STRIP_TAC THEN
    USE_THEN "DP" (MP_TAC o SPECL [`x:real^2`; `x':real^2`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n2 =
                 IMAGE h u INTER {z:real^3 | z$2 = &0}` THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x x'. x IN n2 /\ x' IN n2 /\ (f:real^2->real^N) x = f x' ==> x = x'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LSM_SHEET_INJ THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                          `n1:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN STRIP_TAC THEN
    USE_THEN "DP" (MP_TAC o SPECL [`x:real^2`; `x':real^2`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1 =
                 IMAGE h u INTER {z:real^3 | z$1 = &0}` THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lsm_sheet] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `n1 = (S:real^2->bool) DIFF n2` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL];
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `S:real^2->bool` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `n2 = (S:real^2->bool) DIFF n1` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL];
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `S:real^2->bool` THEN ASM_REWRITE_TAC[]]);;

(* The double points of a chart domain are on k exactly over the chords.   *)

let MOI_LSM_XDATA_AXIS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' e k y u (h:real^N->real^3) h' n1 n2.
     moi_lsm_setup c f g g' e k /\ moi_lsm_xdata c f y u h h' n1 n2 /\
     DISJOINT u (moi_lt_double_image f DIFF k)
     ==> !x. x IN n1 \/ x IN n2
             ==> ((((h:real^N->real^3) (f x))$1 = &0 /\ (h (f x))$2 = &0) <=>
                  ((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_SETUP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LSM_XDATA_CHART) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  UNDISCH_TAC `moi_lsm_xdata c (f:real^2->real^N) y u h h' n1 n2` THEN
  REWRITE_TAC[moi_lsm_xdata] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle /\ (f:real^2->real^N) x IN u` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) x IN k <=>
                ((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2`
  (SUBST1_TAC o SYM) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) (f(x:real^2)) IN IMAGE h (moi_lt_double_image f INTER u)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:real^2->real^N) x = y'` SUBST1_TAC THENL
     [SUBGOAL_THEN `(h':real^3->real^N) ((h:real^N->real^3) (f(x:real^2))) = h' (h y')`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT u (moi_lt_double_image (f:real^2->real^N) DIFF k)` THEN
    UNDISCH_TAC `(y':real^N) IN u` THEN
    UNDISCH_TAC `(y':real^N) IN moi_lt_double_image f` THEN SET_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) (f(x:real^2)) IN IMAGE h (moi_lt_double_image f INTER u)`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER; IN_ELIM_THM]]);;

let MOI_LSM_LINV_INJ = prove
 (`!(h:real^N->real^3) h' u. (!z. z IN u ==> h' (h z) = z)
                             ==> !a b. a IN u /\ b IN u /\ h a = h b ==> a = b`,
  MESON_TAC[]);;

(* A chart at a point of k has a preimage of the point on each sheet, one *)
(* on each chord.                                                         *)

let MOI_LSM_XDATA_PTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' e k y u (h:real^N->real^3) h' n1 n2.
     moi_lsm_setup c f g g' e k /\ moi_lsm_xdata c f y u h h' n1 n2 /\ y IN k
     ==> ?x1 x2. x1 IN n1 /\ x2 IN n2 /\ f x1 = y /\ f x2 = y /\
                 ((((g':real^2->real^2) x1)$1 = &1 /\ (g' x2)$1 = &2) \/
                  ((g' x1)$1 = &2 /\ (g' x2)$1 = &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_SETUP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LSM_XDATA_CHART) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  UNDISCH_TAC `moi_lsm_xdata c (f:real^2->real^N) y u h h' n1 n2` THEN
  REWRITE_TAC[moi_lsm_xdata] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(h:real^N->real^3) y IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1 /\
                (h:real^N->real^3) y IN IMAGE (h o f) n2` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VEC_COMPONENT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(h:real^N->real^3) y = vec 0`)) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; o_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^2` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x1:real^2) IN std_triangle /\ (f:real^2->real^N) x1 IN u /\
                (x2:real^2) IN std_triangle /\ (f:real^2->real^N) x2 IN u`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x1:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN u} /\
                  (x2:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) x1 = y /\ (f:real^2->real^N) x2 = y` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^3`; `h':real^3->real^N`; `u:real^N->bool`]
      MOI_LSM_LINV_INJ) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x1:real^2`; `x2:real^2`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN std_triangle /\ (f:real^2->real^N) x = y
                    ==> ((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!x. x IN std_triangle
                     ==> ((f:real^2->real^N) x IN k <=>
                          ((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2)` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(((g':real^2->real^2) x1)$1 = &1 \/ (g' x1)$1 = &2) /\
                ((g' x2)$1 = &1 \/ (g' x2)$1 = &2)` (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(((g':real^2->real^2) x1)$1 = (g' x2)$1)` MP_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(g':real^2->real^2) x1`; `(g':real^2->real^2) x2`] o
      check (fun th -> is_forall (concl th) && length (fst(strip_forall (concl th))) = 2 &&
        can (find_term (fun t -> t = `&2`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x1:real^2 = x2` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN
    UNDISCH_TAC `(x1:real^2) IN n1` THEN UNDISCH_TAC `(x2:real^2) IN n2` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `((g':real^2->real^2) x1)$1 = &1 \/ (g' x1)$1 = &2` THEN
  UNDISCH_TAC `((g':real^2->real^2) x2)$1 = &1 \/ (g' x2)$1 = &2` THEN
  REAL_ARITH_TAC);;

(* Normalized charts. *)

let moi_lsm_nchart = new_definition
 `moi_lsm_nchart (c:(real^N->bool)->bool) (f:real^2->real^N) (g':real^2->real^2) u
                 (H:real^N->real^3) H' y <=>
    moi_lsm_chart c u H H' /\ y IN u /\ H y = vec 0 /\
    (!x. x IN std_triangle /\ f x IN u
         ==> (x IN moi_lsm_a1 g' /\ (H(f x))$1 = &0 /\
              (&0 < (H(f x))$2 <=> &1 < (g' x)$1) /\ ((H(f x))$2 < &0 <=> (g' x)$1 < &1)) \/
             (x IN moi_lsm_a2 g' /\ (H(f x))$2 = &0 /\
              ((H(f x))$1 < &0 <=> &2 < (g' x)$1) /\ (&0 < (H(f x))$1 <=> (g' x)$1 < &2))) /\
    (!w. w IN IMAGE H u /\ (w$1 = &0 \/ w$2 = &0)
         ==> ?x. x IN std_triangle /\ f x IN u /\ H(f x) = w)`;;

let MOI_LSM_NORMALIZE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g' u (h:real^N->real^3) h' y sw a b.
     moi_lsm_chart c u h h' /\ y IN u /\ h y = vec 0 /\
     (a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1) /\
     (!x. x IN std_triangle /\ f x IN u
          ==> (x IN moi_lsm_a1 g' /\ (moi_lsm_lm sw a b (h(f x)))$1 = &0 /\
               (&0 < (moi_lsm_lm sw a b (h(f x)))$2 <=> &1 < (g' x)$1) /\
               ((moi_lsm_lm sw a b (h(f x)))$2 < &0 <=> (g' x)$1 < &1)) \/
              (x IN moi_lsm_a2 g' /\ (moi_lsm_lm sw a b (h(f x)))$2 = &0 /\
               ((moi_lsm_lm sw a b (h(f x)))$1 < &0 <=> &2 < (g' x)$1) /\
               (&0 < (moi_lsm_lm sw a b (h(f x)))$1 <=> (g' x)$1 < &2))) /\
     (!v. v IN IMAGE h u /\
          ((moi_lsm_lm sw a b v)$1 = &0 \/ (moi_lsm_lm sw a b v)$2 = &0)
          ==> ?x. x IN std_triangle /\ f x IN u /\ h (f x) = v)
     ==> moi_lsm_nchart c f g' u (moi_lsm_lm sw a b o h) (h' o moi_lsm_lmi sw a b) y`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`sw:bool`; `a:real`; `b:real`] MOI_LSM_LM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[moi_lsm_nchart; o_THM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LSM_CHART_LIN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPEC `moi_lsm_lm sw a b` LINEAR_0) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; o_THM] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^N->real^3) z` o check (fun th ->
      is_forall (concl th) && length (fst(strip_forall (concl th))) = 1 &&
      can (find_term (fun t -> t = `IMAGE (h:real^N->real^3) u`)) (concl th) &&
      can (find_term (fun t -> t = `std_triangle`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3)$1 = &0 \/ w$2 = &0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]]);;

let MOI_LSM_LM_CASE = prove
 (`!sw a b jA jB (z:real^3).
     (jA = 1 /\ jB = 2 /\ sw = F) \/ (jA = 2 /\ jB = 1 /\ sw = T)
     ==> (moi_lsm_lm sw a b z)$1 = a * z$jA /\ (moi_lsm_lm sw a b z)$2 = b * z$jB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_lsm_lm; VECTOR_3]);;

(* One sheet in A1 and one in A2: the normalized chart. *)

let MOI_LSM_NCH_CASE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' u (h:real^N->real^3) h' y nA nB
    jA jB sw xA xB.
     moi_lsm_chart c u h h' /\ y IN u /\ h y = vec 0 /\
     ((jA = 1 /\ jB = 2 /\ sw = F) \/ (jA = 2 /\ jB = 1 /\ sw = T)) /\
     moi_lsm_sheet f g g' u h h' nA jA /\ moi_lsm_sheet f g g' u h h' nB jB /\
     {x | x IN std_triangle /\ f x IN u} = nA UNION nB /\
     nA SUBSET moi_lsm_a1 g' /\ nB SUBSET moi_lsm_a2 g' /\
     (!x. x IN nA ==> ((h (f x))$jB = &0 <=> (g' x)$1 = &1)) /\
     (!x. x IN nB ==> ((h (f x))$jA = &0 <=> (g' x)$1 = &2)) /\
     xA IN nA /\ (g' xA)$1 = &1 /\ xB IN nB /\ (g' xB)$1 = &2
     ==> ?H H'. moi_lsm_nchart c f g' u H H' y`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `g':real^2->real^2`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `nA:real^2->bool`; `jA:num`; `jB:num`; `&1`; `xA:real^2`]
    MOI_LSM_SHEET_SIGN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `epA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SA"))) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `g':real^2->real^2`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `nB:real^2->bool`; `jB:num`; `jA:num`; `&2`; `xB:real^2`]
    MOI_LSM_SHEET_SIGN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `epB:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SB"))) THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) nA =
                IMAGE h u INTER {z:real^3 | z$jA = &0} /\
                IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) nB =
                IMAGE h u INTER {z:real^3 | z$jB = &0}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_sheet f g g' u (h:real^N->real^3) h' nA jA` THEN
    UNDISCH_TAC `moi_lsm_sheet f g g' u (h:real^N->real^3) h' nB jB` THEN
    REWRITE_TAC[moi_lsm_sheet] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN nA ==> ((h:real^N->real^3) (f(x:real^2)))$jA = &0) /\
                (!x. x IN nB ==> ((h:real^N->real^3) (f(x:real^2)))$jB = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) x IN IMAGE (h o f) nA`
      MP_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC];
      SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) x IN IMAGE (h o f) nB`
      MP_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC]] THEN
    ASM_REWRITE_TAC[o_THM; IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(--epB = &0) /\ ~(epA = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `moi_lsm_lm sw (--epB) epA o (h:real^N->real^3)` THEN
  EXISTS_TAC `(h':real^3->real^N) o moi_lsm_lmi sw (--epB) epA` THEN
  MATCH_MP_TAC MOI_LSM_NORMALIZE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`sw:bool`; `--epB:real`; `epA:real`; `jA:num`; `jB:num`] MOI_LSM_LM_CASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN nA \/ x IN nB` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = nA UNION nB` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lsm_a1 g'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO];
      DISJ2_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lsm_a2 g'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LNEG; REAL_NEG_LT0; REAL_NEG_GT0] THEN
      USE_THEN "SB" (MP_TAC o C MP (ASSUME `(x:real^2) IN nB`) o SPEC `x:real^2`) THEN
      SIMP_TAC[]];
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN X_GEN_TAC `v:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
     [SUBGOAL_THEN `(v:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) nA` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC];
      SUBGOAL_THEN `(v:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) nB` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC]] THEN
    REWRITE_TAC[IN_IMAGE; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = nA UNION nB` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[]]);;

(* The normalized chart at a point of k inside a given neighbourhood. *)

let MOI_LSM_NCHART = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' e k y V.
     moi_lsm_setup c f g g' e k /\ y IN k /\ open V /\ y IN V /\
     (!x. x IN std_triangle /\ f x IN V ==> x IN moi_lsm_a1 g' \/ x IN moi_lsm_a2 g') /\
     DISJOINT V (moi_lt_double_image f DIFF k)
     ==> ?u (H:real^N->real^3) H'. u SUBSET V /\ moi_lsm_nchart c f g' u H H' y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y:real^N`; `V:real^N->bool`]
    MOI_LC0_CROSSING2_SHRINK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `moi_lt_crossing2_at:((real^N->bool)->bool)->
                                     (real^2->real^N)->real^N->bool`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_lsm_xdata] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `n1:real^2->bool`
      (X_CHOOSE_THEN `n2:real^2->bool` STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `y:real^N`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `n1:real^2->bool`; `n2:real^2->bool`] MOI_LSM_XDATA_SHEETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `y:real^N`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `n1:real^2->bool`; `n2:real^2->bool`] MOI_LSM_XDATA_PTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `x2:real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CASE"))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LSM_XDATA_CHART) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `y:real^N`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `n1:real^2->bool`; `n2:real^2->bool`] MOI_LSM_XDATA_AXIS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `moi_lsm_xdata c (f:real^2->real^N) y u h h' n1 n2` THEN
  REWRITE_TAC[moi_lsm_xdata] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (* membership and the planes of the sheets *)
  SUBGOAL_THEN `!x. x IN n1 \/ x IN n2
                    ==> x IN std_triangle /\ (f:real^2->real^N) x IN u`
  (LABEL_TAC "MEM") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN n1 ==> ((h:real^N->real^3) (f(x:real^2)))$1 = &0) /\
                (!x. x IN n2 ==> ((h:real^N->real^3) (f(x:real^2)))$2 = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) x IN IMAGE (h o f) n1`
      MP_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC];
      SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) x IN IMAGE (h o f) n2`
      MP_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC]] THEN
    ASM_REWRITE_TAC[o_THM; IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the axis on each sheet *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `&2`)) (concl th) &&
    can (find_term (fun t -> t = `n2:real^2->bool`)) (concl th) &&
    can (find_term (fun t -> t = `n1:real^2->bool`)) (concl th))) THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN
     `(!x. x IN n1 ==> (((h:real^N->real^3) (f(x:real^2)))$2 = &0 <=>
                       ((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2)) /\
      (!x. x IN n2 ==> (((h:real^N->real^3) (f(x:real^2)))$1 = &0 <=>
                       ((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2))`
    (CONJUNCTS_THEN2 (LABEL_TAC "AX1") (LABEL_TAC "AX2")) THENL
     [CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(SPEC `x:real^2` th) THEN ASM_SIMP_TAC[];
      ALL_TAC]) THEN
  (* the cover of the sheets by A1 and A2 *)
  SUBGOAL_THEN `!x. x IN n1 \/ x IN n2 ==> x IN moi_lsm_a1 g' \/ x IN moi_lsm_a2 g'`
  (LABEL_TAC "COV") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "MEM" (MP_TAC o C MP (ASSUME `(x:real^2) IN n1 \/ x IN n2`) o SPEC `x:real^2`) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN n1 \/ x IN n2 ==> ~(((g':real^2->real^2) x)$1 = &3 / &2)`
  (LABEL_TAC "COV2") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "COV" (MP_TAC o C MP (ASSUME `(x:real^2) IN n1 \/ x IN n2`) o SPEC `x:real^2`) THEN
    REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a sheet lies on the side of its chord point *)
  SUBGOAL_THEN
   `!n j x0. moi_lsm_sheet f g g' u (h:real^N->real^3) h' n j /\
             (!z. z IN n ==> z IN n1 \/ z IN n2) /\ x0 IN n
             ==> ((((g':real^2->real^2) x0)$1 = &1 ==> n SUBSET moi_lsm_a1 g') /\
                  ((g' x0)$1 = &2 ==> n SUBSET moi_lsm_a2 g'))`
  (LABEL_TAC "SIDE") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `g':real^2->real^2`;
                   `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                   `n:real^2->bool`; `j:num`; `x0:real^2`; `x:real^2`] MOI_LSM_SHEET_SIDE) THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
       USE_THEN "COV2" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN
    (SUBGOAL_THEN `(x:real^2) IN moi_lsm_a1 g' \/ x IN moi_lsm_a2 g'` MP_TAC THENL
      [USE_THEN "COV" MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      t = `(g':real^2->real^2) x$1`)) (concl th) && not (is_forall (concl th))))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "CASE" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [(* n1 around the first chord, n2 around the second *)
    USE_THEN "SIDE" (MP_TAC o SPECL [`n1:real^2->bool`; `1`; `x1:real^2`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "SIDE" (MP_TAC o SPECL [`n2:real^2->bool`; `2`; `x2:real^2`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                         `g':real^2->real^2`; `u:real^N->bool`; `h:real^N->real^3`;
                         `h':real^3->real^N`; `y:real^N`; `n1:real^2->bool`;
                         `n2:real^2->bool`; `1`; `2`; `F`; `x1:real^2`; `x2:real^2`]
                 MOI_LSM_NCH_CASE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THENL
     [USE_THEN "AX1" (MP_TAC o C MP (ASSUME `(x:real^2) IN n1`) o SPEC `x:real^2`) THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lsm_a1 g'` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      USE_THEN "AX2" (MP_TAC o C MP (ASSUME `(x:real^2) IN n2`) o SPEC `x:real^2`) THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lsm_a2 g'` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC]] THEN
    REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      t = `(g':real^2->real^2) x$1`)) (concl th) && not (is_forall (concl th))))) THEN
    REAL_ARITH_TAC;
    (* n2 around the first chord, n1 around the second *)
    USE_THEN "SIDE" (MP_TAC o SPECL [`n1:real^2->bool`; `1`; `x1:real^2`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "SIDE" (MP_TAC o SPECL [`n2:real^2->bool`; `2`; `x2:real^2`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                         `g':real^2->real^2`; `u:real^N->bool`; `h:real^N->real^3`;
                         `h':real^3->real^N`; `y:real^N`; `n2:real^2->bool`;
                         `n1:real^2->bool`; `2`; `1`; `T`; `x2:real^2`; `x1:real^2`]
                 MOI_LSM_NCH_CASE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THENL
     [USE_THEN "AX2" (MP_TAC o C MP (ASSUME `(x:real^2) IN n2`) o SPEC `x:real^2`) THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lsm_a1 g'` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      USE_THEN "AX1" (MP_TAC o C MP (ASSUME `(x:real^2) IN n1`) o SPEC `x:real^2`) THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lsm_a2 g'` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC]] THEN
    REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      t = `(g':real^2->real^2) x$1`)) (concl th) && not (is_forall (concl th))))) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 23: the labels of the normalized charts.  P1 (P2) is the image of   *)
(* the part of the disk just to the right of the first (second) chord, the  *)
(* seam points X are the images of the seam-1 side of the model, and ff is  *)
(* the image of the disk.  A normalized chart is labelled by them, maps X   *)
(* into the seam, and maps k into the axis.                                 *)
(* ------------------------------------------------------------------------- *)

let moi_lsm_p1 = new_definition
 `moi_lsm_p1 (f:real^2->real^N) (g':real^2->real^2) =
    IMAGE f {x | x IN std_triangle /\ &1 < (g' x)$1 /\ (g' x)$1 < &3 / &2}`;;

let moi_lsm_p2 = new_definition
 `moi_lsm_p2 (f:real^2->real^N) (g':real^2->real^2) =
    IMAGE f {x | x IN std_triangle /\ &2 < (g' x)$1 /\ (g' x)$1 < &5 / &2}`;;

let moi_lsm_xs = new_definition
 `moi_lsm_xs (f:real^2->real^N) (g:real^2->real^2) =
    IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&3 / &2; &1]] UNION
                      interval[vector[&2; &0],vector[&3; &1]]))`;;

let MOI_LSM_NCH_LAB = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' e k u (H:real^N->real^3) H' y.
     moi_lsm_setup c f g g' e k /\ moi_lsm_nchart c f g' u H H' y
     ==> moi_lsm_lab u H (moi_lsm_p1 f g') (moi_lsm_p2 f g') (IMAGE f std_triangle) /\
         (!z. z IN u /\ z IN moi_lsm_xs f g
              ==> ((H z)$1 = &0 /\ &0 <= (H z)$2) \/ ((H z)$2 = &0 /\ (H z)$1 <= &0)) /\
         (!z. z IN u /\ z IN k ==> (H z)$1 = &0 /\ (H z)$2 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_SETUP_FACTS) THEN
  UNDISCH_TAC `moi_lsm_nchart c (f:real^2->real^N) g' u (H:real^N->real^3) H' y` THEN
  REWRITE_TAC[moi_lsm_nchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "N") (LABEL_TAC "S"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_CHART_FACTS) THEN
  MP_TAC(ISPECL [`H:real^N->real^3`; `H':real^3->real^N`; `u:real^N->bool`]
    MOI_LSM_LINV_INJ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "INJ")] THEN
  (* a point of u with a vanishing coordinate is f of a point of the disk *)
  SUBGOAL_THEN
   `!z. z IN u /\ (((H:real^N->real^3) z)$1 = &0 \/ (H z)$2 = &0)
        ==> ?x. x IN std_triangle /\ (f:real^2->real^N) x IN u /\ f x = z`
  (LABEL_TAC "PRE") THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    USE_THEN "S" (MP_TAC o SPEC `(H:real^N->real^3) z`) THEN
    (ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the labels *)
    REWRITE_TAC[moi_lsm_lab] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_lsm_p1; moi_lsm_p2; IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
      USE_THEN "N" (MP_TAC o SPEC `x:real^2`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
      UNDISCH_TAC `&1 < ((g':real^2->real^2) x)$1` THEN
      UNDISCH_TAC `((g':real^2->real^2) x)$1 < &3 / &2` THEN REAL_ARITH_TAC;
      STRIP_TAC THEN
      USE_THEN "PRE" (MP_TAC o SPEC `z:real^N`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "N" (MP_TAC o SPEC `x:real^2`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
      UNDISCH_TAC `((H:real^N->real^3) z)$1 = &0` THEN
      UNDISCH_TAC `&0 < ((H:real^N->real^3) z)$2` THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
      USE_THEN "N" (MP_TAC o SPEC `x:real^2`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
      UNDISCH_TAC `&2 < ((g':real^2->real^2) x)$1` THEN
      UNDISCH_TAC `((g':real^2->real^2) x)$1 < &5 / &2` THEN REAL_ARITH_TAC;
      STRIP_TAC THEN
      USE_THEN "PRE" (MP_TAC o SPEC `z:real^N`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "N" (MP_TAC o SPEC `x:real^2`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
      UNDISCH_TAC `((H:real^N->real^3) z)$2 = &0` THEN
      UNDISCH_TAC `((H:real^N->real^3) z)$1 < &0` THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      USE_THEN "N" (MP_TAC o SPEC `x:real^2`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN MESON_TAC[];
      DISCH_TAC THEN
      USE_THEN "PRE" (MP_TAC o SPEC `z:real^N`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]];
    (* the seam *)
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[moi_lsm_xs; IN_IMAGE; IN_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^2`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `p:real^2`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))))) THEN
    SUBGOAL_THEN `(p:real^2) IN moi_lcus_mr /\ &1 <= p$1 /\
                  (p$1 <= &3 / &2 \/ &2 <= p$1)`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
     [UNDISCH_TAC `(p:real^2) IN interval[vector[&1; &0],vector[&3 / &2; &1]] \/
                   p IN interval[vector[&2; &0],vector[&3; &1]]` THEN
      REWRITE_TAC[MOI_LSM_IN_MR; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^2->real^2) p IN std_triangle /\ (g':real^2->real^2) (g p) = p`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "N" (MP_TAC o SPEC `(g:real^2->real^2) p`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
    UNDISCH_TAC `&1 <= (p:real^2)$1` THEN
    UNDISCH_TAC `(p:real^2)$1 <= &3 / &2 \/ &2 <= p$1` THEN REAL_ARITH_TAC;
    (* the axis *)
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x. x IN std_triangle /\ (f:real^2->real^N) x = z` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(z:real^N) IN moi_lt_double_image f` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2` ASSUME_TAC THENL
     [UNDISCH_TAC `!x. x IN std_triangle
                       ==> ((f:real^2->real^N) x IN k <=>
                            ((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2)` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "N" (MP_TAC o SPEC `x:real^2`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN
    UNDISCH_TAC `((g':real^2->real^2) x)$1 = &1 \/ (g' x)$1 = &2` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 24: the push, given the neighbourhood V0 of k.  Normalized charts at *)
(* the points of k inside V0 (MOI_LSM_NCHART), labelled (NCH_LAB), give the  *)
(* hypothesis of MOI_LSM_COVER; the composite of the resulting pushes        *)
(* (Part 18) is the family hh and the union of the closed cubes is S; the    *)
(* invariant (Part 19), with the consistency of the quadrants (Part 20),     *)
(* moves the seam points off the disk or fixes them, and moves k off the     *)
(* disk.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_XS_FACTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g g' e k.
     moi_lsm_setup c f g g' e k
     ==> moi_lsm_xs f g SUBSET IMAGE f std_triangle /\ k SUBSET moi_lsm_xs f g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_SETUP_FACTS) THEN
  SUBGOAL_THEN `interval[vector[&1; &0],vector[&3 / &2; &1]] UNION
                interval[vector[&2; &0],vector[&3; &1]] SUBSET moi_lcus_mr`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION; MOI_LSM_IN_MR; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_lsm_xs] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x. x IN std_triangle /\ (f:real^2->real^N) x = y` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
  REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_lsm_xs; IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `p:real^2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `segment[vector[&1; &0]:real^2,vector[&1; &1]] SUBSET
                interval[vector[&1; &0],vector[&3 / &2; &1]] /\
                segment[vector[&2; &0]:real^2,vector[&2; &1]] SUBSET
                interval[vector[&2; &0],vector[&3; &1]]` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_INTERVAL; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ASM SET_TAC[]]);;

let MOI_LSM_OMEGA_OFF = prove
 (`!(c:(real^N->bool)->bool) U (Hh:num->real^N->real^3) Hi Cc R m P1 P2 ff.
     moi_lsm_fam c U Hh Hi Cc R m /\
     (!i. i < m ==> moi_lsm_lab (U i) (Hh i) P1 P2 ff)
     ==> !z. z IN moi_lsm_omega U Hh Cc R m ==> ~(z IN ff)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[moi_lsm_omega; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i < m:num`) o SPEC `i:num`) THEN
  REWRITE_TAC[moi_lsm_lab] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `((Hh:num->real^N->real^3) i z)$1 < &0` THEN
  UNDISCH_TAC `&0 < ((Hh:num->real^N->real^3) i z)$2` THEN REAL_ARITH_TAC);;

let MOI_LSM_PUSH_CORE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) w (g:real^2->real^2) g' e k V0.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lsm_setup c f g g' e k /\
     open V0 /\ k SUBSET V0 /\
     (!x. x IN std_triangle /\ f x IN V0 ==> x IN moi_lsm_a1 g' \/ x IN moi_lsm_a2 g') /\
     DISJOINT V0 (moi_lt_double_image f DIFF k) /\
     DISJOINT V0 (IMAGE (f o g) (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]])) /\
     V0 INTER complex_boundary c SUBSET w
     ==> ?(hh:real^1->real^N->real^N) S.
           closed S /\ k SUBSET S /\
           DISJOINT S (moi_lt_double_image f DIFF k) /\
           DISJOINT S (IMAGE (f o g) (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]])) /\
           S INTER complex_boundary c SUBSET w /\
           (\z. hh (fstcart z) (sndcart z)) continuous_on
             (interval[vec 0,vec 1] PCROSS UNIONS c) /\
           (!z. z IN UNIONS c ==> hh (vec 0) z = z) /\
           (!t z. t IN interval[vec 0,vec 1] /\ z IN UNIONS c
                  ==> hh t z IN UNIONS c /\
                      (hh t z IN complex_boundary c <=> z IN complex_boundary c) /\
                      (~(z IN S) ==> hh t z = z) /\
                      (z IN S ==> hh t z IN S)) /\
           pl_map_on (UNIONS c) (hh (vec 1)) /\
           (!z z'. z IN UNIONS c /\ z' IN UNIONS c /\ hh (vec 1) z = hh (vec 1) z'
                   ==> z = z') /\
           (!x. x IN IMAGE g (interval[vector[&1; &0],vector[&3 / &2; &1]] UNION
                              interval[vector[&2; &0],vector[&3; &1]])
                ==> hh (vec 1) (f x) = f x \/
                    ~(hh (vec 1) (f x) IN IMAGE f std_triangle)) /\
           (!y. y IN k ==> ~(hh (vec 1) y IN IMAGE f std_triangle))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSM_XS_FACTS) THEN
  SUBGOAL_THEN `compact (k:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lsm_setup c (f:real^2->real^N) g g' e k` THEN
    REWRITE_TAC[moi_lsm_setup] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o
                MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the cover *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:real^N->bool`; `V0:real^N->bool`;
                 `moi_lsm_xs (f:real^2->real^N) g`; `moi_lsm_p1 (f:real^2->real^N) g'`;
                 `moi_lsm_p2 (f:real^2->real^N) g'`; `IMAGE (f:real^2->real^N) std_triangle`]
    MOI_LSM_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `y:real^N`;
                   `V0:real^N->bool`] MOI_LSM_NCHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `H:real^N->real^3`
      (X_CHOOSE_THEN `H':real^3->real^N` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `H:real^N->real^3`; `H':real^3->real^N`] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                   `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `u:real^N->bool`;
                   `H:real^N->real^3`; `H':real^3->real^N`; `y:real^N`] MOI_LSM_NCH_LAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lsm_nchart c (f:real^2->real^N) g' u (H:real^N->real^3) H' y` THEN
    REWRITE_TAC[moi_lsm_nchart] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `U:num->real^N->bool`
    (X_CHOOSE_THEN `Hh:num->real^N->real^3` (X_CHOOSE_THEN `Hi:num->real^3->real^N`
      (X_CHOOSE_THEN `Cc:num->real^3` (X_CHOOSE_THEN `R:num->real`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CH")
          (CONJUNCTS_THEN2 (LABEL_TAC "OV") ASSUME_TAC))))))))) THEN
  (* support facts *)
  SUBGOAL_THEN `moi_lsm_supp U (Hh:num->real^N->real^3) Cc R m SUBSET V0` ASSUME_TAC THENL
   [REWRITE_TAC[moi_lsm_supp; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "CH" (MP_TAC o C MP (ASSUME `i < m:num`) o SPEC `i:num`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (moi_lsm_supp U (Hh:num->real^N->real^3) Cc R m)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `moi_lsm_supp U (Hh:num->real^N->real^3) Cc R m =
      UNIONS (IMAGE (\i. {z | z IN U i /\ moi_lsm_sn (Hh i z - Cc i) <= R i}) {i | i < m})`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_lsm_supp; UNIONS_IMAGE; IN_ELIM_THM; EXTENSION] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) i`;
                   `(Hh:num->real^N->real^3) i`; `(Hi:num->real^3->real^N) i`;
                   `(Cc:num->real^3) i`; `(R:num->real) i`] MOI_LSM_CHART_CUBE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_LSM_FAM_AT THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lsm_supp U (Hh:num->real^N->real^3) Cc R m`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET moi_lsm_ocov U (Hh:num->real^N->real^3) Cc R m` THEN
    REWRITE_TAC[moi_lsm_ocov; moi_lsm_supp; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 1:real^1) IN interval[vec 0,vec 1] /\ &0 < drop(vec 1:real^1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the invariant at time 1 *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`; `Hh:num->real^N->real^3`;
                 `Hi:num->real^3->real^N`; `Cc:num->real^3`; `R:num->real`; `m:num`;
                 `vec 1:real^1`; `moi_lsm_xs (f:real^2->real^N) g`] MOI_LSM_COMP_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "CH" (MP_TAC o C MP (ASSUME `i < m:num`) o SPEC `i:num`) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `z:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `i < m:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "CH" (STRIP_ASSUME_TAC o C MP (ASSUME `i < m:num`) o SPEC `i:num`) THEN
      USE_THEN "CH" (STRIP_ASSUME_TAC o C MP (ASSUME `j < m:num`) o SPEC `j:num`) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                     `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`; `Cc:num->real^3`;
                     `R:num->real`; `m:num`; `i:num`] MOI_LSM_FAM_AT) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                     `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`; `Cc:num->real^3`;
                     `R:num->real`; `m:num`; `j:num`] MOI_LSM_FAM_AT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(U:num->real^N->bool) i`;
                           `(Hh:num->real^N->real^3) i`; `(Hi:num->real^3->real^N) i`;
                           `(U:num->real^N->bool) j`; `(Hh:num->real^N->real^3) j`;
                           `(Hi:num->real^3->real^N) j`; `(Cc:num->real^3) i`;
                           `(R:num->real) i`; `moi_lsm_p1 (f:real^2->real^N) g'`;
                           `moi_lsm_p2 (f:real^2->real^N) g'`;
                           `IMAGE (f:real^2->real^N) std_triangle`; `z:real^N`]
                   MOI_LSM_CONSIST) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "OV" (MP_TAC o SPECL [`i:num`; `j:num`; `z:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    DISCH_THEN(LABEL_TAC "INV")] THEN
  SUBGOAL_THEN `!z. z IN moi_lsm_omega U (Hh:num->real^N->real^3) Cc R m
                    ==> ~(z IN IMAGE (f:real^2->real^N) std_triangle)`
  (LABEL_TAC "OFF") THENL
   [MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                         `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`;
                         `Cc:num->real^3`; `R:num->real`; `m:num`;
                         `moi_lsm_p1 (f:real^2->real^N) g'`; `moi_lsm_p2 (f:real^2->real^N) g'`;
                         `IMAGE (f:real^2->real^N) std_triangle`] MOI_LSM_OMEGA_OFF) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "CH" (MP_TAC o C MP (ASSUME `i < m:num`) o SPEC `i:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the family and the support *)
  EXISTS_TAC `\t z. moi_lsm_comp U Hh Hi Cc R t m (z:real^N)` THEN
  EXISTS_TAC `moi_lsm_supp U (Hh:num->real^N->real^3) Cc R m` THEN
  REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_LSM_COMP_CONT THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[LE_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LSM_COMP_ZERO THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `m:num`] THEN ASM_REWRITE_TAC[LE_REFL];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                   `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`; `Cc:num->real^3`;
                   `R:num->real`; `m:num`; `t:real^1`] MOI_LSM_COMP_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`m:num`; `z:real^N`]) THEN
    ASM_REWRITE_TAC[LE_REFL];
    MATCH_MP_TAC MOI_LSM_COMP_PL THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[LE_REFL];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:num->real^N->bool`;
                   `Hh:num->real^N->real^3`; `Hi:num->real^3->real^N`; `Cc:num->real^3`;
                   `R:num->real`; `m:num`; `vec 1:real^1`] MOI_LSM_COMP_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[LE_REFL] THEN MESON_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN moi_lsm_xs f g` ASSUME_TAC THENL
     [REWRITE_TAC[moi_lsm_xs] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "INV" (MP_TAC o SPECL [`m:num`; `(f:real^2->real^N) x`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_CASES_TAC `(f:real^2->real^N) x IN moi_lsm_ocov U Hh Cc R m` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN moi_lsm_xs f g /\ y IN moi_lsm_ocov U Hh Cc R m`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "INV" (MP_TAC o SPECL [`m:num`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 24b: the open neighbourhood V0 of k, the statement MOI_LSM_V0_STMT   *)
(* and its proof MOI_LSM_V0.  V0 is the complement of four closed sets       *)
(* missing k: f of the disk off the two bands around the chords, the double  *)
(* image off k, f o g of the middle segment, and the boundary off w.         *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_V0_STMT =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) g' e k w.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lsm_setup c f g g' e k /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE f (relative_frontier std_triangle) SUBSET w
     ==> ?V0. open V0 /\ k SUBSET V0 /\
              (!x. x IN std_triangle /\ f x IN V0
                   ==> (&1 / &2 < (g' x)$1 /\ (g' x)$1 < &3 / &2) \/
                       (&3 / &2 < (g' x)$1 /\ (g' x)$1 < &5 / &2)) /\
              DISJOINT V0 (moi_lt_double_image f DIFF k) /\
              DISJOINT V0 (IMAGE (f o g) (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]])) /\
              V0 INTER complex_boundary c SUBSET w`;;

(* ------------------------------------------------------------------------- *)
(* The proof MOI_LSM_V0 of MOI_LSM_V0_STMT, using Parts 1 to 15.  Route: V0  *)
(* is the complement of four closed sets that miss k: the image of the part  *)
(* of std_triangle where the first model coordinate lies outside the two     *)
(* open bands, the other double components, the image of the middle segment  *)
(* at first coordinate 3/2, and complex_boundary c minus w.                  *)
(* ------------------------------------------------------------------------- *)

(* Copy of MOI_FCL_CB_CLOSED (pc_moi_fnd_collar.ml), which is not in the     *)
(* load closure of pc_moi_lt_seam; proof unchanged.                          *)

let MOI_LSMCV_CB_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c ==> closed (complex_boundary c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_boundary] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o
      GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CLOSED]]);;

let MOI_LSMCV_BANDS_OPEN = prove
 (`open {z:real^2 | (&1 / &2 < z$1 /\ z$1 < &3 / &2) \/
                    (&3 / &2 < z$1 /\ z$1 < &5 / &2)}`,
  SUBGOAL_THEN
   `{z:real^2 | (&1 / &2 < z$1 /\ z$1 < &3 / &2) \/ (&3 / &2 < z$1 /\ z$1 < &5 / &2)} =
    ({z | z$1 > &1 / &2} INTER {z | z$1 < &3 / &2}) UNION
    ({z | z$1 > &3 / &2} INTER {z | z$1 < &5 / &2})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_UNION THEN CONJ_TAC THEN MATCH_MP_TAC OPEN_INTER THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT]);;

let MOI_LSMCV_IMAGE_CLOSED = prove
 (`!(f:real^2->real^N) (h:real^2->real^2) s t.
     compact s /\ f continuous_on s /\ h continuous_on s /\ closed t
     ==> closed (IMAGE f {x | x IN s /\ h x IN t})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE]]);;

let MOI_LSMCV_MID_SEG = prove
 (`!z:real^2. z IN segment[vector[&3 / &2; &0],vector[&3 / &2; &1]]
              ==> z$1 = &3 / &2 /\ z IN moi_lcus_mr`,
  GEN_TAC THEN REWRITE_TAC[IN_SEGMENT; moi_lcus_mr; IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2; VEC_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LSMCV_ASSEMBLE = prove
 (`!(k:real^N->bool) C1 C2 C3 cb w.
     closed C1 /\ closed C2 /\ closed C3 /\ closed (cb DIFF w) /\
     DISJOINT k C1 /\ DISJOINT k C2 /\ DISJOINT k C3 /\ k INTER cb SUBSET w
     ==> open ((:real^N) DIFF (C1 UNION C2 UNION C3 UNION (cb DIFF w))) /\
         k SUBSET (:real^N) DIFF (C1 UNION C2 UNION C3 UNION (cb DIFF w)) /\
         DISJOINT ((:real^N) DIFF (C1 UNION C2 UNION C3 UNION (cb DIFF w))) C2 /\
         DISJOINT ((:real^N) DIFF (C1 UNION C2 UNION C3 UNION (cb DIFF w))) C3 /\
         ((:real^N) DIFF (C1 UNION C2 UNION C3 UNION (cb DIFF w))) INTER cb SUBSET w /\
         (!y. y IN (:real^N) DIFF (C1 UNION C2 UNION C3 UNION (cb DIFF w))
              ==> ~(y IN C1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; CLOSED_UNION];
    ASM SET_TAC[]]);;

(* The open neighbourhood V0 of k. *)

let MOI_LSM_V0 = prove
 (MOI_LSM_V0_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LSM_DI_REST_CLOSED) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lsm_setup]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nd") (CONJUNCTS_THEN2 (LABEL_TAC "ph")
    (CONJUNCTS_THEN2 (LABEL_TAC "gm") (CONJUNCTS_THEN2 (LABEL_TAC "gt")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "kc")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fk") (K ALL_TAC))))))))) THEN
  USE_THEN "nd" (MP_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC o MATCH_MP MOI_LT2D_NORMAL2_IMP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sd") (CONJUNCTS_THEN2 (LABEL_TAC "fc")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "dii"))))) THEN
  SUBGOAL_THEN
   `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
    relative_frontier std_triangle`
  (LABEL_TAC "bd") THENL
   [USE_THEN "sd" (MP_TAC o GEN_REWRITE_RULE I [moi_lt_singular_disk]) THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "ph" (STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  SUBGOAL_THEN
   `closed (IMAGE (f:real^2->real^N)
             {x | x IN std_triangle /\
                  (g':real^2->real^2) x IN
                  (:real^2) DIFF {z:real^2 | (&1 / &2 < z$1 /\ z$1 < &3 / &2) \/
                                             (&3 / &2 < z$1 /\ z$1 < &5 / &2)}})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LSMCV_IMAGE_CLOSED THEN
    ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC; GSYM OPEN_CLOSED; MOI_LSMCV_BANDS_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (IMAGE ((f:real^2->real^N) o (g:real^2->real^2))
                  (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]]))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_SEGMENT] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
     [EXISTS_TAC `moi_lcus_mr` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[MOI_LSMCV_MID_SEG];
      EXISTS_TAC `std_triangle:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `z:real^2` THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_LSMCV_MID_SEG) THEN
      STRIP_TAC THEN
      USE_THEN "gm" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^2) IN moi_lcus_mr`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (complex_boundary (c:(real^N->bool)->bool) DIFF w)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL];
      MATCH_MP_TAC MOI_LSMCV_CB_CLOSED THEN
      ASM_MESON_TAC[combinatorial_manifold_with_boundary]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (k:real^N->bool)
      (IMAGE (f:real^2->real^N)
         {x | x IN std_triangle /\
              (g':real^2->real^2) x IN
              (:real^2) DIFF {z:real^2 | (&1 / &2 < z$1 /\ z$1 < &3 / &2) \/
                                         (&3 / &2 < z$1 /\ z$1 < &5 / &2)}})`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT (k:real^N->bool) (IMAGE (f:real^2->real^N) s) <=>
                          !x. x IN s ==> ~(f x IN k)`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    USE_THEN "gt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^2) IN std_triangle`))) THEN
    STRIP_TAC THEN
    USE_THEN "fk" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `(g':real^2->real^2) x IN moi_lcus_mr`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (k:real^N->bool)
      (IMAGE ((f:real^2->real^N) o (g:real^2->real^2))
             (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]]))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT (k:real^N->bool) (IMAGE (f:real^2->real^N) s) <=>
                          !x. x IN s ==> ~(f x IN k)`; o_THM] THEN
    X_GEN_TAC `z:real^2` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_LSMCV_MID_SEG) THEN
    USE_THEN "fk" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^2) IN moi_lcus_mr`))) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) INTER complex_boundary c SUBSET w` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` ASSUME_TAC THENL
     [USE_THEN "kc" (fun th -> MP_TAC(MATCH_MP IN_COMPONENTS_SUBSET th)) THEN
      UNDISCH_TAC `(y:real^N) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "dii" (fun th ->
      MP_TAC(CONJUNCT1(MATCH_MP th (ASSUME `(y:real^N) IN moi_lt_double_image f`)))) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^2) IN relative_frontier std_triangle` ASSUME_TAC THENL
     [USE_THEN "bd" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET w` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `(:real^N) DIFF
    (IMAGE (f:real^2->real^N)
       {x | x IN std_triangle /\
            (g':real^2->real^2) x IN
            (:real^2) DIFF {z:real^2 | (&1 / &2 < z$1 /\ z$1 < &3 / &2) \/
                                       (&3 / &2 < z$1 /\ z$1 < &5 / &2)}} UNION
     (moi_lt_double_image f DIFF k) UNION
     IMAGE (f o (g:real^2->real^2)) (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]]) UNION
     (complex_boundary (c:(real^N->bool)->bool) DIFF w))` THEN
  MP_TAC(ISPECL
   [`k:real^N->bool`;
    `IMAGE (f:real^2->real^N)
       {x | x IN std_triangle /\
            (g':real^2->real^2) x IN
            (:real^2) DIFF {z:real^2 | (&1 / &2 < z$1 /\ z$1 < &3 / &2) \/
                                       (&3 / &2 < z$1 /\ z$1 < &5 / &2)}}`;
    `moi_lt_double_image (f:real^2->real^N) DIFF k`;
    `IMAGE ((f:real^2->real^N) o (g:real^2->real^2))
           (segment[vector[&3 / &2; &0],vector[&3 / &2; &1]])`;
    `complex_boundary (c:(real^N->bool)->bool)`; `w:real^N->bool`] MOI_LSMCV_ASSEMBLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~((f:real^2->real^N) x IN
      IMAGE f {x | x IN std_triangle /\
                   (g':real^2->real^2) x IN
                   (:real^2) DIFF {z:real^2 | (&1 / &2 < z$1 /\ z$1 < &3 / &2) \/
                                              (&3 / &2 < z$1 /\ z$1 < &5 / &2)}})`
  MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_UNIV; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 25: the push and the seam.  The double arc k of the statement is the *)
(* one of the model (two components with the same nonempty preimage meet);   *)
(* the setup holds for it; MOI_LSM_V0 gives the neighbourhood V0 and         *)
(* MOI_LSM_PUSH_CORE the push.  Then SEAM : |- MOI_LCUS_SEAM by              *)
(* MOI_LSM_SEAM_FROM_PUSH (Part 15).                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_LSM_PUSH_THM = prove
 (MOI_LSM_PUSH,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`;
                       `g:real^2->real^2`; `e:bool`; `k:real^N->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LSM_MODEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k':real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `k':real^N->bool = k` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`; `k':real^N->bool`;
                   `k:real^N->bool`] COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~q ==> (q <=> ~p) ==> p`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(f:real^2->real^N) ((g:real^2->real^2) (vector[&1; &0]))` THEN
    SUBGOAL_THEN `(g:real^2->real^2) (vector[&1; &0]) IN
                  IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
                           segment[vector[&2; &0],vector[&2; &1]])` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(g:real^2->real^2) (vector[&1; &0]) IN
                   IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
                            segment[vector[&2; &0],vector[&2; &1]])` THEN
      UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k'} =
                   IMAGE (g:real^2->real^2) (segment[vector[&1; &0],vector[&1; &1]] UNION
                            segment[vector[&2; &0],vector[&2; &1]])` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[IN_ELIM_THM];
      UNDISCH_TAC `(g:real^2->real^2) (vector[&1; &0]) IN
                   IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
                            segment[vector[&2; &0],vector[&2; &1]])` THEN
      UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} =
                   IMAGE (g:real^2->real^2) (segment[vector[&1; &0],vector[&1; &1]] UNION
                            segment[vector[&2; &0],vector[&2; &1]])` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lsm_setup c (f:real^2->real^N) g g' e k` ASSUME_TAC THENL
   [REWRITE_TAC[moi_lsm_setup] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`;
                 `g':real^2->real^2`; `e:bool`; `k:real^N->bool`; `w:real^N->bool`]
    MOI_LSM_V0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_LSM_PUSH_CORE THEN
  MAP_EVERY EXISTS_TAC [`g':real^2->real^2`; `e:bool`; `V0:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  REWRITE_TAC[moi_lsm_a1; moi_lsm_a2; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SEAM = prove
 (MOI_LCUS_SEAM,
  MATCH_MP_TAC MOI_LSM_SEAM_FROM_PUSH THEN ACCEPT_TAC MOI_LSM_PUSH_THM);;

