(* ========================================================================= *)
(* pc_moi_lt_gpa: the simplicial step of general position for the loop       *)
(* theorem.  Main theorem GP_SIMPLICIAL (MOI_LT_GP_SIMPLICIAL of             *)
(* pc_moi_loop_stmt.ml, Moise p.184): a PL singular disk becomes simplicial  *)
(* after subdividing source and target.  The companion statement             *)
(* MANIFOLD_CHARTS is proved in pc_moi_lt_charts.ml.                         *)
(* Route: f is affine on the simplices of a triangulation k1 of the         *)
(* triangle, hence injective on each (local injectivity); the images are    *)
(* simplices; a common subdivision t of c by the images pulls back simplex  *)
(* by simplex (MOI_LGA_PULLBACK_COMPLEX, generic in the dimensions).        *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Affine maps injective on a simplex (images of simplices and              *)
(* of their faces), and local injectivity of an affine map on a convex set. *)
(* ========================================================================= *)

(* An affine map that is locally injective at the points of a convex set s  *)
(* (relative to an ambient set u containing s) is injective on s.           *)

let MOI_LGA_AFFINE_LOCAL_INJ = prove
 (`!(f:real^M->real^N) l b s u.
     linear l /\ convex s /\ s SUBSET u /\ (!x. x IN s ==> f x = l x + b) /\
     (!x. x IN s
          ==> ?n. open n /\ x IN n /\
                  !y z. y IN n INTER u /\ z IN n INTER u /\ f y = f z ==> y = z)
     ==> !x x'. x IN s /\ x' IN s /\ f x = f x' ==> x = x'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff") (LABEL_TAC "loc"))))) THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^M = x'` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `segment[x:real^M,x'] SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^M->real^N) x' = l x` ASSUME_TAC THENL
   [USE_THEN "aff" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^M) IN s`)) THEN
                              MP_TAC(MATCH_MP th (ASSUME `(x':real^M) IN s`))) THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> concl th =
      `(f:real^M->real^N) x = f x'`)) THEN
    CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^M. p IN segment[x,x'] ==> (f:real^M->real^N) p = f x`
  (LABEL_TAC "cst") THENL
   [X_GEN_TAC `p:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(p:real^M) IN segment[x,x']` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "aff" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(p:real^M) IN s`)]) THEN
    USE_THEN "aff" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^M) IN s`)]) THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(x:real^M,x') IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[MIDPOINT_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPEC `midpoint(x:real^M,x')`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `midpoint(x:real^M,x') limit_point_of segment[x,x']` MP_TAC THENL
   [SIMP_TAC[LIMPT_OF_CONVEX; CONVEX_SEGMENT; MIDPOINT_IN_SEGMENT] THEN
    REWRITE_TAC[EXTENSION; IN_SING] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT; MIDPOINT_EQ_ENDPOINT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[limit_point_of] THEN DISCH_THEN(MP_TAC o SPEC `n:real^M->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p:real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^M`; `midpoint(x:real^M,x')`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:real^M) IN u /\ midpoint(x:real^M,x') IN u` (fun th -> REWRITE_TAC[th])
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "cst" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(p:real^M) IN segment[x,x']`);
      MATCH_MP th (ISPECL [`x:real^M`; `x':real^M`] (CONJUNCT1 MIDPOINT_IN_SEGMENT))]);
    ASM_REWRITE_TAC[]]);;

(* Affine maps commute with convex hulls. *)

let MOI_LGA_HULL_IMAGE = prove
 (`!(f:real^M->real^N) l b v.
     linear l /\ (!x. x IN convex hull v ==> f x = l x + b)
     ==> IMAGE f (convex hull v) = convex hull (IMAGE f v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (f:real^M->real^N) (convex hull v) =
    IMAGE (\x. b + x) (IMAGE (l:real^M->real^N) (convex hull v)) /\
    IMAGE (f:real^M->real^N) v = IMAGE (\x. b + x) (IMAGE (l:real^M->real^N) v)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^M. x IN s ==> (f:real^M->real^N) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[HULL_INC] THEN REWRITE_TAC[VECTOR_ADD_SYM];
    ASM_SIMP_TAC[CONVEX_HULL_TRANSLATION; CONVEX_HULL_LINEAR_IMAGE]]);;

(* An affine map injective on a simplex keeps its vertices independent.     *)

let MOI_LGA_INDEP_IMAGE = prove
 (`!(f:real^M->real^N) l b v.
     linear l /\ ~affine_dependent v /\ (!x. x IN convex hull v ==> f x = l x + b) /\
     (!x y. x IN convex hull v /\ y IN convex hull v /\ f x = f y ==> x = y)
     ==> ~affine_dependent (IMAGE f v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `b:real^N`; `convex hull v:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `b':real^M`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `!x. x IN v ==> b' + (l':real^N->real^M) ((f:real^M->real^N) x) = x`
  (LABEL_TAC "inv") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN convex hull v` ASSUME_TAC THENL
     [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~affine_dependent (v:real^M->bool)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `v = IMAGE (\z. b' + z) (IMAGE (l':real^N->real^M) (IMAGE (f:real^M->real^N) v))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[AFFINE_DEPENDENT_TRANSLATION_EQ] THEN
  MATCH_MP_TAC AFFINE_DEPENDENT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  DISCH_TAC THEN SUBGOAL_THEN `x:real^M = y` (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "inv" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^M) IN v`)) THEN
                            MP_TAC(MATCH_MP th (ASSUME `(y:real^M) IN v`))) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The image of an n-simplex under an affine map injective on it.            *)

let MOI_LGA_SIMPLEX_IMAGE = prove
 (`!n (f:real^M->real^N) l b s.
     n simplex s /\ linear l /\ (!x. x IN s ==> f x = l x + b) /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> n simplex (IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `IMAGE (f:real^M->real^N) v` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGA_INDEP_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `n:int`)) (concl th))) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[HULL_INC];
    MATCH_MP_TAC MOI_LGA_HULL_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[]]);;

(* The faces of the image are the images of the faces.                       *)

let MOI_LGA_FACES_IMAGE = prove
 (`!n (f:real^M->real^N) l b s.
     n simplex s /\ linear l /\ (!x. x IN s ==> f x = l x + b) /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> !d. d face_of (IMAGE f s) <=> ?e. e face_of s /\ d = IMAGE f e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `!c. c SUBSET v
        ==> IMAGE (f:real^M->real^N) (convex hull c) = convex hull (IMAGE f c)`
  (LABEL_TAC "hi") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGA_HULL_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[HULL_MONO; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent (IMAGE (f:real^M->real^N) v)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGA_INDEP_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "hi" (fun th -> REWRITE_TAC[MATCH_MP th (ISPEC `v:real^M->bool` SUBSET_REFL)]) THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  X_GEN_TAC `d:real^N->bool` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull {x | x IN v /\ (f:real^M->real^N) x IN w}` THEN CONJ_TAC THENL
     [EXISTS_TAC `{x | x IN v /\ (f:real^M->real^N) x IN w}` THEN SET_TAC[]; ALL_TAC] THEN
    USE_THEN "hi" (fun th -> REWRITE_TAC[MATCH_MP th
      (SET_RULE `{x | x IN v /\ (f:real^M->real^N) x IN w} SUBSET v`)]) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `(w:real^N->bool) SUBSET IMAGE (f:real^M->real^N) v` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e:real^M->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) SUBST1_TAC)) THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) c` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET]]);;

(* The pullback of a piece r of the image of s.                               *)

let MOI_LGA_PULL_PIECE = prove
 (`!(f:real^M->real^N) (g:real^N->real^M) s r.
     (!x. x IN s ==> g (f x) = x) /\ r SUBSET IMAGE f s
     ==> {x | x IN s /\ f x IN r} = IMAGE g r /\
         IMAGE f {x | x IN s /\ f x IN r} = r /\
         (!z. z IN r ==> f (g z) = z /\ g z IN s)`,
  REWRITE_TAC[EXTENSION; SUBSET; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Pulling back a triangulation of the images through a map                 *)
(* that is affine and injective on each simplex of a complex k.             *)
(* ========================================================================= *)

(* An affine map injective on a convex set has a global affine left inverse *)
(* on it.                                                                    *)

let MOI_LGA_LEFT_INVERSE = prove
 (`!(f:real^M->real^N) l b s.
     convex s /\ linear l /\ (!x. x IN s ==> f x = l x + b) /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> ?(g:real^N->real^M) l' b'. linear l' /\ (!z. g z = l' z + b') /\
                                    (!x. x IN s ==> g (f x) = x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `b:real^N`; `s:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `b':real^M`
      STRIP_ASSUME_TAC))] THEN
  MAP_EVERY EXISTS_TAC [`\z:real^N. (l':real^N->real^M) z + b'`; `l':real^N->real^M`;
                        `b':real^M`] THEN
  ASM_SIMP_TAC[]);;

(* The pullback of a simplex r inside the image of s is a simplex, and its   *)
(* faces are the pullbacks of the faces of r.                                *)

let MOI_LGA_PULL_SIMPLEX = prove
 (`!(f:real^M->real^N) l b s m r.
     convex s /\ linear l /\ (!x. x IN s ==> f x = l x + b) /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     m simplex r /\ r SUBSET IMAGE f s
     ==> m simplex {x | x IN s /\ f x IN r} /\
         !d. d face_of {x | x IN s /\ f x IN r} <=>
             ?e. e face_of r /\ d = {x | x IN s /\ f x IN e}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `b:real^N`; `s:real^M->bool`]
    MOI_LGA_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` (X_CHOOSE_THEN `l':real^N->real^M`
    (X_CHOOSE_THEN `b':real^M` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!e. e SUBSET r
        ==> {x | x IN s /\ (f:real^M->real^N) x IN e} = IMAGE (g:real^N->real^M) e`
  (LABEL_TAC "pp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`; `s:real^M->bool`;
                   `e:real^N->bool`] MOI_LGA_PULL_PIECE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN r ==> (f:real^M->real^N) ((g:real^N->real^M) z) = z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`; `s:real^M->bool`;
                   `r:real^N->bool`] MOI_LGA_PULL_PIECE) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z w. z IN r /\ w IN r /\ (g:real^N->real^M) z = g w ==> z = w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(z:real^N) IN r`))]) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP th (ASSUME `(w:real^N) IN r`))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "pp" (fun th -> REWRITE_TAC[MATCH_MP th (ISPEC `r:real^N->bool` SUBSET_REFL)]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGA_SIMPLEX_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l':real^N->real^M`; `b':real^M`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:int`; `g:real^N->real^M`; `l':real^N->real^M`; `b':real^M`;
                 `r:real^N->bool`] MOI_LGA_FACES_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  X_GEN_TAC `d:real^M->bool` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "pp" (fun th -> REWRITE_TAC[MATCH_MP th
    (MATCH_MP FACE_OF_IMP_SUBSET (ASSUME `(e:real^N->bool) face_of r`))]));;

(* The meet of two pullbacks is a face of the first: it is the s1-pullback  *)
(* of IMAGE f (s1 INTER s2) INTER (r1 INTER r2), a face of r1.              *)

let MOI_LGA_PULL_INTER = prove
 (`!(f:real^M->real^N) l b n s1 s2 m r1 r2.
     n simplex s1 /\ linear l /\ (!x. x IN s1 ==> f x = l x + b) /\
     (!x y. x IN s1 /\ y IN s1 /\ f x = f y ==> x = y) /\
     (s1 INTER s2) face_of s1 /\ m simplex r1 /\ (r1 INTER r2) face_of r1 /\
     r1 SUBSET IMAGE f s1
     ==> ({x | x IN s1 /\ f x IN r1} INTER {x | x IN s2 /\ f x IN r2}) face_of
         {x | x IN s1 /\ f x IN r1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `w = IMAGE (f:real^M->real^N) (s1 INTER s2) INTER (r1 INTER r2)` THEN
  SUBGOAL_THEN `(w:real^N->bool) face_of r1` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `r1 INTER r2:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r1 INTER r2 = IMAGE (f:real^M->real^N) s1 INTER (r1 INTER r2)`
    (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [UNDISCH_TAC `r1 SUBSET IMAGE (f:real^M->real^N) s1` THEN SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "w" THEN MATCH_MP_TAC FACE_OF_SLICE THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`n:int`; `f:real^M->real^N`; `l:real^M->real^N`; `b:real^N`;
                     `s1:real^M->bool`] MOI_LGA_FACES_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      EXISTS_TAC `s1 INTER s2:real^M->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN EXISTS_TAC `r1:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN s1 /\ (f:real^M->real^N) x IN r1} INTER {x | x IN s2 /\ f x IN r2} =
    {x | x IN s1 /\ f x IN w}`
  SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:real^M` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x':real^M` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `x:real^M = x'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `s1:real^M->bool`)) (concl th) &&
        not (can (find_term ((=) `l:real^M->real^N`)) (concl th)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `b:real^N`; `s1:real^M->bool`;
                 `m:int`; `r1:real^N->bool`] MOI_LGA_PULL_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th])] THEN
  EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* The pullback complex. *)

let moi_lga_pullback = new_definition
 `moi_lga_pullback (k:(real^M->bool)->bool) (t:(real^N->bool)->bool) (f:real^M->real^N) =
    {{x | x IN s /\ f x IN r} | s,r | s IN k /\ r IN t /\ r SUBSET IMAGE f s}`;;

let MOI_LGA_IN_PULLBACK = prove
 (`!(k:(real^M->bool)->bool) (t:(real^N->bool)->bool) (f:real^M->real^N) p.
     p IN moi_lga_pullback k t f <=>
     ?s r. s IN k /\ r IN t /\ r SUBSET IMAGE f s /\ p = {x | x IN s /\ f x IN r}`,
  REWRITE_TAC[moi_lga_pullback; IN_ELIM_THM; GSYM CONJ_ASSOC]);;

let MOI_LGA_PULLBACK_COMPLEX = prove
 (`!(k:(real^M->bool)->bool) (t:(real^N->bool)->bool) (f:real^M->real^N).
     simplicial_complex k /\ simplicial_complex t /\
     (!s. s IN k ==> ?l b. linear l /\ !x. x IN s ==> f x = l x + b) /\
     (!s x y. s IN k /\ x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     (!s. s IN k ==> ?d. d SUBSET t /\ IMAGE f s = UNIONS d)
     ==> simplicial_complex (moi_lga_pullback k t f) /\
         UNIONS (moi_lga_pullback k t f) = UNIONS k /\
         simplicial_map_on (moi_lga_pullback k t f) t f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "k") (CONJUNCTS_THEN2 (LABEL_TAC "t")
    (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (LABEL_TAC "cov"))))) THEN
  USE_THEN "k" (CONJUNCTS_THEN2 (LABEL_TAC "kfin") (CONJUNCTS_THEN2 (LABEL_TAC "ksim")
    (CONJUNCTS_THEN2 (LABEL_TAC "kface") (LABEL_TAC "kint"))) o
    GEN_REWRITE_RULE I [simplicial_complex]) THEN
  USE_THEN "t" (CONJUNCTS_THEN2 (LABEL_TAC "tfin") (CONJUNCTS_THEN2 (LABEL_TAC "tsim")
    (CONJUNCTS_THEN2 (LABEL_TAC "tface") (LABEL_TAC "tint"))) o
    GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN
   `!s r. s IN k /\ r IN t /\ r SUBSET IMAGE (f:real^M->real^N) s
          ==> (?m. m simplex {x | x IN s /\ f x IN r}) /\
              (!d. d face_of {x | x IN s /\ f x IN r} <=>
                   ?e. e face_of r /\ d = {x | x IN s /\ f x IN e})`
  (LABEL_TAC "piece") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "aff" (MP_TAC o SPEC `s:real^M->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?m. m simplex (r:real^N->bool)` (X_CHOOSE_TAC `m:int`) THENL
     [USE_THEN "tsim" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `convex (s:real^M->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN USE_THEN "ksim" MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `b:real^N`; `s:real^M->bool`;
                   `m:int`; `r:real^N->bool`] MOI_LGA_PULL_SIMPLEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s r. s IN k /\ r IN t /\ r SUBSET IMAGE (f:real^M->real^N) s
          ==> IMAGE f {x | x IN s /\ f x IN r} = r /\
              {x | x IN s /\ f x IN r} SUBSET s`
  (LABEL_TAC "img") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `r SUBSET IMAGE (f:real^M->real^N) s` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_complex] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{{x | x IN s /\ (f:real^M->real^N) x IN r} | s,r | s IN k /\ r IN t}` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`\(s:real^M->bool) (r:real^N->bool).
                          {x | x IN s /\ (f:real^M->real^N) x IN r}`;
                       `k:(real^M->bool)->bool`; `\s:real^M->bool. (t:(real^N->bool)->bool)`]
          FINITE_PRODUCT_DEPENDENT) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; MOI_LGA_IN_PULLBACK; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[MOI_LGA_IN_PULLBACK] THEN X_GEN_TAC `p:real^M->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` (X_CHOOSE_THEN `r:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "piece" (MP_TAC o SPECL [`s:real^M->bool`; `r:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REWRITE_TAC[MOI_LGA_IN_PULLBACK] THEN
      MAP_EVERY X_GEN_TAC [`d:real^M->bool`; `p:real^M->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^M->bool` (X_CHOOSE_THEN `r:real^N->bool`
        STRIP_ASSUME_TAC)) MP_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "piece" (MP_TAC o SPECL [`s:real^M->bool`; `r:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th])] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `e:real^N->bool`] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "tface" MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET];
      REWRITE_TAC[MOI_LGA_IN_PULLBACK] THEN
      SUBGOAL_THEN
       `!sa sb ra rb. sa IN k /\ sb IN k /\ ra IN t /\ rb IN t /\
                      ra SUBSET IMAGE (f:real^M->real^N) sa
                      ==> ({x | x IN sa /\ f x IN ra} INTER {x | x IN sb /\ f x IN rb}) face_of
                          {x | x IN sa /\ f x IN ra}`
      (LABEL_TAC "one") THENL
       [REPEAT STRIP_TAC THEN
        USE_THEN "aff" (MP_TAC o SPEC `sa:real^M->bool`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `b:real^N`
          STRIP_ASSUME_TAC)) THEN
        SUBGOAL_THEN `?n. n simplex (sa:real^M->bool)` (X_CHOOSE_TAC `n:int`) THENL
         [USE_THEN "ksim" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `?m. m simplex (ra:real^N->bool)` (X_CHOOSE_TAC `m:int`) THENL
         [USE_THEN "tsim" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(sa INTER sb:real^M->bool) face_of sa` ASSUME_TAC THENL
         [USE_THEN "kint" (fun th -> ACCEPT_TAC(CONJUNCT1(MATCH_MP
            (SPECL [`sa:real^M->bool`; `sb:real^M->bool`] th)
            (CONJ (ASSUME `(sa:real^M->bool) IN k`) (ASSUME `(sb:real^M->bool) IN k`)))));
          ALL_TAC] THEN
        SUBGOAL_THEN `(ra INTER rb:real^N->bool) face_of ra` ASSUME_TAC THENL
         [USE_THEN "tint" (fun th -> ACCEPT_TAC(CONJUNCT1(MATCH_MP
            (SPECL [`ra:real^N->bool`; `rb:real^N->bool`] th)
            (CONJ (ASSUME `(ra:real^N->bool) IN t`) (ASSUME `(rb:real^N->bool) IN t`)))));
          ALL_TAC] THEN
        MATCH_MP_TAC MOI_LGA_PULL_INTER THEN
        MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `b:real^N`; `n:int`; `m:int`] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
        EXISTS_TAC `sa:real^M->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`p1:real^M->bool`; `p2:real^M->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s1:real^M->bool` (X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC))
        (X_CHOOSE_THEN `s2:real^M->bool` (X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "one" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[INTER_COMM] THEN USE_THEN "one" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; MOI_LGA_IN_PULLBACK] THEN X_GEN_TAC `p:real^M->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` (X_CHOOSE_THEN `r:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^M->bool` THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(s:real^M->bool) IN k` THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; MOI_LGA_IN_PULLBACK] THEN
      X_GEN_TAC `y:real^M` THEN DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "cov" (MP_TAC o SPEC `s:real^M->bool`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?r. r IN d /\ (f:real^M->real^N) y IN r` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (f:real^M->real^N) s = UNIONS d` THEN
        UNDISCH_TAC `(y:real^M) IN s` THEN
        REWRITE_TAC[EXTENSION; IN_UNIONS; IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `{x | x IN s /\ (f:real^M->real^N) x IN r}` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[IN_ELIM_THM]] THEN
      MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `r:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(d:(real^N->bool)->bool) SUBSET t` THEN
        UNDISCH_TAC `(r:real^N->bool) IN d` THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (f:real^M->real^N) s = UNIONS d` THEN
        UNDISCH_TAC `(r:real^N->bool) IN d` THEN SET_TAC[]]];
    REWRITE_TAC[simplicial_map_on; MOI_LGA_IN_PULLBACK] THEN X_GEN_TAC `p:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` (X_CHOOSE_THEN `r:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "img" (MP_TAC o SPECL [`s:real^M->bool`; `r:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN ASM_REWRITE_TAC[];
      USE_THEN "aff" (MP_TAC o SPEC `s:real^M->bool`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^M->real^N` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
      SIMP_TAC[IN_ELIM_THM]]]);;

(* ========================================================================= *)
(* The main theorem GP_SIMPLICIAL (MOI_LT_GP_SIMPLICIAL).                    *)
(* ========================================================================= *)

let GP_SIMPLICIAL = prove
 (MOI_LT_GP_SIMPLICIAL,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`&2:int`; `std_triangle`] MOI_FMB_FACE_COMPLEX) THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{e:real^2->bool | e face_of std_triangle}`; `f:real^2->real^N`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:(real^2->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "aff"))))) THEN
  SUBGOAL_THEN `!s:real^2->bool. s IN k1 ==> s SUBSET std_triangle /\ ?n. n simplex s`
  (LABEL_TAC "ks") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplicial_complex] o check (fun th ->
        concl th = `simplicial_complex (k1:(real^2->bool)->bool)`)) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s x y. s IN k1 /\ x IN s /\ y IN s /\ (f:real^2->real^N) x = f y ==> x = y`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "aff" (MP_TAC o SPEC `s:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "ks" (MP_TAC o SPEC `s:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `n:int`)) THEN
    MP_TAC(ISPECL [`f:real^2->real^N`; `l:real^2->real^N`; `b:real^N`; `s:real^2->bool`;
                   `std_triangle`] MOI_LGA_AFFINE_LOCAL_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
        X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM SET_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^2->bool. s IN k1 ==> polytope (IMAGE (f:real^2->real^N) s) /\
                                 IMAGE f s SUBSET UNIONS c`
  (LABEL_TAC "poly") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "aff" (MP_TAC o SPEC `s:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "ks" (MP_TAC o SPEC `s:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `n:int`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `n:int` THEN
      MATCH_MP_TAC MOI_LGA_SIMPLEX_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
      EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f:real^2->real^N) std_triangle` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `IMAGE (IMAGE (f:real^2->real^N)) k1`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      MATCH_MP_TAC FINITE_IMAGE THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplicial_complex] o check (fun th ->
        concl th = `simplicial_complex (k1:(real^2->bool)->bool)`)) THEN
      SIMP_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "poly" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k1:(real^2->bool)->bool`; `t:(real^N->bool)->bool`; `f:real^2->real^N`]
    MOI_LGA_PULLBACK_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (f:real^2->real^N) s` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `IMAGE (IMAGE (f:real^2->real^N)) k1`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `moi_lga_pullback k1 t (f:real^2->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [MOI_SIMPLICIAL_COMPLEX_LF] o
    check (fun th -> concl th = `simplicial_complex (t:(real^N->bool)->bool)`)) THEN
  ASM_REWRITE_TAC[subdivides] THEN ASM_MESON_TAC[]);;

