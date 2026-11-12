(* ========================================================================= *)
(* pc_top_pi2: the second homotopy group of a pointed topological space, in *)
(* the cube model (maps of the unit square sending the boundary to the base *)
(* point, up to homotopy through such maps), as an abelian group; the       *)
(* classes of edge-constant singular 2-simplices and the homotopy addition  *)
(* theorem for edge-constant singular 3-simplices.  General topological     *)
(* spaces, HOL Light library only (metric.ml, homology.ml).  Used by        *)
(* pc_top_hurewicz (Hurewicz in degree 2).                                   *)
(*                                                                           *)
(* The square, its boundary, square maps, joins and reversal;               *)
(* continuity tools for maps given by real formulas.                         *)
(* ========================================================================= *)

needs "Multivariate/homology.ml";;

prioritize_real();;
type_invention_error := true;;

(* The unit square [0,1] x [0,1] as a topological space of pairs.          *)

let sqtop = new_definition
 `sqtop = prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                        (subtopology euclideanreal (real_interval[&0,&1]))`;;

let sqbd = new_definition
 `sqbd (x:real#real) <=> FST x = &0 \/ FST x = &1 \/ SND x = &0 \/ SND x = &1`;;

(* Square maps based at a: continuous maps of the square sending the        *)
(* boundary to a; homotopy through such maps; horizontal and vertical      *)
(* joins; horizontal reversal.                                               *)

let pi2_map = new_definition
 `pi2_map (top:A topology) a (g:real#real->A) <=>
    continuous_map (sqtop,top) g /\
    !x. x IN topspace sqtop /\ sqbd x ==> g x = a`;;

let pi2_homotopic = new_definition
 `pi2_homotopic (top:A topology) a (g:real#real->A) h <=>
    homotopic_with (\k. !x. x IN topspace sqtop /\ sqbd x ==> k x = a)
                   (sqtop,top) g h`;;

let pi2_join = new_definition
 `pi2_join (g:real#real->A) h =
    \x. if FST x <= &1 / &2 then g(&2 * FST x,SND x)
        else h(&2 * FST x - &1,SND x)`;;

let pi2_vjoin = new_definition
 `pi2_vjoin (g:real#real->A) h =
    \x. if SND x <= &1 / &2 then g(FST x,&2 * SND x)
        else h(FST x,&2 * SND x - &1)`;;

let pi2_reverse = new_definition
 `pi2_reverse (g:real#real->A) = \x. g(&1 - FST x,SND x)`;;

(* ------------------------------------------------------------------------- *)
(* Basic facts about the square.                                             *)
(* ------------------------------------------------------------------------- *)

let TOPSPACE_SQTOP = prove
 (`topspace sqtop = real_interval[&0,&1] CROSS real_interval[&0,&1]`,
  REWRITE_TAC[sqtop; TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]);;

let IN_TOPSPACE_SQTOP = prove
 (`!x. x IN topspace sqtop <=>
       &0 <= FST x /\ FST x <= &1 /\ &0 <= SND x /\ SND x <= &1`,
  REWRITE_TAC[TOPSPACE_SQTOP; FORALL_PAIR_THM; IN_CROSS; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[FST; SND; CONJ_ASSOC]);;

let SQTOP_SUBTOPOLOGY = prove
 (`sqtop = subtopology (prod_topology euclideanreal euclideanreal)
                       (real_interval[&0,&1] CROSS real_interval[&0,&1])`,
  REWRITE_TAC[sqtop; SUBTOPOLOGY_CROSS]);;

let CONTINUOUS_MAP_SQTOP_FST = prove
 (`continuous_map (sqtop,euclideanreal) FST /\
   continuous_map (sqtop,euclideanreal) SND`,
  REWRITE_TAC[SQTOP_SUBTOPOLOGY] THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]);;

let CONTINUOUS_MAP_INTO_SQTOP = prove
 (`!top (f:A->real) g.
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g /\
        (!x. x IN topspace top
             ==> &0 <= f x /\ f x <= &1 /\ &0 <= g x /\ g x <= &1)
        ==> continuous_map (top,sqtop) (\x. f x,g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sqtop; CONTINUOUS_MAP_PAIRWISE] THEN
  REWRITE_TAC[o_DEF; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[]);;

(* A small tactic: continuity of real functions built by +, -, * and      *)
(* negation from constants and given base functions.                         *)

let RCONT_TAC ths =
  let etas = map (CONV_RULE (TRY_CONV (DEPTH_CONV ETA_CONV))) ths in
  let base = CONTINUOUS_MAP_REAL_CONST :: (ths @ etas) in
  let rec tac g =
    (FIRST (map MATCH_ACCEPT_TAC base) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN tac)) g in
  tac;;

let CONTINUOUS_MAP_SQTOP_FST_SND = prove
 (`continuous_map (sqtop,euclideanreal) (\x. FST x) /\
   continuous_map (sqtop,euclideanreal) (\x. SND x)`,
  REWRITE_TAC[ETA_AX; CONTINUOUS_MAP_SQTOP_FST]);;

let CONTINUOUS_MAP_SQTOP_SUBTOPOLOGY_FST_SND = prove
 (`!s. continuous_map (subtopology sqtop s,euclideanreal) FST /\
       continuous_map (subtopology sqtop s,euclideanreal) SND /\
       continuous_map (subtopology sqtop s,euclideanreal) (\x. FST x) /\
       continuous_map (subtopology sqtop s,euclideanreal) (\x. SND x)`,
  GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST]);;

let SQCONT = map GEN_ALL (CONJUNCTS (SPEC_ALL CONTINUOUS_MAP_SQTOP_SUBTOPOLOGY_FST_SND)) @
             CONJUNCTS CONTINUOUS_MAP_SQTOP_FST_SND @ CONJUNCTS CONTINUOUS_MAP_SQTOP_FST;;

(* Gluing two maps on the left and right halves of the square.             *)

let CONTINUOUS_MAP_PI2_JOIN = prove
 (`!top (g:real#real->A) h.
        continuous_map (sqtop,top) g /\ continuous_map (sqtop,top) h /\
        (!t. &0 <= t /\ t <= &1 ==> g(&1,t) = h(&0,t))
        ==> continuous_map (sqtop,top) (pi2_join g h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pi2_join] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
  REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST;
              CONTINUOUS_MAP_REAL_CONST] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. (g:real#real->A)(&2 * FST x,SND x)) =
                  g o (\x. &2 * FST x,SND x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
    REWRITE_TAC[CONTINUOUS_MAP_SQTOP_SUBTOPOLOGY_FST_SND] THEN
    CONJ_TAC THENL
     [RCONT_TAC SQCONT; ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SQTOP] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `(\x. (h:real#real->A)(&2 * FST x - &1,SND x)) =
                  h o (\x. &2 * FST x - &1,SND x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
    REWRITE_TAC[CONTINUOUS_MAP_SQTOP_SUBTOPOLOGY_FST_SND] THEN
    CONJ_TAC THENL
     [RCONT_TAC SQCONT; ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SQTOP] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CONTINUOUS_MAP_PI2_VJOIN = prove
 (`!top (g:real#real->A) h.
        continuous_map (sqtop,top) g /\ continuous_map (sqtop,top) h /\
        (!s. &0 <= s /\ s <= &1 ==> g(s,&1) = h(s,&0))
        ==> continuous_map (sqtop,top) (pi2_vjoin g h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pi2_vjoin] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
  REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST;
              CONTINUOUS_MAP_REAL_CONST] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. (g:real#real->A)(FST x,&2 * SND x)) =
                  g o (\x. FST x,&2 * SND x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
    REWRITE_TAC[CONTINUOUS_MAP_SQTOP_SUBTOPOLOGY_FST_SND] THEN
    CONJ_TAC THENL
     [RCONT_TAC SQCONT; ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SQTOP] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `(\x. (h:real#real->A)(FST x,&2 * SND x - &1)) =
                  h o (\x. FST x,&2 * SND x - &1)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
    REWRITE_TAC[CONTINUOUS_MAP_SQTOP_SUBTOPOLOGY_FST_SND] THEN
    CONJ_TAC THENL
     [RCONT_TAC SQCONT; ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SQTOP] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Square maps are closed under joins, reversal, reparametrization and       *)
(* continuous images; constants are square maps.                             *)
(* ------------------------------------------------------------------------- *)

let PI2_MAP_IMP_CONTINUOUS = prove
 (`!top a (g:real#real->A). pi2_map top a g ==> continuous_map (sqtop,top) g`,
  SIMP_TAC[pi2_map]);;

let PI2_MAP_BASEPOINT = prove
 (`!top a (g:real#real->A). pi2_map top a g ==> a IN topspace top`,
  REWRITE_TAC[pi2_map] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&0,&0):real#real`) THEN
  REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
    (ASSUME `continuous_map (sqtop,top) (g:real#real->A)`)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let PI2_MAP_CONST = prove
 (`!top a:A. a IN topspace top ==> pi2_map top a (\x. a)`,
  SIMP_TAC[pi2_map; CONTINUOUS_MAP_CONST]);;

let PI2_MAP_JOIN = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g /\ pi2_map top a h ==> pi2_map top a (pi2_join g h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_map] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_PI2_JOIN THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[] `x = a /\ y = a ==> (x:A) = y`) THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN REAL_ARITH_TAC;
    REWRITE_TAC[pi2_join; IN_TOPSPACE_SQTOP; sqbd] THEN
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN ASM_REAL_ARITH_TAC]);;

let PI2_MAP_VJOIN = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g /\ pi2_map top a h ==> pi2_map top a (pi2_vjoin g h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_map] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_PI2_VJOIN THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[] `x = a /\ y = a ==> (x:A) = y`) THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN REAL_ARITH_TAC;
    REWRITE_TAC[pi2_vjoin; IN_TOPSPACE_SQTOP; sqbd] THEN
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN ASM_REAL_ARITH_TAC]);;

let CONTINUOUS_MAP_SQTOP_SELF = prove
 (`!(f:real#real->real) g.
        continuous_map (sqtop,euclideanreal) f /\
        continuous_map (sqtop,euclideanreal) g /\
        (!x. x IN topspace sqtop
             ==> &0 <= f x /\ f x <= &1 /\ &0 <= g x /\ g x <= &1)
        ==> continuous_map (sqtop,sqtop) (\x. f x,g x)`,
  REWRITE_TAC[CONTINUOUS_MAP_INTO_SQTOP]);;

let PI2_MAP_REPARAM = prove
 (`!top a (g:real#real->A) phi.
        pi2_map top a g /\ continuous_map (sqtop,sqtop) phi /\
        (!x. x IN topspace sqtop /\ sqbd x ==> sqbd(phi x))
        ==> pi2_map top a (g o phi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_map] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE];
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE]]);;

let PI2_MAP_REVERSE = prove
 (`!top a (g:real#real->A). pi2_map top a g ==> pi2_map top a (pi2_reverse g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pi2_reverse (g:real#real->A) = g o (\x. &1 - FST x,SND x)`
  SUBST1_TAC THENL [REWRITE_TAC[pi2_reverse; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC PI2_MAP_REPARAM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_SQTOP_SELF THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
    CONJ_TAC THENL [RCONT_TAC SQCONT; ALL_TAC] THEN
    CONJ_TAC THENL [RCONT_TAC SQCONT; REAL_ARITH_TAC];
    REWRITE_TAC[sqbd] THEN REAL_ARITH_TAC]);;

let PI2_MAP_COMPOSE = prove
 (`!top top' a (f:A->B) g.
        pi2_map top a g /\ continuous_map (top,top') f
        ==> pi2_map top' (f a) (f o g)`,
  REWRITE_TAC[pi2_map; o_THM] THEN MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;


(* ------------------------------------------------------------------------- *)
(* Homotopies of square maps.  Equivalence, reparametrization               *)
(* by boundary-preserving homotopies of the square (straight lines between  *)
(* side-preserving maps), joins of homotopies, continuous images.           *)
(* ------------------------------------------------------------------------- *)

let PI2_HOMOTOPIC_REFL = prove
 (`!top a (g:real#real->A). pi2_homotopic top a g g <=> pi2_map top a g`,
  REWRITE_TAC[pi2_homotopic; pi2_map; HOMOTOPIC_WITH_REFL]);;

let PI2_HOMOTOPIC_SYM = prove
 (`!top a (g:real#real->A) h. pi2_homotopic top a g h <=> pi2_homotopic top a h g`,
  REWRITE_TAC[pi2_homotopic] THEN MATCH_ACCEPT_TAC HOMOTOPIC_WITH_SYM);;

let PI2_HOMOTOPIC_TRANS = prove
 (`!top a (g:real#real->A) h k.
        pi2_homotopic top a g h /\ pi2_homotopic top a h k
        ==> pi2_homotopic top a g k`,
  REWRITE_TAC[pi2_homotopic] THEN MESON_TAC[HOMOTOPIC_WITH_TRANS]);;

let PI2_HOMOTOPIC_IMP_MAP = prove
 (`!top a (g:real#real->A) h.
        pi2_homotopic top a g h ==> pi2_map top a g /\ pi2_map top a h`,
  REWRITE_TAC[pi2_homotopic; pi2_map] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  SIMP_TAC[]);;

(* The domain of homotopies of square maps.                                *)

let CONTINUOUS_MAP_HSQ_BASE = prove
 (`continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                 sqtop,euclideanreal) (\z. FST z) /\
   continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                 sqtop,euclideanreal) (\z. FST(SND z)) /\
   continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                 sqtop,euclideanreal) (\z. SND(SND z))`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
    SUBGOAL_THEN `(\z:real#real#real. FST(SND z)) = FST o SND` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    REWRITE_TAC[CONTINUOUS_MAP_SND; CONTINUOUS_MAP_SQTOP_FST];
    SUBGOAL_THEN `(\z:real#real#real. SND(SND z)) = SND o SND` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    REWRITE_TAC[CONTINUOUS_MAP_SND; CONTINUOUS_MAP_SQTOP_FST]]);;

let IN_TOPSPACE_HSQ = prove
 (`!z. z IN topspace (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                    sqtop) <=>
       &0 <= FST z /\ FST z <= &1 /\ SND z IN topspace sqtop`,
  REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[FST; SND; CONJ_ASSOC]);;

(* Reparametrization: a homotopy of the square through maps sending the    *)
(* boundary into the boundary gives a homotopy of square maps.             *)

let PI2_HOMOTOPIC_REPARAM = prove
 (`!top a (g:real#real->A) phi psi.
        pi2_map top a g /\
        homotopic_with (\k. !x. x IN topspace sqtop /\ sqbd x
                                ==> k x IN topspace sqtop /\ sqbd(k x))
                       (sqtop,sqtop) phi psi
        ==> pi2_homotopic top a (g o phi) (g o psi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_homotopic; pi2_map] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT THEN
  EXISTS_TAC `\k:real#real->real#real.
                !x. x IN topspace sqtop /\ sqbd x
                    ==> k x IN topspace sqtop /\ sqbd(k x)` THEN
  EXISTS_TAC `sqtop` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real#real->real#real` THEN REWRITE_TAC[o_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let ATOP_CONVEX_UNIT = prove
 (`!l a b. &0 <= l /\ l <= &1 /\ &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1
           ==> &0 <= (&1 - l) * a + l * b /\ (&1 - l) * a + l * b <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - l) * a /\ (&1 - l) * a <= (&1 - l) /\
                &0 <= l * b /\ l * b <= l`
  MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let CONTINUOUS_MAP_HSQ_COMPONENTS = prove
 (`!phi. continuous_map (sqtop,sqtop) phi
         ==> continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                           sqtop,euclideanreal) (\z. FST(phi(SND z))) /\
             continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                           sqtop,euclideanreal) (\z. SND(phi(SND z)))`,
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(\z:real#real#real. FST((phi:real#real->real#real)(SND z))) =
                  FST o phi o SND` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC];
    SUBGOAL_THEN `(\z:real#real#real. SND((phi:real#real->real#real)(SND z))) =
                  SND o phi o SND` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC]] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
  REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_SND]);;

(* Two side-preserving self-maps of the square are homotopic through maps  *)
(* of pairs (straight-line homotopy).                                       *)

let PI2_SIDE_HOMOTOPIC = prove
 (`!phi psi.
        continuous_map (sqtop,sqtop) phi /\ continuous_map (sqtop,sqtop) psi /\
        (!x. x IN topspace sqtop
             ==> (FST x = &0 ==> FST(phi x) = &0 /\ FST(psi x) = &0) /\
                 (FST x = &1 ==> FST(phi x) = &1 /\ FST(psi x) = &1) /\
                 (SND x = &0 ==> SND(phi x) = &0 /\ SND(psi x) = &0) /\
                 (SND x = &1 ==> SND(phi x) = &1 /\ SND(psi x) = &1))
        ==> homotopic_with (\k. !x. x IN topspace sqtop /\ sqbd x
                                    ==> k x IN topspace sqtop /\ sqbd(k x))
                           (sqtop,sqtop) phi psi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "side"))) THEN
  REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC
   `\z:real#real#real.
      ((&1 - FST z) * FST((phi:real#real->real#real)(SND z)) +
       FST z * FST((psi:real#real->real#real)(SND z)),
       (&1 - FST z) * SND(phi(SND z)) + FST z * SND(psi(SND z)))` THEN
  SUBGOAL_THEN
   `!x. x IN topspace sqtop
        ==> (phi:real#real->real#real) x IN topspace sqtop /\
            (psi:real#real->real#real) x IN topspace sqtop`
  MP_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
        (ASSUME `continuous_map (sqtop,sqtop) (phi:real#real->real#real)`));
      MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
        (ASSUME `continuous_map (sqtop,sqtop) (psi:real#real->real#real)`))] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "range")] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID;
              REAL_SUB_REFL; REAL_ADD_LID; PAIR] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
    MP_TAC(SPEC `phi:real#real->real#real` CONTINUOUS_MAP_HSQ_COMPONENTS) THEN
    MP_TAC(SPEC `psi:real#real->real#real` CONTINUOUS_MAP_HSQ_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
      let ths = CONJUNCTS CONTINUOUS_MAP_HSQ_BASE @ CONJUNCTS th1 @ CONJUNCTS th2 in
      CONJ_TAC THENL [RCONT_TAC ths; CONJ_TAC THENL [RCONT_TAC ths; ALL_TAC]])) THEN
    REWRITE_TAC[IN_TOPSPACE_HSQ] THEN X_GEN_TAC `z:real#real#real` THEN STRIP_TAC THEN
    REMOVE_THEN "range" (MP_TAC o SPEC `SND(z:real#real#real)`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(a /\ b) /\ (c /\ d) ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THEN MATCH_MP_TAC ATOP_CONVEX_UNIT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN
    REMOVE_THEN "range" (MP_TAC o SPEC `x:real#real`) THEN
    REMOVE_THEN "side" (MP_TAC o SPEC `x:real#real`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
    STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
      MATCH_MP_TAC(TAUT `(a /\ b) /\ (c /\ d) ==> a /\ b /\ c /\ d`) THEN
      CONJ_TAC THEN MATCH_MP_TAC ATOP_CONVEX_UNIT THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `sqbd(x:real#real)` THEN REWRITE_TAC[sqbd] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]]);;

(* Joins of homotopies.                                                     *)

let CONTINUOUS_MAP_HSQ_SUBTOPOLOGY_BASE = prove
 (`!s. continuous_map
         (subtopology (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                     sqtop) s,euclideanreal) (\z. FST z) /\
       continuous_map
         (subtopology (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                     sqtop) s,euclideanreal) (\z. FST(SND z)) /\
       continuous_map
         (subtopology (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                     sqtop) s,euclideanreal) (\z. SND(SND z))`,
  GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_HSQ_BASE]);;

let HSQCONT = map GEN_ALL (CONJUNCTS (SPEC_ALL CONTINUOUS_MAP_HSQ_SUBTOPOLOGY_BASE)) @
              CONJUNCTS CONTINUOUS_MAP_HSQ_BASE;;

let CONTINUOUS_MAP_INTO_HSQ = prove
 (`!top (l:A->real) f g.
        continuous_map (top,euclideanreal) l /\
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g /\
        (!x. x IN topspace top
             ==> &0 <= l x /\ l x <= &1 /\
                 &0 <= f x /\ f x <= &1 /\ &0 <= g x /\ g x <= &1)
        ==> continuous_map
              (top,prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                 sqtop) (\x. l x,(f x,g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN ASM_SIMP_TAC[]]);;

let PI2_HOMOTOPIC_JOIN = prove
 (`!top a (g:real#real->A) g' h h'.
        pi2_homotopic top a g g' /\ pi2_homotopic top a h h'
        ==> pi2_homotopic top a (pi2_join g h) (pi2_join g' h')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_homotopic; homotopic_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `G:real#real#real->A` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G")))))
    (X_CHOOSE_THEN `H:real#real#real->A` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")))))) THEN
  EXISTS_TAC `\z. if FST(SND z) <= &1 / &2
                  then (G:real#real#real->A)(FST z,&2 * FST(SND z),SND(SND z))
                  else (H:real#real#real->A)(FST z,&2 * FST(SND z) - &1,SND(SND z))` THEN
  ASM_REWRITE_TAC[pi2_join] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
    REWRITE_TAC[CONTINUOUS_MAP_HSQ_BASE; CONTINUOUS_MAP_REAL_CONST] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\z. (G:real#real#real->A)(FST z,&2 * FST(SND z),SND(SND z))) =
                    G o (\z. FST z,(&2 * FST(SND z),SND(SND z)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[&0,&1])) sqtop` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_HSQ THEN
      REPEAT CONJ_TAC THEN TRY(RCONT_TAC HSQCONT) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; IN_TOPSPACE_HSQ;
                  IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `(\z. (H:real#real#real->A)(FST z,&2 * FST(SND z) - &1,SND(SND z))) =
                    H o (\z. FST z,(&2 * FST(SND z) - &1,SND(SND z)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[&0,&1])) sqtop` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_HSQ THEN
      REPEAT CONJ_TAC THEN TRY(RCONT_TAC HSQCONT) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; IN_TOPSPACE_HSQ;
                  IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_TOPSPACE_HSQ; IN_TOPSPACE_SQTOP] THEN
      X_GEN_TAC `z:real#real#real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC(MESON[] `x = a /\ y = a ==> (x:A) = y`) THEN CONJ_TAC THENL
       [USE_THEN "G" (MP_TAC o SPEC `FST(z:real#real#real)`);
        USE_THEN "H" (MP_TAC o SPEC `FST(z:real#real#real)`)] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN MATCH_MP_TAC]) THEN
      REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN X_GEN_TAC `x:real#real` THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN STRIP_TAC THEN
    REMOVE_THEN "G" (MP_TAC o SPEC `t:real`) THEN
    REMOVE_THEN "H" (MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
    UNDISCH_TAC `sqbd(x:real#real)` THEN REWRITE_TAC[sqbd] THEN
    ASM_REAL_ARITH_TAC]);;

(* Composition of homotopies with self-maps of the square (on the right)   *)
(* and with continuous maps of spaces (on the left).                        *)

let PI2_HOMOTOPIC_COMPOSE_RIGHT = prove
 (`!top a (g:real#real->A) h phi.
        pi2_homotopic top a g h /\ continuous_map (sqtop,sqtop) phi /\
        (!x. x IN topspace sqtop /\ sqbd x ==> sqbd(phi x))
        ==> pi2_homotopic top a (g o phi) (h o phi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_homotopic; homotopic_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `G:real#real#real->A` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G")))))
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z. (G:real#real#real->A)(FST z,(phi:real#real->real#real)(SND z))` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\z. (G:real#real#real->A)(FST z,(phi:real#real->real#real)(SND z))) =
                  G o (\z. FST z,phi(SND z))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[&0,&1])) sqtop` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX] THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST] THEN
    SUBGOAL_THEN `(\z:real#real#real. (phi:real#real->real#real)(SND z)) = phi o SND`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN
    REMOVE_THEN "G" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE]]);;

let PI2_HOMOTOPIC_COMPOSE_LEFT = prove
 (`!top top' a (f:A->B) g h.
        pi2_homotopic top a g h /\ continuous_map (top,top') f
        ==> pi2_homotopic top' (f a) (f o g) (f o h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_homotopic] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT THEN
  EXISTS_TAC `\k:real#real->A. !x. x IN topspace sqtop /\ sqbd x ==> k x = a` THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[o_THM] THEN MESON_TAC[]);;

(* The swap of coordinates exchanges horizontal and vertical joins.         *)

let pi2_swap = new_definition
 `pi2_swap (x:real#real) = (SND x,FST x)`;;

let CONTINUOUS_MAP_PI2_SWAP = prove
 (`continuous_map (sqtop,sqtop) pi2_swap`,
  SUBGOAL_THEN `pi2_swap = \x. SND x,FST x` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pi2_swap]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
  REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST;
              IN_TOPSPACE_SQTOP] THEN
  REAL_ARITH_TAC);;

let PI2_SWAP_BOUNDARY = prove
 (`!x. x IN topspace sqtop /\ sqbd x
       ==> pi2_swap x IN topspace sqtop /\ sqbd(pi2_swap x)`,
  REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd; pi2_swap] THEN REAL_ARITH_TAC);;

let PI2_VJOIN_SWAP = prove
 (`!g h:real#real->A.
        pi2_vjoin g h = pi2_join (g o pi2_swap) (h o pi2_swap) o pi2_swap`,
  REWRITE_TAC[FUN_EQ_THM; pi2_vjoin; pi2_join; o_THM; pi2_swap]);;

let PI2_HOMOTOPIC_VJOIN = prove
 (`!top a (g:real#real->A) g' h h'.
        pi2_homotopic top a g g' /\ pi2_homotopic top a h h'
        ==> pi2_homotopic top a (pi2_vjoin g h) (pi2_vjoin g' h')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PI2_VJOIN_SWAP] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_COMPOSE_RIGHT THEN
  REWRITE_TAC[CONTINUOUS_MAP_PI2_SWAP] THEN
  SIMP_TAC[PI2_SWAP_BOUNDARY] THEN MATCH_MP_TAC PI2_HOMOTOPIC_JOIN THEN
  CONJ_TAC THEN MATCH_MP_TAC PI2_HOMOTOPIC_COMPOSE_RIGHT THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_PI2_SWAP; PI2_SWAP_BOUNDARY]);;


(* ------------------------------------------------------------------------- *)
(* The group laws up to homotopy (units, associativity,                    *)
(* inverses, the interchange law and commutativity by Eckmann-Hilton).      *)
(* ------------------------------------------------------------------------- *)

let PI2_HOMOTOPIC_EQ = prove
 (`!top a (g:real#real->A) h g' h'.
        pi2_homotopic top a g h /\
        (!x. x IN topspace sqtop ==> g' x = g x /\ h' x = h x)
        ==> pi2_homotopic top a g' h'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_homotopic] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC [`g:real#real->A`; `h:real#real->A`] THEN
  ASM_SIMP_TAC[]);;

let PI2_HOMOTOPIC_REPARAM_SIDE = prove
 (`!top a (g:real#real->A) phi psi.
        pi2_map top a g /\
        continuous_map (sqtop,sqtop) phi /\ continuous_map (sqtop,sqtop) psi /\
        (!x. x IN topspace sqtop
             ==> (FST x = &0 ==> FST(phi x) = &0 /\ FST(psi x) = &0) /\
                 (FST x = &1 ==> FST(phi x) = &1 /\ FST(psi x) = &1) /\
                 (SND x = &0 ==> SND(phi x) = &0 /\ SND(psi x) = &0) /\
                 (SND x = &1 ==> SND(phi x) = &1 /\ SND(psi x) = &1))
        ==> pi2_homotopic top a (g o phi) (g o psi)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PI2_HOMOTOPIC_REPARAM THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PI2_SIDE_HOMOTOPIC THEN ASM_REWRITE_TAC[]);;

(* g is homotopic to g o phi for any side-preserving phi.                   *)

let PI2_HOMOTOPIC_SIDE_REPARAM = prove
 (`!top a (g:real#real->A) phi.
        pi2_map top a g /\ continuous_map (sqtop,sqtop) phi /\
        (!x. x IN topspace sqtop
             ==> (FST x = &0 ==> FST(phi x) = &0) /\
                 (FST x = &1 ==> FST(phi x) = &1) /\
                 (SND x = &0 ==> SND(phi x) = &0) /\
                 (SND x = &1 ==> SND(phi x) = &1))
        ==> pi2_homotopic top a g (g o phi)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `g:real#real->A`; `\x:real#real. x`;
                 `phi:real#real->real#real`] PI2_HOMOTOPIC_REPARAM_SIDE) THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_ID] THEN
  SUBGOAL_THEN `(g:real#real->A) o (\x. x) = g` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* Units.                                                                   *)

let PI2_JOIN_LUNIT = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (pi2_join (\x. a) g) g`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`g:real#real->A`; `(g:real#real->A) o (\x. max (&2 * FST x - &1) (&0),SND x)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_SIDE_REPARAM THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
      REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN RCONT_TAC SQCONT;
        REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
      REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
    REWRITE_TAC[IN_TOPSPACE_SQTOP; pi2_join; o_THM] THEN
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [pi2_map]) THEN
      DISCH_THEN(MP_TAC o SPEC `(&0,SND(x:real#real))`) THEN
      REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_REAL_ARITH_TAC;
      AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_REAL_ARITH_TAC]]);;

let PI2_CASES_TAC =
  REPEAT COND_CASES_TAC THEN
  ((AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_REAL_ARITH_TAC) ORELSE
   (MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC));;

let PI2_MAP_BOUNDARY = prove
 (`!top a (g:real#real->A) x.
        pi2_map top a g /\ x IN topspace sqtop /\ sqbd x ==> g x = a`,
  SIMP_TAC[pi2_map]);;

let PI2_JOIN_RUNIT = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (pi2_join g (\x. a)) g`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`g:real#real->A`; `(g:real#real->A) o (\x. min (&2 * FST x) (&1),SND x)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_SIDE_REPARAM THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
      REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN RCONT_TAC SQCONT;
        REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
      REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
    REWRITE_TAC[pi2_join; o_THM] THEN X_GEN_TAC `x:real#real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_TOPSPACE_SQTOP]) THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_REAL_ARITH_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PI2_MAP_BOUNDARY THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN ASM_REAL_ARITH_TAC]]);;

let PI2_JOIN_ASSOC = prove
 (`!top a (g:real#real->A) h k.
        pi2_map top a g /\ pi2_map top a h /\ pi2_map top a k
        ==> pi2_homotopic top a (pi2_join (pi2_join g h) k)
                                (pi2_join g (pi2_join h k))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`pi2_join (g:real#real->A) (pi2_join h k)`;
    `pi2_join (g:real#real->A) (pi2_join h k) o
     (\x. min (&2 * FST x) (min (FST x + &1 / &4) ((FST x + &1) / &2)),SND x)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_SIDE_REPARAM THEN
    ASM_SIMP_TAC[PI2_MAP_JOIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
      REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST] THEN
      CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN CONJ_TAC) THEN
        TRY(RCONT_TAC SQCONT) THEN
        REWRITE_TAC[real_div] THEN RCONT_TAC SQCONT;
        REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
      REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
    REWRITE_TAC[pi2_join; o_THM; IN_TOPSPACE_SQTOP] THEN
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN
    REWRITE_TAC[real_min] THEN PI2_CASES_TAC]);;

(* Inverses: g followed by its reverse contracts by folding.               *)

let PI2_JOIN_RINV = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (pi2_join g (pi2_reverse g)) (\x. a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PI2_HOMOTOPIC_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(g:real#real->A) o (\x:real#real. &1 - abs(&1 - &2 * FST x),SND x)`;
    `(g:real#real->A) o (\x:real#real. &0,SND x)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_REPARAM THEN ASM_REWRITE_TAC[homotopic_with] THEN
    EXISTS_TAC `\z:real#real#real. (&1 - FST z) * (&1 - abs(&1 - &2 * FST(SND z))),
                                   SND(SND z)` THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THEN
        TRY(RCONT_TAC HSQCONT) THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN RCONT_TAC HSQCONT;
        ALL_TAC] THEN
      CONJ_TAC THENL [RCONT_TAC HSQCONT; ALL_TAC] THEN
      REWRITE_TAC[IN_TOPSPACE_HSQ; IN_TOPSPACE_SQTOP] THEN
      X_GEN_TAC `z:real#real#real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      X_GEN_TAC `x:real#real` THEN REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RZERO] THEN TRY REAL_ARITH_TAC THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
         GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
         MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC])];
    REWRITE_TAC[pi2_join; pi2_reverse; o_THM; IN_TOPSPACE_SQTOP] THEN
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
      ASM_REAL_ARITH_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PI2_MAP_BOUNDARY THEN
      EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN ASM_REAL_ARITH_TAC]]);;

let PI2_REVERSE_REVERSE = prove
 (`!g:real#real->A. pi2_reverse(pi2_reverse g) = g`,
  REWRITE_TAC[pi2_reverse; FUN_EQ_THM; REAL_ARITH `&1 - (&1 - x) = x`]);;

let PI2_JOIN_LINV = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (pi2_join (pi2_reverse g) g) (\x. a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `pi2_reverse(g:real#real->A)`]
                PI2_JOIN_RINV) THEN
  ASM_SIMP_TAC[PI2_MAP_REVERSE; PI2_REVERSE_REVERSE]);;

(* Vertical units via the swap of coordinates.                             *)

let PI2_MAP_SWAP = prove
 (`!top a (g:real#real->A). pi2_map top a g ==> pi2_map top a (g o pi2_swap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PI2_MAP_REPARAM THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_PI2_SWAP; PI2_SWAP_BOUNDARY]);;

let PI2_HOMOTOPIC_SWAP = prove
 (`!top a (g:real#real->A) h.
        pi2_homotopic top a g h
        ==> pi2_homotopic top a (g o pi2_swap) (h o pi2_swap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PI2_HOMOTOPIC_COMPOSE_RIGHT THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_PI2_SWAP; PI2_SWAP_BOUNDARY]);;

let PI2_SWAP_SWAP = prove
 (`!g:real#real->A. (g o pi2_swap) o pi2_swap = g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; pi2_swap]);;

let PI2_CONST_SWAP = prove
 (`!a:A. (\x:real#real. a) o pi2_swap = (\x. a)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let PI2_VJOIN_LUNIT = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (pi2_vjoin (\x. a) g) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`;
                 `pi2_join (\x. a) ((g:real#real->A) o pi2_swap)`;
                 `(g:real#real->A) o pi2_swap`] PI2_HOMOTOPIC_SWAP) THEN
  ASM_SIMP_TAC[PI2_JOIN_LUNIT; PI2_MAP_SWAP] THEN
  REWRITE_TAC[PI2_VJOIN_SWAP; PI2_SWAP_SWAP; PI2_CONST_SWAP]);;

let PI2_VJOIN_RUNIT = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (pi2_vjoin g (\x. a)) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`;
                 `pi2_join ((g:real#real->A) o pi2_swap) (\x. a)`;
                 `(g:real#real->A) o pi2_swap`] PI2_HOMOTOPIC_SWAP) THEN
  ASM_SIMP_TAC[PI2_JOIN_RUNIT; PI2_MAP_SWAP] THEN
  REWRITE_TAC[PI2_VJOIN_SWAP; PI2_SWAP_SWAP; PI2_CONST_SWAP]);;

(* The interchange law and the Eckmann-Hilton argument.                     *)

let PI2_INTERCHANGE = prove
 (`!g1 g2 h1 h2:real#real->A.
        pi2_join (pi2_vjoin g1 g2) (pi2_vjoin h1 h2) =
        pi2_vjoin (pi2_join g1 h1) (pi2_join g2 h2)`,
  REWRITE_TAC[FUN_EQ_THM; pi2_join; pi2_vjoin; FST; SND] THEN
  REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let PI2_JOIN_COMM = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g /\ pi2_map top a h
        ==> pi2_homotopic top a (pi2_join g h) (pi2_join h g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[PI2_MAP_BASEPOINT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`] PI2_MAP_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
  EXISTS_TAC `pi2_join (pi2_vjoin (g:real#real->A) (\x. a)) (pi2_vjoin (\x. a) h)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_JOIN THEN ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
    ASM_SIMP_TAC[PI2_VJOIN_LUNIT; PI2_VJOIN_RUNIT];
    ALL_TAC] THEN
  REWRITE_TAC[PI2_INTERCHANGE] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
  EXISTS_TAC `pi2_vjoin (g:real#real->A) h` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_VJOIN THEN
    ASM_SIMP_TAC[PI2_JOIN_LUNIT; PI2_JOIN_RUNIT];
    ALL_TAC] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
  EXISTS_TAC `pi2_vjoin (pi2_join (\x. a) (g:real#real->A)) (pi2_join h (\x. a))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_VJOIN THEN ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
    ASM_SIMP_TAC[PI2_JOIN_LUNIT; PI2_JOIN_RUNIT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM PI2_INTERCHANGE] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_JOIN THEN
  ASM_SIMP_TAC[PI2_VJOIN_LUNIT; PI2_VJOIN_RUNIT]);;

let PI2_HOMOTOPIC_REVERSE = prove
 (`!top a (g:real#real->A) h.
        pi2_homotopic top a g h
        ==> pi2_homotopic top a (pi2_reverse g) (pi2_reverse h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k:real#real->A. pi2_reverse k = k o (\x. &1 - FST x,SND x)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pi2_reverse; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_COMPOSE_RIGHT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_SQTOP_SELF THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
    CONJ_TAC THENL [RCONT_TAC SQCONT; ALL_TAC] THEN
    CONJ_TAC THENL [RCONT_TAC SQCONT; REAL_ARITH_TAC];
    REWRITE_TAC[sqbd] THEN REAL_ARITH_TAC]);;

(* The second homotopy group as a HOL group.  When the base point is not in *)
(* the space all classes are empty and the group is trivial.               *)

let pi2_class = new_definition
 `pi2_class top a (g:real#real->A) = {h | pi2_homotopic top a g h}`;;

let pi2_group = new_definition
 `pi2_group (top:A topology,a:A) =
    group({pi2_class top a g | g | pi2_map top a g \/ g = (\x. a)},
          pi2_class top a (\x. a),
          (\c. {k | ?g. g IN c /\ pi2_homotopic top a (pi2_reverse g) k}),
          (\c d. {k | ?g h. g IN c /\ h IN d /\
                            pi2_homotopic top a (pi2_join g h) k}))`;;

let IN_PI2_CLASS = prove
 (`!top a (g:real#real->A) h. h IN pi2_class top a g <=> pi2_homotopic top a g h`,
  REWRITE_TAC[pi2_class; IN_ELIM_THM]);;

let PI2_CLASS_EQ = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g
        ==> (pi2_class top a g = pi2_class top a h <=> pi2_homotopic top a g h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_PI2_CLASS] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `g:real#real->A`) THEN
    ASM_REWRITE_TAC[PI2_HOMOTOPIC_REFL] THEN MESON_TAC[PI2_HOMOTOPIC_SYM];
    MESON_TAC[PI2_HOMOTOPIC_SYM; PI2_HOMOTOPIC_TRANS]]);;

let PI2_CLASS_EQ_EMPTY = prove
 (`!top a (g:real#real->A). pi2_class top a g = {} <=> ~pi2_map top a g`,
  REWRITE_TAC[EXTENSION; IN_PI2_CLASS; NOT_IN_EMPTY] THEN
  MESON_TAC[PI2_HOMOTOPIC_REFL; PI2_HOMOTOPIC_IMP_MAP]);;

let PI2_CLASS_INV = prove
 (`!top a (g:real#real->A).
        {k | ?g'. g' IN pi2_class top a g /\ pi2_homotopic top a (pi2_reverse g') k} =
        pi2_class top a (pi2_reverse g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_PI2_CLASS] THEN
  X_GEN_TAC `k:real#real->A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g':real#real->A` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
    EXISTS_TAC `pi2_reverse(g':real#real->A)` THEN
    ASM_SIMP_TAC[PI2_HOMOTOPIC_REVERSE];
    DISCH_TAC THEN EXISTS_TAC `g:real#real->A` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PI2_HOMOTOPIC_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP PI2_HOMOTOPIC_IMP_MAP) THEN
    MESON_TAC[PI2_MAP_REVERSE; PI2_REVERSE_REVERSE]]);;

let PI2_CLASS_MUL = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g /\ pi2_map top a h
        ==> {k | ?g' h'. g' IN pi2_class top a g /\ h' IN pi2_class top a h /\
                         pi2_homotopic top a (pi2_join g' h') k} =
            pi2_class top a (pi2_join g h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_PI2_CLASS] THEN
  X_GEN_TAC `k:real#real->A` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g':real#real->A`; `h':real#real->A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
    EXISTS_TAC `pi2_join (g':real#real->A) h'` THEN
    ASM_SIMP_TAC[PI2_HOMOTOPIC_JOIN];
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`g:real#real->A`; `h:real#real->A`] THEN
    ASM_REWRITE_TAC[PI2_HOMOTOPIC_REFL]]);;

let PI2_CLASS_IN_GSPEC = prove
 (`!top a (g:real#real->A).
        pi2_map top a g
        ==> pi2_class top a g IN {pi2_class top a h | h | pi2_map top a h}`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let PI2_GROUP_OPERATIONS = prove
 (`!top a:A.
        group_carrier(pi2_group(top,a)) =
          {pi2_class top a g | g | pi2_map top a g \/ g = (\x. a)} /\
        group_id(pi2_group(top,a)) = pi2_class top a (\x. a) /\
        group_inv(pi2_group(top,a)) =
          (\c. {k | ?g. g IN c /\ pi2_homotopic top a (pi2_reverse g) k}) /\
        group_mul(pi2_group(top,a)) =
          (\c d. {k | ?g h. g IN c /\ h IN d /\
                            pi2_homotopic top a (pi2_join g h) k})`,
  REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl pi2_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM pi2_group] THEN ANTS_TAC THENL
   [ASM_CASES_TAC `(a:A) IN topspace top` THENL
     [SUBGOAL_THEN `{pi2_class top a g | g | pi2_map top a g \/ g = (\x. a)} =
                    {pi2_class top a (g:real#real->A) | g | pi2_map top a g}`
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `c:(real#real->A)->bool` THEN EQ_TAC THENL
         [STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
           [EXISTS_TAC `g:real#real->A` THEN ASM_REWRITE_TAC[];
            EXISTS_TAC `(\x. a):real#real->A` THEN ASM_SIMP_TAC[PI2_MAP_CONST]];
          MESON_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[PI2_CLASS_INV; PI2_CLASS_MUL; PI2_MAP_JOIN; PI2_MAP_REVERSE;
                   PI2_MAP_CONST; PI2_CLASS_IN_GSPEC] THEN
      ASM_SIMP_TAC[PI2_CLASS_EQ; PI2_MAP_JOIN; PI2_MAP_REVERSE; PI2_MAP_CONST;
                   PI2_JOIN_LUNIT; PI2_JOIN_RUNIT; PI2_JOIN_LINV; PI2_JOIN_RINV] THEN
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
      ASM_SIMP_TAC[PI2_JOIN_ASSOC];
      SUBGOAL_THEN `!g:real#real->A. pi2_class top a g = {}` ASSUME_TAC THENL
       [ASM_MESON_TAC[PI2_CLASS_EQ_EMPTY; PI2_MAP_BASEPOINT]; ALL_TAC] THEN
      SUBGOAL_THEN `{pi2_class top a g | g | pi2_map top a g \/ g = (\x. a)} =
                    {{}:(real#real->A)->bool}` SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; EMPTY_GSPEC; IMP_CONJ;
                      RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2]];
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let PI2_GROUP = prove
 (`!top a:A.
        a IN topspace top
        ==> group_carrier(pi2_group(top,a)) =
              {pi2_class top a g | g | pi2_map top a g} /\
            group_id(pi2_group(top,a)) = pi2_class top a (\x. a) /\
            (!g. pi2_map top a g
                 ==> group_inv(pi2_group(top,a)) (pi2_class top a g) =
                     pi2_class top a (pi2_reverse g)) /\
            (!g h. pi2_map top a g /\ pi2_map top a h
                   ==> group_mul(pi2_group(top,a)) (pi2_class top a g)
                                                   (pi2_class top a h) =
                       pi2_class top a (pi2_join g h))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PI2_GROUP_OPERATIONS; PI2_CLASS_INV; PI2_CLASS_MUL] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `c:(real#real->A)->bool` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `g:real#real->A` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(\x. a):real#real->A` THEN ASM_SIMP_TAC[PI2_MAP_CONST]];
    MESON_TAC[]]);;

let ABELIAN_PI2_GROUP = prove
 (`!top a:A. abelian_group(pi2_group(top,a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abelian_group] THEN
  ASM_CASES_TAC `(a:A) IN topspace top` THENL
   [ASM_SIMP_TAC[PI2_GROUP; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[PI2_CLASS_EQ; PI2_MAP_JOIN; PI2_JOIN_COMM];
    SUBGOAL_THEN `!g:real#real->A. pi2_class top a g = {}` ASSUME_TAC THENL
     [ASM_MESON_TAC[PI2_CLASS_EQ_EMPTY; PI2_MAP_BASEPOINT]; ALL_TAC] THEN
    REWRITE_TAC[PI2_GROUP_OPERATIONS] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let PI2_GROUP_ID_EQ = prove
 (`!top a (g:real#real->A).
        pi2_map top a g
        ==> (pi2_class top a g = group_id(pi2_group(top,a)) <=>
             pi2_homotopic top a g (\x. a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PI2_MAP_BASEPOINT) THEN
  ASM_SIMP_TAC[PI2_GROUP; PI2_CLASS_EQ]);;

let PI2_CLASS_IN_CARRIER = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_class top a g IN group_carrier(pi2_group(top,a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PI2_MAP_BASEPOINT) THEN
  ASM_SIMP_TAC[PI2_GROUP; PI2_CLASS_IN_GSPEC]);;

let PI2_JOIN_VJOIN = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g /\ pi2_map top a h
        ==> pi2_homotopic top a (pi2_join g h) (pi2_vjoin g h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[PI2_MAP_BASEPOINT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`] PI2_MAP_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
  EXISTS_TAC `pi2_join (pi2_vjoin (g:real#real->A) (\x. a)) (pi2_vjoin (\x. a) h)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_JOIN THEN ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
    ASM_SIMP_TAC[PI2_VJOIN_LUNIT; PI2_VJOIN_RUNIT];
    ALL_TAC] THEN
  REWRITE_TAC[PI2_INTERCHANGE] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_VJOIN THEN
  ASM_SIMP_TAC[PI2_JOIN_LUNIT; PI2_JOIN_RUNIT]);;

(* ========================================================================= *)
(* Rotating a 2-cube by a quarter turn does not change its                   *)
(* class, and the diagonal swap inverts it.                                  *)
(* ========================================================================= *)

let pi2_rotate = new_definition
 `pi2_rotate (x:real#real) = (&1 - SND x,FST x)`;;

let CONTINUOUS_MAP_PI2_ROTATE = prove
 (`continuous_map (sqtop,sqtop) pi2_rotate`,
  SUBGOAL_THEN `pi2_rotate = \x. &1 - SND x,FST x` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pi2_rotate]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
  REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST; IN_TOPSPACE_SQTOP] THEN
  CONJ_TAC THENL [RCONT_TAC SQCONT; REAL_ARITH_TAC]);;

let PI2_ROTATE_BOUNDARY = prove
 (`!x. x IN topspace sqtop /\ sqbd x
       ==> pi2_rotate x IN topspace sqtop /\ sqbd(pi2_rotate x)`,
  REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd; pi2_rotate] THEN REAL_ARITH_TAC);;

let PI2_MAP_ROTATE = prove
 (`!top a (g:real#real->A). pi2_map top a g ==> pi2_map top a (g o pi2_rotate)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PI2_MAP_REPARAM THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_PI2_ROTATE; PI2_ROTATE_BOUNDARY]);;

(* Elementary estimate: a convex combination of two numbers bounded by b.    *)

let PI2_ROT_CONVEX_BOUND = prove
 (`!l r1 r2 b.
        &0 <= l /\ l <= &1 /\ abs r1 <= b /\ abs r2 <= b
        ==> abs((&1 - l) * r1 + l * r2) <= b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((&1 - l) * r1) + abs(l * r2)` THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE; REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(&1 - l) = &1 - l /\ abs l = l` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - l) * b + l * b` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* The rotation homotopy moves boundary points outside the middle square.  *)

let PI2_ROT_BOUNDARY_ARITH = prove
 (`!l x1 x2.
        &0 <= l /\ l <= &1 /\ (x1 = &0 \/ x1 = &1 \/ x2 = &0 \/ x2 = &1)
        ==> &1 / &2 + &4 * ((&1 - l) * (x1 - &1 / &2) - l * (x2 - &1 / &2)) <= &0 \/
            &1 <= &1 / &2 + &4 * ((&1 - l) * (x1 - &1 / &2) - l * (x2 - &1 / &2)) \/
            &1 / &2 + &4 * (l * (x1 - &1 / &2) + (&1 - l) * (x2 - &1 / &2)) <= &0 \/
            &1 <= &1 / &2 + &4 * (l * (x1 - &1 / &2) + (&1 - l) * (x2 - &1 / &2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
  ABBREV_TAC `r1 = (&1 - l) * (x1 - &1 / &2) - l * (x2 - &1 / &2)` THEN
  ABBREV_TAC `r2 = l * (x1 - &1 / &2) + (&1 - l) * (x2 - &1 / &2)` THEN
  MATCH_MP_TAC(TAUT `~(~p1 /\ ~p2 /\ ~p3 /\ ~p4) ==> p1 \/ p2 \/ p3 \/ p4`) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs r1 <= &1 / &8 /\ abs r2 <= &1 / &8` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (&1 - l) pow 2 + l pow 2` THEN
  SUBGOAL_THEN `&1 / &2 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    SUBGOAL_THEN `(&1 - l) pow 2 + l pow 2 = &1 / &2 + &2 * (l - &1 / &2) pow 2`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `l - &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(d * (x1 - &1 / &2)) <= &1 / &8 /\ abs(d * (x2 - &1 / &2)) <= &1 / &8`
  MP_TAC THENL
   [SUBGOAL_THEN `d * (x1 - &1 / &2) = (&1 - l) * r1 + l * r2 /\
                  d * (x2 - &1 / &2) = (&1 - l) * r2 + l * --r1`
     (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY EXPAND_TAC ["d"; "r1"; "r2"] THEN CONV_TAC REAL_RING;
      CONJ_TAC THEN MATCH_MP_TAC PI2_ROT_CONVEX_BOUND THEN
      ASM_REWRITE_TAC[REAL_ABS_NEG]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs d = d` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 * abs(x1 - &1 / &2) <= &1 / &8 /\
                &1 / &2 * abs(x2 - &1 / &2) <= &1 / &8`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `d * abs(x1 - &1 / &2)`; EXISTS_TAC `d * abs(x2 - &1 / &2)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    REMOVE_THEN "B" MP_TAC THEN REAL_ARITH_TAC]);;

(* The quarter turn: shrink into the middle square, rotate the middle square *)
(* through the scaled rotations (1 - l) I + l R, and expand again.           *)

let PI2_ROTATE_HOMOTOPIC = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (g o pi2_rotate) g`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `phi = \x:real#real. max (&0) (min (&1) (&4 * FST x - &3 / &2)),
                                  max (&0) (min (&1) (&4 * SND x - &3 / &2))` THEN
  SUBGOAL_THEN `continuous_map (sqtop,sqtop) (phi:real#real->real#real) /\
                (!x. x IN topspace sqtop
                     ==> (FST x = &0 ==> FST(phi x) = &0) /\
                         (FST x = &1 ==> FST(phi x) = &1) /\
                         (SND x = &0 ==> SND(phi x) = &0) /\
                         (SND x = &1 ==> SND(phi x) = &1))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN RCONT_TAC SQCONT;
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN RCONT_TAC SQCONT;
        REAL_ARITH_TAC];
      REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
  EXISTS_TAC `((g:real#real->A) o pi2_rotate) o (phi:real#real->real#real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PI2_HOMOTOPIC_SIDE_REPARAM THEN ASM_SIMP_TAC[PI2_MAP_ROTATE];
    ALL_TAC] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN EXISTS_TAC `(g:real#real->A) o (phi:real#real->real#real)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
    MATCH_MP_TAC PI2_HOMOTOPIC_SIDE_REPARAM THEN ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
  REWRITE_TAC[pi2_homotopic; homotopic_with] THEN
  EXISTS_TAC
   `(g:real#real->A) o
    (\z:real#real#real.
      max (&0) (min (&1) (&1 / &2 + &4 * ((&1 - FST z) * (FST(SND z) - &1 / &2) -
                                          FST z * (SND(SND z) - &1 / &2)))),
      max (&0) (min (&1) (&1 / &2 + &4 * (FST z * (FST(SND z) - &1 / &2) +
                                          (&1 - FST z) * (SND(SND z) - &1 / &2)))))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[pi2_map]] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN RCONT_TAC HSQCONT;
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN RCONT_TAC HSQCONT;
      REAL_ARITH_TAC];
    X_GEN_TAC `x:real#real` THEN EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real#real` THEN EXPAND_TAC "phi" THEN
    REWRITE_TAC[o_THM; pi2_rotate] THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REAL_ARITH_TAC;
    X_GEN_TAC `l:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC PI2_MAP_BOUNDARY THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`l:real`; `FST(x:real#real)`; `SND(x:real#real)`]
                 PI2_ROT_BOUNDARY_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[sqbd]; ALL_TAC] THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN REAL_ARITH_TAC]);;

(* The diagonal swap and the reflection invert the class.                  *)

let PI2_SWAP_ROTATE = prove
 (`!g:real#real->A. g o pi2_swap = (pi2_reverse g) o pi2_rotate`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; pi2_swap; pi2_reverse; pi2_rotate] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`]);;

let PI2_SWAP_HOMOTOPIC = prove
 (`!top a (g:real#real->A).
        pi2_map top a g ==> pi2_homotopic top a (g o pi2_swap) (pi2_reverse g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PI2_SWAP_ROTATE] THEN
  MATCH_MP_TAC PI2_ROTATE_HOMOTOPIC THEN ASM_SIMP_TAC[PI2_MAP_REVERSE]);;

(* ========================================================================= *)
(* Threefold joins and the 3 x 3 grid of 2-cubes.                            *)
(* ========================================================================= *)

let pi2_join3 = new_definition
 `pi2_join3 (g:real#real->A) h k =
    \x. if FST x <= &1 / &3 then g(&3 * FST x,SND x)
        else if FST x <= &2 / &3 then h(&3 * FST x - &1,SND x)
        else k(&3 * FST x - &2,SND x)`;;

let pi2_vjoin3 = new_definition
 `pi2_vjoin3 (g:real#real->A) h k =
    \x. if SND x <= &1 / &3 then g(FST x,&3 * SND x)
        else if SND x <= &2 / &3 then h(FST x,&3 * SND x - &1)
        else k(FST x,&3 * SND x - &2)`;;

let PI2_JOIN3_REPARAM = prove
 (`!g h k:real#real->A.
        pi2_join3 g h k =
        pi2_join (pi2_join g h) k o
        (\x. max (&3 / &4 * FST x) (&3 / &2 * FST x - &1 / &2),SND x)`,
  REWRITE_TAC[FUN_EQ_THM; pi2_join3; pi2_join; o_THM; real_max] THEN
  REPEAT GEN_TAC THEN PI2_CASES_TAC);;

let PI2_JOIN3_HOMOTOPIC = prove
 (`!top a (g:real#real->A) h k.
        pi2_map top a g /\ pi2_map top a h /\ pi2_map top a k
        ==> pi2_homotopic top a (pi2_join3 g h k) (pi2_join (pi2_join g h) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PI2_JOIN3_REPARAM] THEN
  ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_SIDE_REPARAM THEN ASM_SIMP_TAC[PI2_MAP_JOIN] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
    REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN CONJ_TAC THEN RCONT_TAC SQCONT;
      REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC]);;

let PI2_MAP_JOIN3 = prove
 (`!top a (g:real#real->A) h k.
        pi2_map top a g /\ pi2_map top a h /\ pi2_map top a k
        ==> pi2_map top a (pi2_join3 g h k)`,
  MESON_TAC[PI2_JOIN3_HOMOTOPIC; PI2_HOMOTOPIC_IMP_MAP]);;

let PI2_VJOIN3_SWAP = prove
 (`!g h k:real#real->A.
        pi2_vjoin3 g h k =
        pi2_join3 (g o pi2_swap) (h o pi2_swap) (k o pi2_swap) o pi2_swap`,
  REWRITE_TAC[FUN_EQ_THM; pi2_vjoin3; pi2_join3; o_THM; pi2_swap]);;

let PI2_VJOIN3_HOMOTOPIC = prove
 (`!top a (g:real#real->A) h k.
        pi2_map top a g /\ pi2_map top a h /\ pi2_map top a k
        ==> pi2_homotopic top a (pi2_vjoin3 g h k) (pi2_vjoin (pi2_vjoin g h) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PI2_VJOIN3_SWAP] THEN
  SUBGOAL_THEN
   `pi2_vjoin (pi2_vjoin g h) (k:real#real->A) =
    pi2_join (pi2_join (g o pi2_swap) (h o pi2_swap)) (k o pi2_swap) o pi2_swap`
  SUBST1_TAC THENL
   [REWRITE_TAC[PI2_VJOIN_SWAP; PI2_SWAP_SWAP]; ALL_TAC] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_SWAP THEN MATCH_MP_TAC PI2_JOIN3_HOMOTOPIC THEN
  ASM_SIMP_TAC[PI2_MAP_SWAP]);;

let PI2_MAP_VJOIN3 = prove
 (`!top a (g:real#real->A) h k.
        pi2_map top a g /\ pi2_map top a h /\ pi2_map top a k
        ==> pi2_map top a (pi2_vjoin3 g h k)`,
  MESON_TAC[PI2_VJOIN3_HOMOTOPIC; PI2_HOMOTOPIC_IMP_MAP]);;

(* Class of a threefold join and of a threefold vertical join.              *)

let PI2_CLASS_JOIN3 = prove
 (`!top a (g:real#real->A) h k.
        pi2_map top a g /\ pi2_map top a h /\ pi2_map top a k
        ==> pi2_class top a (pi2_join3 g h k) =
            group_mul (pi2_group(top,a))
              (group_mul (pi2_group(top,a)) (pi2_class top a g) (pi2_class top a h))
              (pi2_class top a k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PI2_MAP_BASEPOINT) THEN
  ASM_SIMP_TAC[PI2_GROUP; PI2_MAP_JOIN; PI2_MAP_JOIN3; PI2_CLASS_EQ] THEN
  ASM_SIMP_TAC[PI2_JOIN3_HOMOTOPIC]);;

let PI2_CLASS_VJOIN3 = prove
 (`!top a (g:real#real->A) h k.
        pi2_map top a g /\ pi2_map top a h /\ pi2_map top a k
        ==> pi2_class top a (pi2_vjoin3 g h k) =
            group_mul (pi2_group(top,a))
              (group_mul (pi2_group(top,a)) (pi2_class top a g) (pi2_class top a h))
              (pi2_class top a k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PI2_MAP_BASEPOINT) THEN
  ASM_SIMP_TAC[PI2_GROUP; PI2_MAP_JOIN; PI2_MAP_VJOIN3; PI2_CLASS_EQ] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
  EXISTS_TAC `pi2_vjoin (pi2_vjoin (g:real#real->A) h) k` THEN
  ASM_SIMP_TAC[PI2_VJOIN3_HOMOTOPIC] THEN
  MATCH_MP_TAC PI2_HOMOTOPIC_TRANS THEN
  EXISTS_TAC `pi2_join (pi2_vjoin (g:real#real->A) h) k` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN MATCH_MP_TAC PI2_JOIN_VJOIN THEN
    ASM_SIMP_TAC[PI2_MAP_VJOIN];
    MATCH_MP_TAC PI2_HOMOTOPIC_JOIN THEN ASM_REWRITE_TAC[PI2_HOMOTOPIC_REFL] THEN
    ONCE_REWRITE_TAC[PI2_HOMOTOPIC_SYM] THEN ASM_SIMP_TAC[PI2_JOIN_VJOIN]]);;

(* The class of a pi2 map depends only on its values on the square.         *)

let PI2_MAP_EQ = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g /\ (!x. x IN topspace sqtop ==> h x = g x)
        ==> pi2_map top a h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_map] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `g:real#real->A` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let PI2_CLASS_EQ_ON = prove
 (`!top a (g:real#real->A) h.
        pi2_map top a g /\ (!x. x IN topspace sqtop ==> h x = g x)
        ==> pi2_class top a h = pi2_class top a g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pi2_map top a (h:real#real->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PI2_MAP_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[PI2_CLASS_EQ] THEN MATCH_MP_TAC PI2_HOMOTOPIC_EQ THEN
  MAP_EVERY EXISTS_TAC [`g:real#real->A`; `g:real#real->A`] THEN
  ASM_SIMP_TAC[PI2_HOMOTOPIC_REFL]);;

(* Continuity of threefold joins of arbitrary maps agreeing on the seams.   *)

let CONTINUOUS_MAP_PI2_JOIN3 = prove
 (`!top (g:real#real->A) h k.
        continuous_map (sqtop,top) g /\ continuous_map (sqtop,top) h /\
        continuous_map (sqtop,top) k /\
        (!t. &0 <= t /\ t <= &1 ==> g(&1,t) = h(&0,t) /\ h(&1,t) = k(&0,t))
        ==> continuous_map (sqtop,top) (pi2_join3 g h k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PI2_JOIN3_REPARAM] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SQTOP THEN
    REWRITE_TAC[CONTINUOUS_MAP_SQTOP_FST_SND; CONTINUOUS_MAP_SQTOP_FST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN CONJ_TAC THEN RCONT_TAC SQCONT;
      REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REAL_ARITH_TAC];
    REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_PI2_JOIN THEN REPEAT CONJ_TAC) THEN
    ASM_SIMP_TAC[pi2_join] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[]]);;

let CONTINUOUS_MAP_PI2_VJOIN3 = prove
 (`!top (g:real#real->A) h k.
        continuous_map (sqtop,top) g /\ continuous_map (sqtop,top) h /\
        continuous_map (sqtop,top) k /\
        (!s. &0 <= s /\ s <= &1 ==> g(s,&1) = h(s,&0) /\ h(s,&1) = k(s,&0))
        ==> continuous_map (sqtop,top) (pi2_vjoin3 g h k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PI2_VJOIN3_SWAP] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PI2_SWAP] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_PI2_JOIN3 THEN
  ASM_SIMP_TAC[o_THM; pi2_swap] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PI2_SWAP]);;

let PI2_JOIN3_COMPOSE = prove
 (`!(f:A->B) g h k. f o pi2_join3 g h k = pi2_join3 (f o g) (f o h) (f o k)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; pi2_join3] THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let PI2_VJOIN3_COMPOSE = prove
 (`!(f:A->B) g h k. f o pi2_vjoin3 g h k = pi2_vjoin3 (f o g) (f o h) (f o k)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; pi2_vjoin3] THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

(* ========================================================================= *)
(* The square onto the 2-simplex, edge-constant singular                     *)
(* simplices and their classes in pi_2.                                      *)
(* ========================================================================= *)

(* Points of the 3-simplex given by four barycentric coordinates.           *)

let pi2_bary = new_definition
 `pi2_bary a0 a1 a2 a3 =
    (\i. if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2
         else if i = 3 then a3 else &0)`;;

let PI2_IDX4 = ARITH_RULE
 `!i. 4 <= i ==> ~(i = 0) /\ ~(i = 1) /\ ~(i = 2) /\ ~(i = 3) /\
                 ~(i < 1) /\ ~(i < 2) /\ ~(i < 3) /\ ~(i < 4) /\
                 ~(i - 1 = 0) /\ ~(i - 1 = 1) /\ ~(i - 1 = 2)`;;

let PI2_IDX_CASES = ARITH_RULE `!i. i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ 4 <= i`;;

let PI2_IDX_TAC =
  STRIP_ASSUME_TAC(SPEC `i:num` PI2_IDX_CASES) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC; FIRST_X_ASSUM SUBST_ALL_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC; FIRST_X_ASSUM SUBST_ALL_TAC;
    MP_TAC(SPEC `i:num` PI2_IDX4) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let PI2_BARY_EQ = prove
 (`!a0 a1 a2 a3 b0 b1 b2 b3.
        pi2_bary a0 a1 a2 a3 = pi2_bary b0 b1 b2 b3 <=>
        a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi2_bary; FUN_EQ_THM] THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                         MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    SIMP_TAC[]]);;

let PI2_BARY_IN_STANDARD_SIMPLEX = prove
 (`!a0 a1 a2 a3.
        &0 <= a0 /\ &0 <= a1 /\ &0 <= a2 /\ &0 <= a3 /\ a0 + a1 + a2 + a3 = &1
        ==> pi2_bary a0 a1 a2 a3 IN standard_simplex 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[pi2_bary] THEN PI2_IDX_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[pi2_bary] THEN
    ASM_SIMP_TAC[ARITH_RULE `3 < i ==> 4 <= i`; PI2_IDX4];
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
    REWRITE_TAC[pi2_bary] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]);;

let CONTINUOUS_MAP_PI2_BARY = prove
 (`!top (f0:A->real) f1 f2 f3.
        continuous_map (top,euclideanreal) f0 /\
        continuous_map (top,euclideanreal) f1 /\
        continuous_map (top,euclideanreal) f2 /\
        continuous_map (top,euclideanreal) f3
        ==> continuous_map (top,product_topology (:num) (\i. euclideanreal))
                           (\x. pi2_bary (f0 x) (f1 x) (f2 x) (f3 x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV; pi2_bary] THEN
  X_GEN_TAC `i:num` THEN PI2_IDX_TAC THEN
  ASM_REWRITE_TAC[ETA_AX; CONTINUOUS_MAP_REAL_CONST]);;

(* The square onto the 2-simplex: (s,t) |-> (1 - s, s (1 - t), s t).        *)
(* It collapses the side s = 0 to the vertex e_0 and is injective elsewhere. *)

let pi2_tri = new_definition
 `pi2_tri (x:real#real) =
    (\i. if i = 0 then &1 - FST x
         else if i = 1 then FST x * (&1 - SND x)
         else if i = 2 then FST x * SND x else &0)`;;

let PI2_UNIT_MUL = prove
 (`!a b. &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1
         ==> &0 <= a * b /\ a * b <= &1`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let PI2_TRI_IN_STANDARD_SIMPLEX = prove
 (`!x. x IN topspace sqtop ==> pi2_tri x IN standard_simplex 2`,
  REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[pi2_tri] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRY(MATCH_MP_TAC PI2_UNIT_MUL) THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[pi2_tri] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 < i ==> ~(i = 0) /\ ~(i = 1) /\ ~(i = 2)`];
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
    REWRITE_TAC[pi2_tri] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let CONTINUOUS_MAP_PI2_TRI = prove
 (`continuous_map (sqtop,subtopology (product_topology (:num) (\i. euclideanreal))
                                     (standard_simplex 2)) pi2_tri`,
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV; pi2_tri] THEN
    X_GEN_TAC `i:num` THEN
    MAP_EVERY ASM_CASES_TAC [`i = 0`; `i = 1`; `i = 2`] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN RCONT_TAC SQCONT;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PI2_TRI_IN_STANDARD_SIMPLEX]]);;

let PI2_TRI_INJECTIVE = prove
 (`!x y. x IN topspace sqtop /\ y IN topspace sqtop /\ pi2_tri x = pi2_tri y
         ==> x = y \/ FST x = &0 /\ FST y = &0`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_TOPSPACE_SQTOP; pi2_tri; FST; SND; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `s':real`; `t':real`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN FIRST_ASSUM(MP_TAC o SPEC `2`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `s':real = s` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_EQ_MUL_LCANCEL]);;

let PI2_TRI_SURJECTIVE = prove
 (`!y. y IN standard_simplex 2 ==> ?x. x IN topspace sqtop /\ pi2_tri x = y`,
  X_GEN_TAC `y:num->real` THEN REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B") (CONJUNCTS_THEN2 (LABEL_TAC "Z")
    ASSUME_TAC)) THEN
  USE_THEN "B" (fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                          MP_TAC(SPEC `2` th)) THEN
  REPEAT DISCH_TAC THEN
  EXISTS_TAC `(&1 - y 0,if y 0 = &1 then &0 else y 2 / (&1 - y 0)):real#real` THEN
  REWRITE_TAC[IN_TOPSPACE_SQTOP; FUN_EQ_THM; pi2_tri; FST; SND] THEN
  ASM_CASES_TAC `(y:num->real) 0 = &1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(y:num->real) 1 = &0 /\ y 2 = &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN X_GEN_TAC `i:num` THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO]) THEN
    CONV_TAC SYM_CONV THEN USE_THEN "Z" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `&0 < &1 - (y:num->real) 0 /\ ~(&1 - y 0 = &0)` STRIP_ASSUME_TAC
    THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THENL
     [REAL_ARITH_TAC;
      UNDISCH_TAC `~(&1 - (y:num->real) 0 = &0)` THEN
      UNDISCH_TAC `(y:num->real) 0 + y 1 + y 2 = &1` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `~(&1 - (y:num->real) 0 = &0)` THEN CONV_TAC REAL_FIELD;
      CONV_TAC SYM_CONV THEN USE_THEN "Z" MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let PI2_TRI_BOUNDARY = prove
 (`!x. x IN topspace sqtop
       ==> (sqbd x <=> pi2_tri x 0 = &0 \/ pi2_tri x 1 = &0 \/ pi2_tri x 2 = &0)`,
  REWRITE_TAC[sqbd; pi2_tri] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC);;

let PI2_TRI_IMAGE = prove
 (`IMAGE pi2_tri (topspace sqtop) = standard_simplex 2`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  MESON_TAC[PI2_TRI_IN_STANDARD_SIMPLEX; PI2_TRI_SURJECTIVE]);;

let QUOTIENT_MAP_PI2_TRI = prove
 (`quotient_map (sqtop,subtopology (product_topology (:num) (\i. euclideanreal))
                                   (standard_simplex 2)) pi2_tri`,
  MATCH_MP_TAC CONTINUOUS_CLOSED_IMP_QUOTIENT_MAP THEN
  REWRITE_TAC[CONTINUOUS_MAP_PI2_TRI; TOPSPACE_STANDARD_SIMPLEX; PI2_TRI_IMAGE] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_CLOSED_MAP THEN
  REWRITE_TAC[CONTINUOUS_MAP_PI2_TRI] THEN CONJ_TAC THENL
   [REWRITE_TAC[sqtop; COMPACT_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL];
    MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[HAUSDORFF_SPACE_PRODUCT_TOPOLOGY; HAUSDORFF_SPACE_EUCLIDEANREAL]]);;

(* Singular simplices whose 1-skeleton maps to the base point.              *)

let edgeconst_simplex = new_definition
 `edgeconst_simplex (p,top) (a:A) f <=>
    singular_simplex (p,top) f /\
    !x i j. x IN standard_simplex p /\ (!k. ~(k = i) /\ ~(k = j) ==> x k = &0)
            ==> f x = a`;;

let EDGECONST_SIMPLEX_2 = prove
 (`!top a (f:(num->real)->A).
        edgeconst_simplex (2,top) a f <=>
        singular_simplex (2,top) f /\
        !x. x IN standard_simplex 2 /\ (x 0 = &0 \/ x 1 = &0 \/ x 2 = &0)
            ==> f x = a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[edgeconst_simplex] THEN
  AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:num->real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")) THEN
    SUBGOAL_THEN `!k. 2 < k ==> (x:num->real) k = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:num->real) IN standard_simplex 2` THEN
      SIMP_TAC[standard_simplex; IN_ELIM_THM];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "D" STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXISTS_TAC [`1`; `2`];
      MAP_EVERY EXISTS_TAC [`0`; `2`];
      MAP_EVERY EXISTS_TAC [`0`; `1`]] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    (ASM_CASES_TAC `k = 0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     ASM_CASES_TAC `k = 1` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     ASM_CASES_TAC `k = 2` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);
    MAP_EVERY X_GEN_TAC [`x:num->real`; `i:num`; `j:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S")) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `~(i = 0) /\ ~(j = 0)` THENL
     [DISJ1_TAC THEN REMOVE_THEN "S" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `~(i = 1) /\ ~(j = 1)` THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN REMOVE_THEN "S" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN REMOVE_THEN "S" MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

let EDGECONST_SIMPLEX_IMP_SINGULAR = prove
 (`!p top a (f:(num->real)->A).
        edgeconst_simplex (p,top) a f ==> singular_simplex (p,top) f`,
  SIMP_TAC[edgeconst_simplex]);;

let EDGECONST_SIMPLEX_PI2_MAP = prove
 (`!top a (f:(num->real)->A).
        edgeconst_simplex (2,top) a f ==> pi2_map top a (f o pi2_tri)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EDGECONST_SIMPLEX_2; singular_simplex] THEN
  STRIP_TAC THEN REWRITE_TAC[pi2_map] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex 2)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PI2_TRI];
    X_GEN_TAC `x:real#real` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[PI2_TRI_IN_STANDARD_SIMPLEX] THEN
    ASM_MESON_TAC[PI2_TRI_BOUNDARY]]);;

let EDGECONST_SIMPLEX_FACE = prove
 (`!p k top a (f:(num->real)->A).
        edgeconst_simplex (p,top) a f /\ 1 <= p /\ k <= p
        ==> edgeconst_simplex (p - 1,top) a (singular_face p k f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[edgeconst_simplex] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SINGULAR_SIMPLEX_SINGULAR_FACE] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[singular_face; RESTRICTION; o_THM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`if i < k then i else i + 1`; `if j < k then j else j + 1`] THEN
  ASM_SIMP_TAC[SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[simplicial_face] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COND_RAND]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      is_cond(rand(rand(concl th)))) )) THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      is_cond(rand(rand(concl th)))) )) THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let EDGECONST_SIMPLEX_CONST = prove
 (`!p top a:A.
        a IN topspace top
        ==> edgeconst_simplex (p,top) a (RESTRICTION (standard_simplex p) (\x. a))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[edgeconst_simplex; singular_simplex] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_CONST; RESTRICTION]);;

let PI2_CLASS_EDGECONST_CONST = prove
 (`!top a:A.
        a IN topspace top
        ==> pi2_class top a (RESTRICTION (standard_simplex 2) (\x. a) o pi2_tri) =
            group_id(pi2_group(top,a))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PI2_GROUP] THEN
  MATCH_MP_TAC PI2_CLASS_EQ_ON THEN ASM_SIMP_TAC[PI2_MAP_CONST] THEN
  SIMP_TAC[o_THM; RESTRICTION; PI2_TRI_IN_STANDARD_SIMPLEX]);;

(* Every pi_2 map factors through the square-to-simplex map.                *)

let PI2_MAP_TRI_FACTOR = prove
 (`!top a (g:real#real->A).
        pi2_map top a g
        ==> ?f. edgeconst_simplex (2,top) a f /\
                !x. x IN topspace sqtop ==> f(pi2_tri x) = g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sqtop`;
                 `subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex 2)`;
                 `top:A topology`; `pi2_tri`; `g:real#real->A`]
                QUOTIENT_MAP_LIFT_EXISTS) THEN
  REWRITE_TAC[QUOTIENT_MAP_PI2_TRI] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[pi2_map]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real#real`; `y:real#real`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`x:real#real`; `y:real#real`] PI2_TRI_INJECTIVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `a:A` THEN CONJ_TAC THENL
     [ALL_TAC; CONV_TAC SYM_CONV] THEN
    MATCH_MP_TAC PI2_MAP_BOUNDARY THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[sqbd];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(num->real)->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `RESTRICTION (standard_simplex 2) (f:(num->real)->A)` THEN
  ASM_SIMP_TAC[RESTRICTION; PI2_TRI_IN_STANDARD_SIMPLEX] THEN
  REWRITE_TAC[EDGECONST_SIMPLEX_2; singular_simplex] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  ASM_SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
  X_GEN_TAC `y:num->real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[RESTRICTION] THEN
  MP_TAC(SPEC `y:num->real` PI2_TRI_SURJECTIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real#real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC PI2_MAP_BOUNDARY THEN EXISTS_TAC `top:A topology` THEN
  ASM_SIMP_TAC[PI2_TRI_BOUNDARY]);;

(* ========================================================================= *)
(* A 3 x 3 net of the boundary of the 3-simplex and the                      *)
(* homotopy addition theorem for edge-constant 3-simplices.                  *)
(* Cell (i,j) sits in column i (first coordinate) and row j.  The cells of   *)
(* the middle column and the middle of the right column are the four faces;  *)
(* the others lie in edges through the vertex e_0.                            *)
(* ========================================================================= *)

let pi2_c11 = new_definition
 `pi2_c11 (x:real#real) = pi2_bary (&1 - FST x * SND x) (FST x * SND x) (&0) (&0)`;;
let pi2_c12 = new_definition
 `pi2_c12 (x:real#real) = pi2_bary (&1 - FST x) (FST x) (&0) (&0)`;;
let pi2_c13 = new_definition
 `pi2_c13 (x:real#real) =
    pi2_bary (&1 - FST x * (&1 - SND x)) (FST x * (&1 - SND x)) (&0) (&0)`;;
let pi2_c21 = new_definition
 `pi2_c21 (x:real#real) =
    pi2_bary (&1 - SND x) (SND x * (&1 - FST x)) (SND x * FST x) (&0)`;;
let pi2_c22 = new_definition
 `pi2_c22 (x:real#real) =
    pi2_bary (&0) (&1 - FST x) (FST x * (&1 - SND x)) (FST x * SND x)`;;
let pi2_c23 = new_definition
 `pi2_c23 (x:real#real) =
    pi2_bary (SND x) ((&1 - SND x) * (&1 - FST x)) (&0) ((&1 - SND x) * FST x)`;;
let pi2_c31 = new_definition
 `pi2_c31 (x:real#real) =
    pi2_bary (&1 - SND x * (&1 - FST x)) (&0) (SND x * (&1 - FST x)) (&0)`;;
let pi2_c32 = new_definition
 `pi2_c32 (x:real#real) =
    pi2_bary (FST x) (&0) ((&1 - FST x) * (&1 - SND x)) ((&1 - FST x) * SND x)`;;
let pi2_c33 = new_definition
 `pi2_c33 (x:real#real) =
    pi2_bary (&1 - (&1 - FST x) * (&1 - SND x)) (&0) (&0)
             ((&1 - FST x) * (&1 - SND x))`;;

let PI2_CELLS = [pi2_c11; pi2_c12; pi2_c13; pi2_c21; pi2_c22; pi2_c23;
                 pi2_c31; pi2_c32; pi2_c33];;

let pi2_net = new_definition
 `pi2_net = pi2_join3 (pi2_vjoin3 pi2_c11 pi2_c12 pi2_c13)
                      (pi2_vjoin3 pi2_c21 pi2_c22 pi2_c23)
                      (pi2_vjoin3 pi2_c31 pi2_c32 pi2_c33)`;;

let PI2_UNIT_MUL_LE = prove
 (`!a b. &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1 ==> a * b <= &1`,
  MESON_TAC[PI2_UNIT_MUL]);;

let PI2_UNIT_TAC =
  FIRST [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &0 <= &1 - x`) THEN
         MATCH_MP_TAC PI2_UNIT_MUL_LE THEN ASM_REAL_ARITH_TAC];;

let PI2_CELLS_IN_STANDARD_SIMPLEX = prove
 (`!x. x IN topspace sqtop
       ==> pi2_c11 x IN standard_simplex 3 /\ pi2_c12 x IN standard_simplex 3 /\
           pi2_c13 x IN standard_simplex 3 /\ pi2_c21 x IN standard_simplex 3 /\
           pi2_c22 x IN standard_simplex 3 /\ pi2_c23 x IN standard_simplex 3 /\
           pi2_c31 x IN standard_simplex 3 /\ pi2_c32 x IN standard_simplex 3 /\
           pi2_c33 x IN standard_simplex 3`,
  REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC PI2_CELLS THEN MATCH_MP_TAC PI2_BARY_IN_STANDARD_SIMPLEX THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THEN (PI2_UNIT_TAC ORELSE CONV_TAC REAL_RING));;

(* Lambda forms of the cells, for continuity proofs.                        *)

let PI2_CELL_ABS =
  let cell_abs th =
    let th' = SPEC_ALL th in
    let l,r = dest_eq(concl th') in
    prove(mk_eq(rator l,mk_abs(rand l,r)),REWRITE_TAC[FUN_EQ_THM; th]) in
  map cell_abs PI2_CELLS;;

let CONTINUOUS_MAP_PI2_CELLS = prove
 (`continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c11 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c12 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c13 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c21 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c22 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c23 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c31 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c32 /\
   continuous_map (sqtop,product_topology (:num) (\i. euclideanreal)) pi2_c33`,
  REWRITE_TAC PI2_CELL_ABS THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_PI2_BARY THEN REPEAT CONJ_TAC THEN
  RCONT_TAC SQCONT);;

let PI2_CELL_SEAMS = prove
 (`(!s. pi2_c11(s,&1) = pi2_c12(s,&0)) /\ (!s. pi2_c12(s,&1) = pi2_c13(s,&0)) /\
   (!s. pi2_c21(s,&1) = pi2_c22(s,&0)) /\ (!s. pi2_c22(s,&1) = pi2_c23(s,&0)) /\
   (!s. pi2_c31(s,&1) = pi2_c32(s,&0)) /\ (!s. pi2_c32(s,&1) = pi2_c33(s,&0)) /\
   (!t. pi2_c11(&1,t) = pi2_c21(&0,t)) /\ (!t. pi2_c21(&1,t) = pi2_c31(&0,t)) /\
   (!t. pi2_c12(&1,t) = pi2_c22(&0,t)) /\ (!t. pi2_c22(&1,t) = pi2_c32(&0,t)) /\
   (!t. pi2_c13(&1,t) = pi2_c23(&0,t)) /\ (!t. pi2_c23(&1,t) = pi2_c33(&0,t))`,
  REWRITE_TAC PI2_CELLS THEN REWRITE_TAC[PI2_BARY_EQ; FST; SND] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let PI2_JOIN3_IN = prove
 (`!(g:real#real->A) h k s.
        (!x. x IN topspace sqtop ==> g x IN s) /\
        (!x. x IN topspace sqtop ==> h x IN s) /\
        (!x. x IN topspace sqtop ==> k x IN s)
        ==> !x. x IN topspace sqtop ==> pi2_join3 g h k x IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real#real` THEN
  REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN STRIP_TAC THEN REWRITE_TAC[pi2_join3] THEN
  REPEAT COND_CASES_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
  ASM_REAL_ARITH_TAC);;

let PI2_VJOIN3_IN = prove
 (`!(g:real#real->A) h k s.
        (!x. x IN topspace sqtop ==> g x IN s) /\
        (!x. x IN topspace sqtop ==> h x IN s) /\
        (!x. x IN topspace sqtop ==> k x IN s)
        ==> !x. x IN topspace sqtop ==> pi2_vjoin3 g h k x IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real#real` THEN
  REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN STRIP_TAC THEN REWRITE_TAC[pi2_vjoin3] THEN
  REPEAT COND_CASES_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
  ASM_REAL_ARITH_TAC);;

let PI2_NET_IN_STANDARD_SIMPLEX = prove
 (`!x. x IN topspace sqtop ==> pi2_net x IN standard_simplex 3`,
  REWRITE_TAC[pi2_net] THEN MATCH_MP_TAC PI2_JOIN3_IN THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC PI2_VJOIN3_IN THEN
  SIMP_TAC[PI2_CELLS_IN_STANDARD_SIMPLEX]);;

let CONTINUOUS_MAP_PI2_NET = prove
 (`continuous_map (sqtop,subtopology (product_topology (:num) (\i. euclideanreal))
                                     (standard_simplex 3)) pi2_net`,
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PI2_NET_IN_STANDARD_SIMPLEX]] THEN
  REWRITE_TAC[pi2_net] THEN MATCH_MP_TAC CONTINUOUS_MAP_PI2_JOIN3 THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_PI2_VJOIN3 THEN
    REWRITE_TAC[CONTINUOUS_MAP_PI2_CELLS; PI2_CELL_SEAMS];
    MATCH_MP_TAC CONTINUOUS_MAP_PI2_VJOIN3 THEN
    REWRITE_TAC[CONTINUOUS_MAP_PI2_CELLS; PI2_CELL_SEAMS];
    MATCH_MP_TAC CONTINUOUS_MAP_PI2_VJOIN3 THEN
    REWRITE_TAC[CONTINUOUS_MAP_PI2_CELLS; PI2_CELL_SEAMS];
    REWRITE_TAC[pi2_vjoin3; PI2_CELL_SEAMS]]);;

let PI2_NET_BOUNDARY = prove
 (`!x. x IN topspace sqtop /\ sqbd x ==> pi2_net x = pi2_bary (&1) (&0) (&0) (&0)`,
  REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd; pi2_net; pi2_join3; pi2_vjoin3] THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC PI2_CELLS THEN
  REWRITE_TAC[PI2_BARY_EQ; FST; SND] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_SUB_REFL] THEN
  ASM_REAL_ARITH_TAC);;

let PI2_NET_PI2_MAP = prove
 (`pi2_map (subtopology (product_topology (:num) (\i. euclideanreal))
                        (standard_simplex 3))
           (pi2_bary (&1) (&0) (&0) (&0)) pi2_net`,
  REWRITE_TAC[pi2_map; CONTINUOUS_MAP_PI2_NET; PI2_NET_BOUNDARY]);;

let PI2_NET_NULLHOMOTOPIC = prove
 (`pi2_homotopic (subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex 3))
                 (pi2_bary (&1) (&0) (&0) (&0)) pi2_net
                 (\x. pi2_bary (&1) (&0) (&0) (&0))`,
  REWRITE_TAC[pi2_homotopic; homotopic_with] THEN
  EXISTS_TAC `\z:real#real#real.
       (\i. (&1 - FST z) * pi2_net (SND z) i +
            FST z * pi2_bary (&1) (&0) (&0) (&0) i)` THEN
  REWRITE_TAC[FUN_EQ_THM; REAL_SUB_RZERO; REAL_SUB_REFL] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN X_GEN_TAC `i:num` THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      REPEAT CONJ_TAC THEN TRY(RCONT_TAC HSQCONT) THEN
      SUBGOAL_THEN `(\z:real#real#real. pi2_net (SND z) i) =
                    (\x. pi2_net x i) o SND` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND] THEN
      MP_TAC CONTINUOUS_MAP_PI2_NET THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_TOPSPACE_HSQ] THEN
      X_GEN_TAC `z:real#real#real` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONVEX_STANDARD_SIMPLEX THEN REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[PI2_NET_IN_STANDARD_SIMPLEX] THEN
      MATCH_MP_TAC PI2_BARY_IN_STANDARD_SIMPLEX THEN REAL_ARITH_TAC];
    X_GEN_TAC `l:real` THEN DISCH_TAC THEN X_GEN_TAC `x:real#real` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[PI2_NET_BOUNDARY] THEN REAL_ARITH_TAC]);;

(* The face cells are the faces composed with pi2_tri and a symmetry.       *)

let PI2_CELL_FACES = prove
 (`(!x. pi2_c21 x = simplicial_face 3 (pi2_tri (pi2_swap x))) /\
   (!x. pi2_c22 x = simplicial_face 0 (pi2_tri x)) /\
   (!x. pi2_c23 x = simplicial_face 2 (pi2_tri (pi2_rotate x))) /\
   (!x. pi2_c32 x = simplicial_face 1 (pi2_tri (&1 - FST x,SND x)))`,
  REWRITE_TAC PI2_CELLS THEN
  REWRITE_TAC[FUN_EQ_THM; pi2_bary; simplicial_face; pi2_tri; pi2_swap;
              pi2_rotate; FST; SND] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:real#real` THEN X_GEN_TAC `i:num` THEN
  PI2_IDX_TAC THEN REAL_ARITH_TAC);;

(* Edge cells are mapped to the base point by edge-constant 3-simplices.     *)

let EDGECONST_SIMPLEX_EDGE_CELLS = prove
 (`!top a (tau:(num->real)->A) x.
        edgeconst_simplex (3,top) a tau /\ x IN topspace sqtop
        ==> tau(pi2_c11 x) = a /\ tau(pi2_c12 x) = a /\ tau(pi2_c13 x) = a /\
            tau(pi2_c31 x) = a /\ tau(pi2_c33 x) = a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[edgeconst_simplex] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[PI2_CELLS_IN_STANDARD_SIMPLEX] THENL
   [MAP_EVERY EXISTS_TAC [`0`; `1`];
    MAP_EVERY EXISTS_TAC [`0`; `1`];
    MAP_EVERY EXISTS_TAC [`0`; `1`];
    MAP_EVERY EXISTS_TAC [`0`; `2`];
    MAP_EVERY EXISTS_TAC [`0`; `3`]] THEN
  REWRITE_TAC PI2_CELLS THEN REWRITE_TAC[pi2_bary] THEN
  X_GEN_TAC `i:num` THEN PI2_IDX_TAC);;

let EDGECONST_SIMPLEX_BASEPOINT = prove
 (`!top a (tau:(num->real)->A).
        edgeconst_simplex (3,top) a tau ==> tau(pi2_bary (&1) (&0) (&0) (&0)) = a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[edgeconst_simplex] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`0`; `0`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PI2_BARY_IN_STANDARD_SIMPLEX THEN REAL_ARITH_TAC;
    REWRITE_TAC[pi2_bary] THEN X_GEN_TAC `i:num` THEN PI2_IDX_TAC]);;

let EDGECONST_SIMPLEX_FACE_CELLS = prove
 (`!top a (tau:(num->real)->A) x.
        edgeconst_simplex (3,top) a tau /\ x IN topspace sqtop
        ==> tau(pi2_c21 x) = ((singular_face 3 3 tau o pi2_tri) o pi2_swap) x /\
            tau(pi2_c22 x) = (singular_face 3 0 tau o pi2_tri) x /\
            tau(pi2_c23 x) = ((singular_face 3 2 tau o pi2_tri) o pi2_rotate) x /\
            tau(pi2_c32 x) = pi2_reverse (singular_face 3 1 tau o pi2_tri) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PI2_CELL_FACES; o_THM; pi2_reverse] THEN
  REWRITE_TAC[singular_face; RESTRICTION; o_THM] THEN
  SUBGOAL_THEN
   `pi2_tri (pi2_swap x) IN standard_simplex 2 /\
    pi2_tri x IN standard_simplex 2 /\
    pi2_tri (pi2_rotate x) IN standard_simplex 2 /\
    pi2_tri (&1 - FST x,SND x) IN standard_simplex 2`
   (fun th -> REWRITE_TAC[th; ARITH_RULE `3 - 1 = 2`]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC PI2_TRI_IN_STANDARD_SIMPLEX THEN
  ASM_SIMP_TAC[PI2_SWAP_BOUNDARY; PI2_ROTATE_BOUNDARY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_TOPSPACE_SQTOP]) THEN
  REWRITE_TAC[IN_TOPSPACE_SQTOP; pi2_swap; pi2_rotate] THEN ASM_REAL_ARITH_TAC);;

(* Classes of the nine composite cells.                                      *)

let PI2_HAT_EDGE_CELLS = prove
 (`!top a (tau:(num->real)->A).
        edgeconst_simplex (3,top) a tau
        ==> pi2_map top a (tau o pi2_c11) /\ pi2_map top a (tau o pi2_c12) /\
            pi2_map top a (tau o pi2_c13) /\ pi2_map top a (tau o pi2_c31) /\
            pi2_map top a (tau o pi2_c33) /\
            pi2_class top a (tau o pi2_c11) = group_id(pi2_group(top,a)) /\
            pi2_class top a (tau o pi2_c12) = group_id(pi2_group(top,a)) /\
            pi2_class top a (tau o pi2_c13) = group_id(pi2_group(top,a)) /\
            pi2_class top a (tau o pi2_c31) = group_id(pi2_group(top,a)) /\
            pi2_class top a (tau o pi2_c33) = group_id(pi2_group(top,a))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP EDGECONST_SIMPLEX_BASEPOINT) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [edgeconst_simplex]) THEN
    REWRITE_TAC[singular_simplex] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX] THEN
    DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o CONJUNCT1) THEN
    MATCH_MP_TAC PI2_BARY_IN_STANDARD_SIMPLEX THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`] PI2_MAP_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[PI2_GROUP] THEN
  MATCH_MP_TAC(TAUT `(p1 /\ p2 /\ p3 /\ p4 /\ p5) /\
                     (p1 /\ p2 /\ p3 /\ p4 /\ p5 ==> q)
                     ==> p1 /\ p2 /\ p3 /\ p4 /\ p5 /\ q`) THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC PI2_MAP_EQ THEN
    EXISTS_TAC `(\x. a):real#real->A` THEN ASM_REWRITE_TAC[o_THM] THEN
    ASM_MESON_TAC[EDGECONST_SIMPLEX_EDGE_CELLS];
    STRIP_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC PI2_CLASS_EQ_ON THEN
    ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[EDGECONST_SIMPLEX_EDGE_CELLS]]);;

let PI2_FACE_CELLS_TAC =
  X_GEN_TAC `x:real#real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `a:A`; `tau:(num->real)->A`; `x:real#real`]
               EDGECONST_SIMPLEX_FACE_CELLS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM] THEN SIMP_TAC[];;

let PI2_HAT_FACE_CELLS = prove
 (`!top a (tau:(num->real)->A).
        edgeconst_simplex (3,top) a tau
        ==> pi2_map top a (tau o pi2_c21) /\ pi2_map top a (tau o pi2_c22) /\
            pi2_map top a (tau o pi2_c23) /\ pi2_map top a (tau o pi2_c32) /\
            pi2_class top a (tau o pi2_c21) =
              group_inv (pi2_group(top,a))
                        (pi2_class top a (singular_face 3 3 tau o pi2_tri)) /\
            pi2_class top a (tau o pi2_c22) =
              pi2_class top a (singular_face 3 0 tau o pi2_tri) /\
            pi2_class top a (tau o pi2_c23) =
              pi2_class top a (singular_face 3 2 tau o pi2_tri) /\
            pi2_class top a (tau o pi2_c32) =
              group_inv (pi2_group(top,a))
                        (pi2_class top a (singular_face 3 1 tau o pi2_tri))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. k <= 3 ==> pi2_map top a (singular_face 3 k (tau:(num->real)->A) o
                                               pi2_tri)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EDGECONST_SIMPLEX_PI2_MAP THEN
    MP_TAC(SPECL [`3`; `k:num`; `top:A topology`; `a:A`; `tau:(num->real)->A`]
                 EDGECONST_SIMPLEX_FACE) THEN
    ASM_REWRITE_TAC[ARITH_RULE `3 - 1 = 2`] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pi2_map top a (singular_face 3 0 tau o pi2_tri) /\
    pi2_map top a (singular_face 3 1 tau o pi2_tri) /\
    pi2_map top a (singular_face 3 2 tau o pi2_tri) /\
    pi2_map top a ((singular_face 3 3 tau:(num->real)->A) o pi2_tri)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PI2_MAP_BASEPOINT) THEN
  ASM_SIMP_TAC[PI2_GROUP] THEN
  SUBGOAL_THEN
   `pi2_map top a (((singular_face 3 3 tau:(num->real)->A) o pi2_tri) o pi2_swap) /\
    pi2_map top a (((singular_face 3 2 tau:(num->real)->A) o pi2_tri) o pi2_rotate) /\
    pi2_map top a (pi2_reverse((singular_face 3 1 tau:(num->real)->A) o pi2_tri))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PI2_MAP_SWAP; PI2_MAP_ROTATE; PI2_MAP_REVERSE]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p1 /\ p2 /\ p3 /\ p4) /\
                     (p1 /\ p2 /\ p3 /\ p4 ==> q)
                     ==> p1 /\ p2 /\ p3 /\ p4 /\ q`) THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC PI2_MAP_EQ THENL
     [EXISTS_TAC `((singular_face 3 3 tau:(num->real)->A) o pi2_tri) o pi2_swap`;
      EXISTS_TAC `(singular_face 3 0 tau:(num->real)->A) o pi2_tri`;
      EXISTS_TAC `((singular_face 3 2 tau:(num->real)->A) o pi2_tri) o pi2_rotate`;
      EXISTS_TAC `pi2_reverse((singular_face 3 1 tau:(num->real)->A) o pi2_tri)`] THEN
    ASM_REWRITE_TAC[] THEN PI2_FACE_CELLS_TAC;
    STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS
     `pi2_class top a (((singular_face 3 3 tau:(num->real)->A) o pi2_tri) o pi2_swap)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PI2_CLASS_EQ_ON THEN ASM_REWRITE_TAC[] THEN PI2_FACE_CELLS_TAC;
      ASM_SIMP_TAC[PI2_CLASS_EQ; PI2_SWAP_HOMOTOPIC]];
    MATCH_MP_TAC PI2_CLASS_EQ_ON THEN ASM_REWRITE_TAC[] THEN PI2_FACE_CELLS_TAC;
    TRANS_TAC EQ_TRANS
     `pi2_class top a (((singular_face 3 2 tau:(num->real)->A) o pi2_tri) o pi2_rotate)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PI2_CLASS_EQ_ON THEN ASM_REWRITE_TAC[] THEN PI2_FACE_CELLS_TAC;
      ASM_SIMP_TAC[PI2_CLASS_EQ; PI2_ROTATE_HOMOTOPIC]];
    MATCH_MP_TAC PI2_CLASS_EQ_ON THEN ASM_REWRITE_TAC[] THEN PI2_FACE_CELLS_TAC]);;

let PI2_HAT_ALGEBRA = prove
 (`!G (p0:A) p1 p2 p3.
        abelian_group G /\
        p0 IN group_carrier G /\ p1 IN group_carrier G /\
        p2 IN group_carrier G /\ p3 IN group_carrier G /\
        group_mul G (group_mul G (group_mul G (group_inv G p3) p0) p2)
                    (group_inv G p1) = group_id G
        ==> group_mul G (group_mul G p0 (group_inv G p1))
                        (group_mul G p2 (group_inv G p3)) = group_id G`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ABELIAN_GROUP_MUL_AC]) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[GROUP_INV; GROUP_MUL]);;

(* The homotopy addition theorem: for an edge-constant 3-simplex the         *)
(* alternating product of the classes of its faces is trivial.               *)

let PI2_HOMOTOPY_ADDITION = prove
 (`!top a (tau:(num->real)->A).
        edgeconst_simplex (3,top) a tau
        ==> group_mul (pi2_group(top,a))
              (group_mul (pi2_group(top,a))
                 (pi2_class top a (singular_face 3 0 tau o pi2_tri))
                 (group_inv (pi2_group(top,a))
                    (pi2_class top a (singular_face 3 1 tau o pi2_tri))))
              (group_mul (pi2_group(top,a))
                 (pi2_class top a (singular_face 3 2 tau o pi2_tri))
                 (group_inv (pi2_group(top,a))
                    (pi2_class top a (singular_face 3 3 tau o pi2_tri)))) =
            group_id (pi2_group(top,a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PI2_HAT_EDGE_CELLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PI2_HAT_FACE_CELLS) THEN
  SUBGOAL_THEN `!k. k <= 3 ==> pi2_map top a (singular_face 3 k (tau:(num->real)->A) o
                                               pi2_tri)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EDGECONST_SIMPLEX_PI2_MAP THEN
    MP_TAC(SPECL [`3`; `k:num`; `top:A topology`; `a:A`; `tau:(num->real)->A`]
                 EDGECONST_SIMPLEX_FACE) THEN
    ASM_REWRITE_TAC[ARITH_RULE `3 - 1 = 2`] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PI2_HAT_ALGEBRA THEN REWRITE_TAC[ABELIAN_PI2_GROUP] THEN
  ASM_SIMP_TAC[PI2_CLASS_IN_CARRIER; ARITH] THEN
  (* The class of tau o net is trivial. *)
  SUBGOAL_THEN `pi2_class top a ((tau:(num->real)->A) o pi2_net) =
                group_id(pi2_group(top,a))` MP_TAC THENL
   [SUBGOAL_THEN `(a:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[PI2_MAP_BASEPOINT]; ALL_TAC] THEN
    ASM_SIMP_TAC[PI2_GROUP] THEN
    MP_TAC(ISPECL
     [`subtopology (product_topology (:num) (\i. euclideanreal)) (standard_simplex 3)`;
      `top:A topology`; `pi2_bary (&1) (&0) (&0) (&0)`; `tau:(num->real)->A`;
      `pi2_net`; `\x:real#real. pi2_bary (&1) (&0) (&0) (&0)`]
     PI2_HOMOTOPIC_COMPOSE_LEFT) THEN
    REWRITE_TAC[PI2_NET_NULLHOMOTOPIC] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [edgeconst_simplex]) THEN
      SIMP_TAC[singular_simplex];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP EDGECONST_SIMPLEX_BASEPOINT) THEN
    SUBGOAL_THEN `(tau:(num->real)->A) o (\x:real#real. pi2_bary (&1) (&0) (&0) (&0)) =
                  (\x. a)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[EDGECONST_SIMPLEX_BASEPOINT];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PI2_CLASS_EQ
       (CONJUNCT1(MATCH_MP PI2_HOMOTOPIC_IMP_MAP th))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Decompose the net. *)
  REWRITE_TAC[pi2_net; PI2_JOIN3_COMPOSE; PI2_VJOIN3_COMPOSE] THEN
  ASM_SIMP_TAC[PI2_CLASS_JOIN3; PI2_CLASS_VJOIN3; PI2_MAP_VJOIN3] THEN
  SUBGOAL_THEN
    `!k. k <= 3 ==> pi2_class top a (singular_face 3 k (tau:(num->real)->A) o pi2_tri)
                    IN group_carrier(pi2_group(top,a))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PI2_CLASS_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pi2_class top a (singular_face 3 0 (tau:(num->real)->A) o pi2_tri)
      IN group_carrier(pi2_group(top,a)) /\
    pi2_class top a (singular_face 3 1 (tau:(num->real)->A) o pi2_tri)
      IN group_carrier(pi2_group(top,a)) /\
    pi2_class top a (singular_face 3 2 (tau:(num->real)->A) o pi2_tri)
      IN group_carrier(pi2_group(top,a)) /\
    pi2_class top a (singular_face 3 3 (tau:(num->real)->A) o pi2_tri)
      IN group_carrier(pi2_group(top,a))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_MUL_RID; GROUP_ID; GROUP_INV; GROUP_MUL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GROUP_MUL_LID THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV]);;

(* ========================================================================= *)
(* The inverse Hurewicz map on edge-constant 2-chains, which                 *)
(* kills boundaries of edge-constant 3-chains.                               *)
(* ========================================================================= *)

let PI2_CHAIN_BOUNDARY_3 = prove
 (`!tau:(num->real)->A.
        chain_boundary 3 (frag_of tau) =
        frag_add (frag_add (frag_of (singular_face 3 0 tau))
                           (frag_neg (frag_of (singular_face 3 1 tau))))
                 (frag_add (frag_of (singular_face 3 2 tau))
                           (frag_neg (frag_of (singular_face 3 3 tau))))`,
  GEN_TAC THEN REWRITE_TAC[CHAIN_BOUNDARY_OF] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NUMSEG_CONV `0..3`] THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; NEUTRAL_FRAG_ADD] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC FRAG_MODULE);;

let PI2_HOM_FRAG4 = prove
 (`!s G (h:(B)frag->C) f0 f1 f2 f3.
        group_homomorphism (free_abelian_group s,G) h /\
        f0 IN s /\ f1 IN s /\ f2 IN s /\ f3 IN s
        ==> h(frag_add (frag_add (frag_of f0) (frag_neg (frag_of f1)))
                       (frag_add (frag_of f2) (frag_neg (frag_of f3)))) =
            group_mul G (group_mul G (h(frag_of f0)) (group_inv G (h(frag_of f1))))
                        (group_mul G (h(frag_of f2)) (group_inv G (h(frag_of f3))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frag_add (frag_add (frag_of f0) (frag_neg (frag_of f1)))
             (frag_add (frag_of f2) (frag_neg (frag_of (f3:B)))) =
    group_mul (free_abelian_group s)
      (group_mul (free_abelian_group s) (frag_of f0)
         (group_inv (free_abelian_group s) (frag_of f1)))
      (group_mul (free_abelian_group s) (frag_of f2)
         (group_inv (free_abelian_group s) (frag_of f3)))`
  SUBST1_TAC THENL [REWRITE_TAC[FREE_ABELIAN_GROUP]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP GROUP_HOMOMORPHISM_MUL th;
                                     MATCH_MP GROUP_HOMOMORPHISM_INV th;
                                     GROUP_MUL; GROUP_INV;
                                     FRAG_OF_IN_FREE_ABELIAN_GROUP]));;

let PI2_HUREWICZ_INVERSE = prove
 (`!top a:A.
        a IN topspace top
        ==> ?h. group_homomorphism
                  (free_abelian_group (edgeconst_simplex (2,top) a),pi2_group(top,a)) h /\
                (!f. edgeconst_simplex (2,top) a f
                     ==> h(frag_of f) = pi2_class top a (f o pi2_tri)) /\
                (!c. frag_support c SUBSET edgeconst_simplex (3,top) a
                     ==> h(chain_boundary 3 c) = group_id(pi2_group(top,a)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\f:(num->real)->A. pi2_class top a (f o pi2_tri)`;
                 `edgeconst_simplex (2,top) (a:A)`; `pi2_group(top,a:A)`]
         FREE_ABELIAN_GROUP_UNIVERSAL) THEN
  REWRITE_TAC[ABELIAN_PI2_GROUP] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `f:(num->real)->A` THEN
    DISCH_TAC THEN MATCH_MP_TAC PI2_CLASS_IN_CARRIER THEN
    MATCH_MP_TAC EDGECONST_SIMPLEX_PI2_MAP THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:((num->real)->A)frag->(real#real->A)->bool`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:((num->real)->A)frag->(real#real->A)->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN group_carrier(free_abelian_group (edgeconst_simplex (3,top) (a:A)))
        ==> chain_boundary 3 c IN
              group_carrier(free_abelian_group (edgeconst_simplex (2,top) a)) /\
            h(chain_boundary 3 c) = group_id(pi2_group(top,a))`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC FREE_ABELIAN_GROUP_INDUCT THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ r ==> p /\ q /\ r`) THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THENL
   [REWRITE_TAC[CHAIN_BOUNDARY_0] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM; FRAG_SUPPORT_0; EMPTY_SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [group_homomorphism]) THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP];
    MAP_EVERY X_GEN_TAC [`x:((num->real)->A)frag`; `y:((num->real)->A)frag`] THEN
    STRIP_TAC THEN REWRITE_TAC[CHAIN_BOUNDARY_SUB] THEN
    SUBGOAL_THEN
     `frag_sub (chain_boundary 3 x) (chain_boundary 3 y) =
      group_mul (free_abelian_group (edgeconst_simplex (2,top) (a:A)))
                (chain_boundary 3 x)
                (group_inv (free_abelian_group (edgeconst_simplex (2,top) a))
                           (chain_boundary 3 y))` SUBST1_TAC THENL
     [REWRITE_TAC[FREE_ABELIAN_GROUP] THEN CONV_TAC FRAG_MODULE; ALL_TAC] THEN
    ASM_SIMP_TAC[GROUP_MUL; GROUP_INV] THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP GROUP_HOMOMORPHISM_MUL th;
                                       MATCH_MP GROUP_HOMOMORPHISM_INV th;
                                       GROUP_INV]) THEN
    SIMP_TAC[GROUP_INV_ID; GROUP_MUL_LID; GROUP_ID];
    X_GEN_TAC `tau:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
    REWRITE_TAC[PI2_CHAIN_BOUNDARY_3] THEN
    SUBGOAL_THEN `!k. k <= 3 ==> edgeconst_simplex (2,top) (a:A) (singular_face 3 k tau)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`3`; `k:num`; `top:A topology`; `a:A`; `tau:(num->real)->A`]
                   EDGECONST_SIMPLEX_FACE) THEN
      ASM_REWRITE_TAC[ARITH_RULE `3 - 1 = 2`] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN
      REPEAT(MATCH_MP_TAC(SET_RULE
        `frag_support (frag_add (x:((num->real)->A)frag) y) SUBSET
           frag_support x UNION frag_support y /\
         frag_support x SUBSET s /\ frag_support y SUBSET s
         ==> frag_support (frag_add x y) SUBSET s`) THEN
       REWRITE_TAC[FRAG_SUPPORT_ADD] THEN CONJ_TAC) THEN
      REWRITE_TAC[FRAG_SUPPORT_NEG; FRAG_SUPPORT_OF; SING_SUBSET] THEN
      REWRITE_TAC[IN] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`edgeconst_simplex (2,top) (a:A)`; `pi2_group(top,a:A)`;
                   `h:((num->real)->A)frag->(real#real->A)->bool`;
                   `singular_face 3 0 (tau:(num->real)->A)`;
                   `singular_face 3 1 (tau:(num->real)->A)`;
                   `singular_face 3 2 (tau:(num->real)->A)`;
                   `singular_face 3 3 (tau:(num->real)->A)`] PI2_HOM_FRAG4) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
    SUBGOAL_THEN
     `edgeconst_simplex (2,top) (a:A) (singular_face 3 0 tau) /\
      edgeconst_simplex (2,top) a (singular_face 3 1 tau) /\
      edgeconst_simplex (2,top) a (singular_face 3 2 tau) /\
      edgeconst_simplex (2,top) a (singular_face 3 3 tau)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC PI2_HOMOTOPY_ADDITION THEN
    ASM_REWRITE_TAC[]]);;

