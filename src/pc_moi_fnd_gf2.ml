(* ========================================================================= *)
(* pc_moi_fnd_gf2: counting over GF(2) for parity incidence maps.  Used by   *)
(* pc_moi_fnd_z2 (Z2_COCYCLE_NONSPHERE_BOUNDARY) and pc_moi_s33_z2a (H^1     *)
(* counts of surfaces).  Polymorphic; no geometry.                           *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Counting over GF(2).  Symmetric differences, parity incidence maps        *)
(* (additive), and CARD G = CARD kernel * CARD image for additive maps on a  *)
(* finite family of sets closed under symmetric difference.                  *)
(* ------------------------------------------------------------------------- *)

let moi_fz2_sd = new_definition
 `moi_fz2_sd (x:A->bool) y = (x DIFF y) UNION (y DIFF x)`;;

let moi_fz2_pm = new_definition
 `moi_fz2_pm (r:A->B->bool) (ys:B->bool) (x:A->bool) =
    {y | y IN ys /\ ODD (CARD {a | a IN x /\ r a y})}`;;

let MOI_FZ2_IN_SD = prove
 (`!(z:A) s t. z IN moi_fz2_sd s t <=> ~(z IN s <=> z IN t)`,
  REWRITE_TAC[moi_fz2_sd; IN_UNION; IN_DIFF] THEN MESON_TAC[]);;

let MOI_FZ2_SD = prove
 (`!x y z:A->bool.
     moi_fz2_sd x {} = x /\ moi_fz2_sd {} x = x /\ moi_fz2_sd x x = {} /\
     moi_fz2_sd x y = moi_fz2_sd y x /\
     moi_fz2_sd (moi_fz2_sd x y) z = moi_fz2_sd x (moi_fz2_sd y z) /\
     moi_fz2_sd (moi_fz2_sd x y) y = x /\
     (moi_fz2_sd x y = {} <=> x = y) /\
     moi_fz2_sd x y SUBSET x UNION y`,
  REWRITE_TAC[moi_fz2_sd] THEN SET_TAC[]);;

let MOI_FZ2_SD_PARITY = prove
 (`!s t:A->bool.
     FINITE s /\ FINITE t
     ==> (ODD (CARD (moi_fz2_sd s t)) <=> ~(ODD (CARD s) <=> ODD (CARD t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fz2_sd] THEN
  SUBGOAL_THEN `CARD (s:A->bool) + CARD (t:A->bool) =
                CARD ((s DIFF t) UNION (t DIFF s)) + 2 * CARD (s INTER t)` MP_TAC THENL
   [SUBGOAL_THEN `CARD (s:A->bool) = CARD (s DIFF t) + CARD (s INTER t) /\
                  CARD (t:A->bool) = CARD (t DIFF s) + CARD (s INTER t)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `CARD ((s DIFF t) UNION (t DIFF s):A->bool) =
                  CARD (s DIFF t) + CARD (t DIFF s)` SUBST1_TAC THENL
     [MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN CONV_TAC TAUT);;

(* Parity incidence maps are additive and vanish on the empty set. *)

let MOI_FZ2_PM_SD = prove
 (`!(r:A->B->bool) ys x1 x2.
     (!y. y IN ys ==> FINITE {a | r a y})
     ==> moi_fz2_pm r ys (moi_fz2_sd x1 x2) =
         moi_fz2_sd (moi_fz2_pm r ys x1) (moi_fz2_pm r ys x2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:B. {a:A | a IN moi_fz2_sd x1 x2 /\ r a y} =
                      moi_fz2_sd {a | a IN x1 /\ r a y} {a | a IN x2 /\ r a y}`
  (fun th -> REWRITE_TAC[moi_fz2_pm; th]) THENL
   [REWRITE_TAC[moi_fz2_sd] THEN SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:B` THEN
  REWRITE_TAC[MOI_FZ2_IN_SD; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(y:B) IN ys` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FZ2_SD_PARITY THEN
  CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a:A | r a (y:B)}` THEN
  ASM_SIMP_TAC[] THEN SET_TAC[]);;

let MOI_FZ2_PM_EMPTY = prove
 (`!(r:A->B->bool) ys. moi_fz2_pm r ys {} = {}`,
  REWRITE_TAC[moi_fz2_pm; NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; ODD] THEN
  SET_TAC[]);;

let MOI_FZ2_PM_SUBSET = prove
 (`!(r:A->B->bool) ys x. moi_fz2_pm r ys x SUBSET ys`,
  REWRITE_TAC[moi_fz2_pm] THEN SET_TAC[]);;

(* Kernel times image. *)

let MOI_FZ2_KERNEL_IMAGE = prove
 (`!(G:(A->bool)->bool) (f:(A->bool)->(B->bool)).
     FINITE G /\ (!x y. x IN G /\ y IN G ==> moi_fz2_sd x y IN G) /\
     (!x y. x IN G /\ y IN G ==> f (moi_fz2_sd x y) = moi_fz2_sd (f x) (f y))
     ==> CARD G = CARD {x | x IN G /\ f x = {}} * CARD (IMAGE f G)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = {x | x IN G /\ (f:(A->bool)->(B->bool)) x = {}}` THEN
  SUBGOAL_THEN `FINITE (K:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x0. x0 IN G
         ==> {x | x IN G /\ (f:(A->bool)->(B->bool)) x = f x0} =
             IMAGE (\k. moi_fz2_sd k x0) K`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:A->bool` THEN DISCH_TAC THEN EXPAND_TAC "K" THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `moi_fz2_sd (x:A->bool) x0` THEN
      ASM_SIMP_TAC[MOI_FZ2_SD];
      DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[MOI_FZ2_SD]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (f:(A->bool)->(B->bool)) G
        ==> CARD {x | x IN G /\ f x = y} = CARD (K:(A->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x0:A->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MOI_FZ2_SD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(A->bool)->(B->bool)`; `\x:A->bool. 1`; `G:(A->bool)->bool`]
    NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. nsum {x | x IN G /\ (f:(A->bool)->(B->bool)) x = y} (\x. 1) =
                    CARD {x | x IN G /\ f x = y}` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_EQ_NSUM THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CARD_EQ_NSUM] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `nsum (IMAGE (f:(A->bool)->(B->bool)) G) (\y. CARD {x | x IN G /\ f x = y}) =
                nsum (IMAGE f G) (\y. CARD (K:(A->bool)->bool))` SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CONST; FINITE_IMAGE] THEN REWRITE_TAC[MULT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Parity of finite sums and double counting mod 2.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_FZ2_NSUM_PARITY = prove
 (`!(n:A->num) s.
     FINITE s ==> (EVEN (nsum s n) <=> EVEN (CARD {x | x IN s /\ ODD (n x)}))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NSUM_CLAUSES; NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; EVEN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NSUM_CLAUSES] THEN
  SUBGOAL_THEN `FINITE {x | x IN s /\ ODD ((n:A->num) x)} /\
                ~((a:A) IN {x | x IN s /\ ODD (n x)})` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `ODD ((n:A->num) a)` THENL
   [SUBGOAL_THEN `{x | x IN a INSERT s /\ ODD ((n:A->num) x)} =
                  a INSERT {x | x IN s /\ ODD (n x)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; EVEN_ADD; EVEN] THEN ASM_MESON_TAC[NOT_EVEN]];
    SUBGOAL_THEN `{x | x IN a INSERT s /\ ODD ((n:A->num) x)} =
                  {x | x IN s /\ ODD (n x)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[EVEN_ADD] THEN ASM_MESON_TAC[NOT_EVEN]]]);;

let MOI_FZ2_DOUBLE_EVEN = prove
 (`!(r:A->B->bool) s t.
     FINITE s /\ FINITE t /\
     (!x. x IN s ==> EVEN (CARD {y | y IN t /\ r x y}))
     ==> EVEN (CARD {y | y IN t /\ ODD (CARD {x | x IN s /\ r x y})})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\y:B. CARD {x:A | x IN s /\ r x y}`; `t:B->bool`]
    MOI_FZ2_NSUM_PARITY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `nsum t (\y:B. CARD {x:A | x IN s /\ r x y}) =
                nsum s (\x. CARD {y | y IN t /\ r x y})` SUBST1_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`\(y:B) (x:A). (r:A->B->bool) x y`; `\(y:B) (x:A). 1`;
                             `t:B->bool`; `s:A->bool`] NSUM_NSUM_RESTRICT)) THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_NSUM; FINITE_RESTRICT];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\x:A. CARD {y:B | y IN t /\ r x y}`; `s:A->bool`]
    MOI_FZ2_NSUM_PARITY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `{x:A | x IN s /\ ODD (CARD {y:B | y IN t /\ r x y})} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; GSYM NOT_EVEN] THEN ASM_MESON_TAC[];
    REWRITE_TAC[CARD_CLAUSES; EVEN]]);;

(* ------------------------------------------------------------------------- *)
(* Power sets, images closed under symmetric difference, even subsets (their *)
(* number, and generation by pairs).                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_FZ2_POW_SD = prove
 (`!(s:A->bool) x y. x SUBSET s /\ y SUBSET s ==> moi_fz2_sd x y SUBSET s`,
  REWRITE_TAC[moi_fz2_sd] THEN SET_TAC[]);;

let MOI_FZ2_KERNEL_IMAGE_POW = prove
 (`!(s:A->bool) (f:(A->bool)->(B->bool)).
     FINITE s /\
     (!x y. x SUBSET s /\ y SUBSET s ==> f (moi_fz2_sd x y) = moi_fz2_sd (f x) (f y))
     ==> 2 EXP CARD s =
         CARD {x | x SUBSET s /\ f x = {}} * CARD (IMAGE f {x | x SUBSET s})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM CARD_POWERSET] THEN
  MP_TAC(ISPECL [`{x:A->bool | x SUBSET s}`; `f:(A->bool)->(B->bool)`]
    MOI_FZ2_KERNEL_IMAGE) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; IN_ELIM_THM; MOI_FZ2_POW_SD] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM]);;

let MOI_FZ2_IMAGE_SD = prove
 (`!(G:(A->bool)->bool) (f:(A->bool)->(B->bool)) u v.
     (!x y. x IN G /\ y IN G ==> moi_fz2_sd x y IN G) /\
     (!x y. x IN G /\ y IN G ==> f (moi_fz2_sd x y) = moi_fz2_sd (f x) (f y)) /\
     u IN IMAGE f G /\ v IN IMAGE f G
     ==> moi_fz2_sd u v IN IMAGE f G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
  EXISTS_TAC `moi_fz2_sd (x:A->bool) x'` THEN ASM_SIMP_TAC[]);;

let MOI_FZ2_EVEN_SUBSETS = prove
 (`!y:A->bool.
     FINITE y /\ ~(y = {})
     ==> CARD {x | x SUBSET y /\ EVEN (CARD x)} = 2 EXP (CARD y - 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `CARD (y DELETE (a:A)) = CARD y - 1` (SUBST1_TAC o SYM) THENL
   [ASM_SIMP_TAC[CARD_DELETE]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CARD_POWERSET; FINITE_DELETE] THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\x:A->bool. x DELETE a`;
    `\w:A->bool. if EVEN (CARD w) then w else (a:A) INSERT w`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[FINITE_POWERSET; FINITE_DELETE; ASSUME `FINITE (y:A->bool)`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE (x:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(a:A) IN x` THENL
     [ASM_SIMP_TAC[CARD_DELETE] THEN
      SUBGOAL_THEN `~EVEN (CARD (x:A->bool) - 1)` (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[EVEN_SUB; ARITH] THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(CARD (x:A->bool) = 0) /\ ~(CARD x = 1)` MP_TAC THENL
         [CONJ_TAC THENL
           [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
            DISCH_TAC THEN UNDISCH_TAC `EVEN (CARD (x:A->bool))` THEN
            ASM_REWRITE_TAC[ARITH]];
          ARITH_TAC];
        ASM SET_TAC[]];
      SUBGOAL_THEN `(x:A->bool) DELETE a = x` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]]];
    X_GEN_TAC `w:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE (w:A->bool) /\ ~((a:A) IN w)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DELETE]; ASM SET_TAC[]];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM SET_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; EVEN] THEN ASM SET_TAC[]]]);;

(* A family closed under symmetric difference that contains {} and all     *)
(* pairs of distinct points of y contains every even subset of y.           *)

let MOI_FZ2_EVEN_GEN = prove
 (`!(G:(A->bool)->bool) y.
     FINITE y /\ {} IN G /\
     (!u v. u IN G /\ v IN G ==> moi_fz2_sd u v IN G) /\
     (!a b. a IN y /\ b IN y /\ ~(a = b) ==> {a,b} IN G)
     ==> !x. x SUBSET y /\ EVEN (CARD x) ==> x IN G`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "SD") (LABEL_TAC "PR")))) THEN
  SUBGOAL_THEN `!n x:A->bool. CARD x = n /\ x SUBSET y /\ EVEN n ==> x IN G`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `x:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (x:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `x:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `?b:A. b IN x /\ ~(b = a)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `x = {a:A}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `EVEN n` THEN EXPAND_TAC "n" THEN REWRITE_TAC[CARD_SING; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:A,b} SUBSET x /\ CARD {a:A,b} = 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (x DIFF {a:A,b}) = n - 2 /\ 2 <= n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    MP_TAC(ISPECL [`{a:A,b}`; `x:A->bool`] CARD_SUBSET) THEN
    ASM_SIMP_TAC[CARD_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `x = moi_fz2_sd (x DIFF {a:A,b}) {a,b}` SUBST1_TAC THENL
   [REWRITE_TAC[moi_fz2_sd] THEN ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "SD" MATCH_MP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; USE_THEN "PR" MATCH_MP_TAC THEN ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[EVEN_SUB; ARITH] THEN ASM SET_TAC[]);;

