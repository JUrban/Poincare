(* ========================================================================= *)
(* Unit pc_rfa_hpush: the pointwise "positive push" of the maximum principle *)
(* for the perturbed Harnack quadratic: array identities and inequalities at *)
(* a null vector.                                                            *)
(* ========================================================================= *)

needs "src/pc_rfa_hext.ml";;
needs "src/pc_rfa_halg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The change of J under the perturbation (RFA_HJ_PERTURB):                  *)
(* J(R + alpha I, P, M + beta delta) - J(R, P, M) in closed form, for        *)
(* arbitrary arrays and antisymmetric u.                                     *)
(* ========================================================================= *)

let RFA_ARRAY_POLY_PROVE anti tm =
  (* tm: an equation between array expressions over 1..3; anti: |- !i j. u i j = --(u j i) *)
  let u_f = rator(rator(lhs(snd(strip_forall(concl anti))))) in
  let nm = mk_small_numeral in
  let hook t =
    match strip_comb t with
      (f, [i; j]) when f = u_f ->
        let a = dest_small_numeral i and b = dest_small_numeral j in
        if a > b then ISPECL [i; j] anti
        else if a = b then MP (ISPEC t RFA_UDIAG) (ISPECL [i; j] anti)
        else failwith "canonical"
    | _ -> failwith "atom" in
  let saved = RFA_ENGINE_SAVE () in
  RFA_ENGINE_RESET ();
  rfa_mp_hook := (fun t -> try hook t with Failure s -> failwith s
                                        | Match_failure _ -> failwith "atom");
  let res =
    try
      let ev t = let th1 = (REWRITE_CONV[rfa_hj; rfa_i4; rfa_kd] THENC DEPTH_CONV BETA_CONV) t in
                 TRANS th1 (RFA_MPOLY (rand(concl th1))) in
      let thl = ev (lhs tm) and thr = ev (rhs tm) in
      if aconv (rand(concl thl)) (rand(concl thr)) then TRANS thl (SYM thr)
      else failwith "RFA_ARRAY_POLY_PROVE: normal forms"
    with e -> (RFA_ENGINE_RESTORE saved; raise e) in
  RFA_ENGINE_RESTORE saved; res;;

let RFA_HJ_PERTURB = prove
 (`!(R:num->num->num->num->real) P M (u:num->num->real) w alpha beta.
     (!i j. u i j = --(u j i))
     ==> rfa_hj 3 (\a b c d. R a b c d + alpha * rfa_i4 a b c d) P
                  (\a b. M a b + beta * rfa_kd a b) u w =
         rfa_hj 3 R P M u w +
         alpha * (sum(1..3) (\a. M a a) * sum(1..3) (\a. w a pow 2) -
                  sum(1..3) (\a. sum(1..3) (\b. M b a * w a * w b))) +
         &2 * beta * sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. R a c c b * w a * w b))) +
         &2 * alpha * beta * sum(1..3) (\a. w a pow 2) +
         &4 * alpha * (sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\d. u a b * w a * P d b d))) -
                       sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. u a b * P c b a * w c)))) +
         &4 * alpha * sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                 sum(1..3) (\e. sum(1..3) (\f.
                   (rfa_i4 a e f c * R b e f d + R a e f c * rfa_i4 b e f d) *
                   u a b * u c d)))))) +
         alpha pow 2 * sum(1..3) (\a. sum(1..3) (\b. u a b pow 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  W(fun (asl, w) -> ACCEPT_TAC (RFA_ARRAY_POLY_PROVE (snd(hd asl)) w)));;

(* ========================================================================= *)
(* The polarization of rfa_hz (rfa_hzb, RFA_HZ_POLAR) and the                *)
(* bilinear null condition of a positive semidefinite form at a null vector *)
(* (RFA_HZ_NULL_BIL).                                                        *)
(* ========================================================================= *)

let rfa_hzb = new_definition
 `rfa_hzb (n:num) (R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
          (u:num->num->real) (w:num->real) (x:num->num->real) (y:num->real) =
    inv(&2) * sum(1..n) (\a. sum(1..n) (\b. M a b * (w a * y b + y a * w b))) +
    sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. P a b c * (u a b * y c + x a b * w c)))) +
    inv(&2) * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
                R a b c d * (u a b * x d c + x a b * u d c)))))`;;

let RFA_HZ_POLAR = prove
 (`!(R:num->num->num->num->real) P M (u:num->num->real) w x y t.
     rfa_hz 3 R P M (\i j. u i j + t * x i j) (\i. w i + t * y i) =
     rfa_hz 3 R P M u w + &2 * t * rfa_hzb 3 R P M u w x y + t pow 2 * rfa_hz 3 R P M x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hz; rfa_hzb; SUM_3] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC REAL_RING);;

let RFA_QUAD_NULL = prove
 (`!B Q. (!t. &0 <= &2 * t * B + t pow 2 * Q) ==> B = &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k = abs Q + &1` THEN
  SUBGOAL_THEN `&0 < k /\ Q - &2 * k < &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--B / k`) THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < k ==> &2 * (--B / k) * B + (--B / k) pow 2 * Q =
                                      (B pow 2 * (Q - &2 * k)) / k pow 2`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_MUL_LZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `B pow 2 * (Q - &2 * k) = &0` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * c <= &0 <=> &0 <= x * --c`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC]);;

let RFA_HZ_NULL_BIL = prove
 (`!(R:num->num->num->num->real) P M (u:num->num->real) w x y.
     (!u' w'. (!i j. u' i j = --(u' j i)) ==> &0 <= rfa_hz 3 R P M u' w') /\
     (!i j. u i j = --(u j i)) /\ rfa_hz 3 R P M u w = &0 /\
     (!i j. x i j = --(x j i))
     ==> rfa_hzb 3 R P M u w x y = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "psd") (CONJUNCTS_THEN2 (LABEL_TAC "au")
    (CONJUNCTS_THEN2 (LABEL_TAC "null") (LABEL_TAC "ax")))) THEN
  MATCH_MP_TAC RFA_QUAD_NULL THEN
  EXISTS_TAC `rfa_hz 3 R P M x y` THEN X_GEN_TAC `t:real` THEN
  REMOVE_THEN "psd" (MP_TAC o SPECL [`\i j. (u:num->num->real) i j + t * x i j`;
                                     `\i. (w:num->real) i + t * y i`]) THEN
  REWRITE_TAC[RFA_HZ_POLAR] THEN REMOVE_THEN "null" SUBST1_TAC THEN
  REWRITE_TAC[REAL_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN BETA_TAC THEN
  USE_THEN "au" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  USE_THEN "ax" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RING);;

(* ========================================================================= *)
(* Array identities with symmetry hypotheses.  A normalizer for              *)
(* identities over 1..3 between expressions in arrays R (curvature-type     *)
(* symmetries), P (antisymmetric in its first two slots), M (symmetric) and *)
(* antisymmetric 2-arrays (RFA_SYM_ARRAY_PROVE); the perturbed polarization *)
(* (RFA_HZB_PERTURB) and the cancellation of the defect terms of U and W    *)
(* at a null vector (RFA_HV_CANCEL).                                        *)
(* ========================================================================= *)

(* syms: theorems of the forms
     !a b c d. R a b c d = --(R b a c d)   (and the cd and pair versions)
     !a b c. P a b c = --(P b a c)
     !a b. M a b = M b a
     !i j. u i j = --(u j i)
   classified by shape; the hook rewrites an atom at numeral indices to a
   canonical one (or zero). *)

let RFA_SYM_ARRAY_PROVE syms tm =
  let nm = mk_small_numeral in
  let info = map (fun th ->
    let vs, body = strip_forall (concl th) in
    let l = lhs body and r = rhs body in
    let f, args = strip_comb l in
    let neg = is_comb r && rator r = `(--):real->real` in
    let r' = if neg then rand r else r in
    let _, args' = strip_comb r' in
    let perm = map (fun a -> index a args) args' in
    (f, (th, length args, perm, neg))) syms in
  let apply_rule (th, n, perm, neg) vals =
    ISPECL (map nm vals) th in
  let hook t =
    let f, args = strip_comb t in
    let rules = map snd (filter (fun (g, _) -> g = f) info) in
    if rules = [] then failwith "atom" else
    let vals = map dest_small_numeral args in
    (* try each rule; use it when it strictly decreases the index list
       lexicographically, or proves zero when the permuted list is equal *)
    let try_rule (th, n, perm, neg) =
      if length vals <> n then failwith "arity" else
      let vals' = map (fun k -> el k vals) perm in
      if vals' < vals then apply_rule (th, n, perm, neg) vals
      else if vals' = vals && neg then MP (ISPEC t RFA_UDIAG) (apply_rule (th, n, perm, neg) vals)
      else failwith "no progress" in
    tryfind try_rule rules in
  let saved = RFA_ENGINE_SAVE () in
  RFA_ENGINE_RESET ();
  rfa_mp_hook := (fun t -> try hook t with Failure s -> failwith s
                                        | Match_failure _ -> failwith "atom"
                                        | Invalid_argument _ -> failwith "atom");
  let res =
    try
      let ev t = let th1 = (REWRITE_CONV[rfa_hj; rfa_hz; rfa_hzb; rfa_i4; rfa_kd] THENC
                            DEPTH_CONV BETA_CONV) t in
                 TRANS th1 (RFA_MPOLY (rand(concl th1))) in
      let thl = ev (lhs tm) and thr = ev (rhs tm) in
      if aconv (rand(concl thl)) (rand(concl thr)) then TRANS thl (SYM thr)
      else failwith "RFA_SYM_ARRAY_PROVE: normal forms"
    with e -> (RFA_ENGINE_RESTORE saved; raise e) in
  RFA_ENGINE_RESTORE saved; res;;

let RFA_SYM_ARRAY_TAC (asl, w) =
  let syms = filter (fun th -> try let _, b = strip_forall (concl th) in
                                   is_eq b && not (is_forall b)
                               with Failure _ -> false) (map snd asl) in
  ACCEPT_TAC (RFA_SYM_ARRAY_PROVE syms w) (asl, w);;

let RFA_HZB_PERTURB = prove
 (`!(R:num->num->num->num->real) P M (u:num->num->real) w x y alpha beta.
     (!i j. u i j = --(u j i)) /\ (!i j. x i j = --(x j i))
     ==> rfa_hzb 3 (\a b c d. R a b c d + alpha * rfa_i4 a b c d) P
                   (\a b. M a b + beta * rfa_kd a b) u w x y =
         rfa_hzb 3 R P M u w x y +
         alpha * sum(1..3) (\a. sum(1..3) (\b. u a b * x a b)) +
         beta * sum(1..3) (\a. w a * y a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RFA_SYM_ARRAY_TAC);;

let RFA_HV_ID = prove
 (`!(R:num->num->num->num->real) P M (u:num->num->real) w (h:num->num->real) k.
     (!a b c d. R a b c d = --(R b a c d)) /\ (!a b c d. R a b c d = --(R a b d c)) /\
     (!a b c d. R a b c d = R c d a b) /\ (!a b c. P a b c = --(P b a c)) /\
     (!a b. M a b = M b a) /\ (!i j. u i j = --(u j i))
     ==> sum(1..3) (\a. sum(1..3) (\b. M a b * k a * w b)) +
         sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. P a b c *
             (h a b * w c + u a b * k c)))) +
         sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
             R a b d c * h a b * u c d)))) =
         rfa_hzb 3 R P M u w (\i j. (h i j - h j i) / &2) k /\
         sum(1..3) (\a. sum(1..3) (\b. h a b * u a b)) =
         sum(1..3) (\a. sum(1..3) (\b. u a b * (h a b - h b a) / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN RFA_SYM_ARRAY_TAC);;

(* ========================================================================= *)
(* Generic bounds for quadratic expressions over 1..3 with                   *)
(* entrywise bounded coefficients (RFA_QB_WW, RFA_QB_UW, RFA_QB_UU), and the *)
(* bound |nabla U|^2 <= (18 K^2 + 1/(2 tau^2)) |W|^2 for the 1-jet (10.59)   *)
(* (RFA_DU_BOUND).                                                           *)
(* ========================================================================= *)

let RFA_SUM3_ABS = prove
 (`!f:num->real. abs(sum(1..3) f) <= sum(1..3) (\i. abs(f i))`,
  REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC);;

let RFA_AMGM2 = prove
 (`!x y. abs x * abs y <= (x pow 2 + y pow 2) / &2`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `abs x - abs y` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_ARITH `(a - b) pow 2 = a pow 2 - &2 * a * b + b pow 2`; REAL_POW2_ABS] THEN
  REAL_ARITH_TAC);;

let RFA_ABS_PROD_BOUND = prove
 (`!a x y B. abs a <= B ==> abs(a * x * y) <= B * (x pow 2 + y pow 2) / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * abs x * abs y` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM real_div; RFA_AMGM2]]);;

(* Entrywise bounded coefficients over 1..3.                                 *)

let RFA_SUM3_LE = prove
 (`!f g:num->real. (!i. 1 <= i /\ i <= 3 ==> f i <= g i) ==> sum(1..3) f <= sum(1..3) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_REWRITE_TAC[]);;

let RFA_ABS_SUM3_LE = prove
 (`!f g:num->real. (!i. 1 <= i /\ i <= 3 ==> abs(f i) <= g i) ==> abs(sum(1..3) f) <= sum(1..3) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\i. abs((f:num->real) i))` THEN
  REWRITE_TAC[RFA_SUM3_ABS] THEN MATCH_MP_TAC RFA_SUM3_LE THEN ASM_REWRITE_TAC[]);;

let RFA_QB_WW = prove
 (`!(A:num->num->real) B (w:num->real).
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(A a b) <= B)
     ==> abs(sum(1..3) (\a. sum(1..3) (\b. A a b * w a * w b))) <=
         &3 * B * sum(1..3) (\a. w a pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\a. sum(1..3) (\b. B * ((w:num->real) a pow 2 + w b pow 2) / &2))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC RFA_ABS_SUM3_LE THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
    MATCH_MP_TAC RFA_ABS_PROD_BOUND THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC]);;

let RFA_QB_UW = prove
 (`!(A:num->num->num->real) B (u:num->num->real) (w:num->real).
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 ==> abs(A a b c) <= B)
     ==> abs(sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. A a b c * u a b * w c)))) <=
         B * (&3 * sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) +
              &9 * sum(1..3) (\a. w a pow 2)) / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c.
                B * ((u:num->num->real) a b pow 2 + (w:num->real) c pow 2) / &2)))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC RFA_ABS_SUM3_LE THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
    MATCH_MP_TAC RFA_ABS_PROD_BOUND THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC]);;

let RFA_QB_UW2 = prove
 (`!(A:num->num->real) B (u:num->num->real) (w:num->real).
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(A a b) <= B)
     ==> abs(sum(1..3) (\a. sum(1..3) (\b. A a b * u a b * w a))) <=
         B * (sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) +
              &3 * sum(1..3) (\a. w a pow 2)) / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\a. sum(1..3) (\b.
                B * ((u:num->num->real) a b pow 2 + (w:num->real) a pow 2) / &2))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC RFA_ABS_SUM3_LE THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
    MATCH_MP_TAC RFA_ABS_PROD_BOUND THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC]);;

let RFA_QB_UU = prove
 (`!(A:num->num->num->num->real) B (u:num->num->real).
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3 ==> abs(A a b c d) <= B)
     ==> abs(sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
               A a b c d * u a b * u c d))))) <=
         &9 * B * sum(1..3) (\a. sum(1..3) (\b. u a b pow 2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                B * ((u:num->num->real) a b pow 2 + u c d pow 2) / &2))))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC RFA_ABS_SUM3_LE THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
    MATCH_MP_TAC RFA_ABS_PROD_BOUND THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC]);;

let RFA_SQ_ADD_LE = prove
 (`!x y. (x + y) pow 2 <= &2 * x pow 2 + &2 * y pow 2`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `x - y` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_ARITH `(a - b) pow 2 = a pow 2 - &2 * a * b + b pow 2`;
              REAL_ARITH `(a + b) pow 2 = a pow 2 + &2 * a * b + b pow 2`] THEN
  REAL_ARITH_TAC);;

let RFA_PROD_SQ_LE = prove
 (`!r w K. abs r <= K ==> (r * w) pow 2 <= K pow 2 * w pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let RFA_DU_TERM = prove
 (`!r1 r2 w1 w2 y K.
     abs r1 <= K /\ abs r2 <= K
     ==> (inv(&2) * (r1 * w1 - r2 * w2) + y) pow 2 <=
         (K pow 2 * w1 pow 2 + K pow 2 * w2 pow 2) + &2 * y pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (inv(&2) * (r1 * w1 - r2 * w2)) pow 2 + &2 * y pow 2` THEN
  REWRITE_TAC[RFA_SQ_ADD_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + z <= y + z`) THEN
  REWRITE_TAC[REAL_ARITH `&2 * (inv(&2) * x) pow 2 = inv(&2) * x pow 2`] THEN
  MP_TAC(SPECL [`r1 * w1:real`; `--(r2 * w2:real)`] RFA_SQ_ADD_LE) THEN
  MP_TAC(SPECL [`r1:real`; `w1:real`; `K:real`] RFA_PROD_SQ_LE) THEN
  MP_TAC(SPECL [`r2:real`; `w2:real`; `K:real`] RFA_PROD_SQ_LE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `x + --y = x - y`; REAL_ARITH `(--x) pow 2 = x pow 2`] THEN
  REAL_ARITH_TAC);;

let RFA_DU_BOUND = prove
 (`!(r:num->num->real) (w:num->real) tau K.
     &0 < tau /\ (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(r a b) <= K)
     ==> sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e.
           (inv(&2) * (r e a * w b - r e b * w a) +
            inv(&4 * tau) * ((if e = a then &1 else &0) * w b -
                             (if e = b then &1 else &0) * w a)) pow 2))) <=
         (&18 * K pow 2 + inv(&2 * tau pow 2)) * sum(1..3) (\a. w a pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e.
      (K pow 2 * (w:num->real) b pow 2 + K pow 2 * w a pow 2) +
      &2 * (inv(&4 * tau) * ((if e = a then &1 else &0) * w b -
                             (if e = b then &1 else &0) * w a)) pow 2)))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC RFA_SUM3_LE THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
    MATCH_MP_TAC RFA_DU_TERM THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < tau` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* Cauchy-Schwarz for 3x3 arrays (RFA_CS33), the bound on the                *)
(* cross gradient term |<grad q, grad N>| <= sigma psi0 (|U|^2 + |W|^2)      *)
(* from lgrad2 q <= C psi0^2 and |nabla U|^2 <= kappa |W|^2 (RFA_LGI_BOUND), *)
(* and |grad N|^2 <= 4 |U|^2 |nabla U|^2 in a frame (RFA_GRADN_BOUND).       *)
(* ========================================================================= *)

let RFA_DISCR = prove
 (`!A B C. &0 <= C /\ (!t. &0 <= A + &2 * t * B + t pow 2 * C) ==> B pow 2 <= A * C`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `C = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_CASES_TAC `B = &0` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--(abs A + &1) / (&2 * B)`) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(B = &0) ==> &2 * (x / (&2 * B)) * B = x`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--B / C`) THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < C ==> A + &2 * (--B / C) * B + (--B / C) pow 2 * C =
                                      (A * C - B pow 2) / C`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN REAL_ARITH_TAC);;

let RFA_CS33 = prove
 (`!(x:num->num->real) y.
     sum(1..3) (\a. sum(1..3) (\b. x a b * y a b)) pow 2 <=
     sum(1..3) (\a. sum(1..3) (\b. x a b pow 2)) * sum(1..3) (\a. sum(1..3) (\b. y a b pow 2))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_DISCR THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_3] THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_LE_POW_2))
     [`(y:num->num->real) 1 1`; `(y:num->num->real) 1 2`; `(y:num->num->real) 1 3`;
      `(y:num->num->real) 2 1`; `(y:num->num->real) 2 2`; `(y:num->num->real) 2 3`;
      `(y:num->num->real) 3 1`; `(y:num->num->real) 3 2`; `(y:num->num->real) 3 3`] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN
    MP_TAC(ISPECL [`1`; `3`; `\a. sum(1..3) (\b. ((x:num->num->real) a b + t * y a b) pow 2)`]
           SUM_POS_LE_NUMSEG) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> &0 <= a ==> &0 <= b`) THEN
    REWRITE_TAC[SUM_3] THEN CONV_TAC REAL_RING]);;

let RFA_LGI_BOUND = prove
 (`!lgi lgq lgN X Y Z C psi0 kappa sigma.
     lgi pow 2 <= lgq * lgN /\ &0 <= lgq /\ lgq <= C * psi0 pow 2 /\
     &0 <= lgN /\ lgN <= &4 * X * Z /\ &0 <= X /\ &0 <= Y /\ &0 <= Z /\
     Z <= kappa * Y /\ &0 <= C /\ &0 <= sigma /\ C * kappa <= sigma pow 2
     ==> abs lgi <= sigma * abs psi0 * (X + Y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[REAL_LE_SQUARE_ABS; REAL_ABS_REFL]
    `!a b. &0 <= b /\ a pow 2 <= b pow 2 ==> abs a <= b`) THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lgq * lgN` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C * psi0 pow 2) * (&4 * X * Z)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C * psi0 pow 2) * (&4 * X * kappa * Y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(sigma pow 2 * psi0 pow 2) * (&4 * X * Y)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(C * p) * (&4 * X * k * Y) = (C * k) * (p * (&4 * X * Y))`;
                REAL_ARITH `(s * p) * (&4 * X * Y) = s * (p * (&4 * X * Y))`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * X * Y <= (X + Y) pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `X - Y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REWRITE_TAC[]);;

let RFA_GRADN_BOUND = prove
 (`!(u:num->num->real) (du:num->num->num->real).
     sum(1..3) (\e. (&2 * sum(1..3) (\a. sum(1..3) (\b. u a b * du a b e))) pow 2) <=
     &4 * sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) *
     sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e. du a b e pow 2)))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `X = sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2))` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\e. &4 * X *
                sum(1..3) (\a. sum(1..3) (\b. (du:num->num->num->real) a b e pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_SUM3_LE THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`u:num->num->real`; `\a b. (du:num->num->num->real) a b i`] RFA_CS33) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The bound on the change of J under the perturbation                       *)
(* (RFA_DJ_BOUND), from entrywise bounds KR, KP, KM of the arrays R, P, M:   *)
(*   J(R + alpha I, P, M + beta g) - J(R, P, M) <=                           *)
(*     alpha (6 KM + 36 KP + 2 beta) |w|^2 + 18 beta KR |w|^2 +              *)
(*     alpha (12 KP + 324 KR + alpha) |u|^2.                                 *)
(* ========================================================================= *)

let RFA_I4_ABS = prove
 (`!a b c d. abs(rfa_i4 a b c d) <= inv(&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_i4] THEN
  REPEAT COND_CASES_TAC THEN REAL_ARITH_TAC);;

let RFA_MUL_ABS_LE = prove
 (`!c x B. &0 <= c /\ abs x <= B ==> c * x <= c * B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let RFA_MUL_ABS_LE2 = prove
 (`!c x B. &0 <= c /\ abs x <= B ==> c * x <= c * B /\ --(c * x) <= c * B`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `--(c * x) = c * --x`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let RFA_DJ_BOUND = prove
 (`!(R:num->num->num->num->real) P M (u:num->num->real) w alpha beta KR KP KM.
     (!i j. u i j = --(u j i)) /\ &0 <= alpha /\ &0 <= beta /\
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3 ==> abs(R a b c d) <= KR) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(P a b c) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(M a b) <= KM)
     ==> rfa_hj 3 (\a b c d. R a b c d + alpha * rfa_i4 a b c d) P
                  (\a b. M a b + beta * rfa_kd a b) u w - rfa_hj 3 R P M u w <=
         alpha * (&6 * KM + &36 * KP + &2 * beta) * sum(1..3) (\a. w a pow 2) +
         &18 * beta * KR * sum(1..3) (\a. w a pow 2) +
         alpha * (&12 * KP + &324 * KR + alpha) *
         sum(1..3) (\a. sum(1..3) (\b. u a b pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "R")
    (CONJUNCTS_THEN2 (LABEL_TAC "P") (LABEL_TAC "M")))))) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RFA_HJ_PERTURB th]) THEN
  REWRITE_TAC[REAL_ARITH `(x + y) - x = y`] THEN
  ABBREV_TAC `X = sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2))` THEN
  ABBREV_TAC `Y = sum(1..3) (\a. (w:num->real) a pow 2)` THEN
  SUBGOAL_THEN `&0 <= X /\ &0 <= Y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN REWRITE_TAC[SUM_3] THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_LE_POW_2))
     [`(u:num->num->real) 1 1`; `(u:num->num->real) 1 2`; `(u:num->num->real) 1 3`;
      `(u:num->num->real) 2 1`; `(u:num->num->real) 2 2`; `(u:num->num->real) 2 3`;
      `(u:num->num->real) 3 1`; `(u:num->num->real) 3 2`; `(u:num->num->real) 3 3`;
      `(w:num->real) 1`; `(w:num->real) 2`; `(w:num->real) 3`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= KR /\ &0 <= KP /\ &0 <= KM` STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "R" (MP_TAC o SPECL [`1`; `1`; `1`; `1`]) THEN
    REMOVE_THEN "P" (MP_TAC o SPECL [`1`; `1`; `1`]) THEN
    REMOVE_THEN "M" (MP_TAC o SPECL [`1`; `1`]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the trace of M and M(w,w) *)
  SUBGOAL_THEN `abs(sum(1..3) (\a. (M:num->num->real) a a)) <= &3 * KM` ASSUME_TAC THENL
   [REWRITE_TAC[SUM_3] THEN
    USE_THEN "M" (MP_TAC o SPECL [`1`; `1`]) THEN
    USE_THEN "M" (MP_TAC o SPECL [`2`; `2`]) THEN
    USE_THEN "M" (MP_TAC o SPECL [`3`; `3`]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(1..3) (\a. sum(1..3) (\b. (M:num->num->real) b a * w a * w b))) <=
                &3 * KM * Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN
    MP_TAC(ISPECL [`\a b. (M:num->num->real) b a`; `KM:real`; `w:num->real`] RFA_QB_WW) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    USE_THEN "M" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Ric(w,w) *)
  SUBGOAL_THEN
   `abs(sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c.
        (R:num->num->num->num->real) a c c b * w a * w b)))) <= &3 * (&3 * KR) * Y`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUM_RMUL] THEN EXPAND_TAC "Y" THEN
    MP_TAC(ISPECL [`\a b. sum(1..3) (\c. (R:num->num->num->num->real) a c c b)`;
                   `&3 * KR`; `w:num->real`] RFA_QB_WW) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUM_3] THEN
    SUBGOAL_THEN `!c. 1 <= c /\ c <= 3 ==> abs((R:num->num->num->num->real) a c c b) <= KR`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
                         MP_TAC(SPEC `3` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the P terms *)
  SUBGOAL_THEN
   `abs(sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\d.
        (u:num->num->real) a b * w a * (P:num->num->num->real) d b d)))) <=
    (&3 * KP) * (X + &3 * Y) / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\d.
          (u:num->num->real) a b * w a * (P:num->num->num->real) d b d))) =
      sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\d. P d b d) * u a b * w a))`
    SUBST1_TAC THENL [REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    MP_TAC(ISPECL [`\(a:num) (b:num). sum(1..3) (\d. (P:num->num->num->real) d b d)`;
                   `&3 * KP`; `u:num->num->real`; `w:num->real`] RFA_QB_UW2) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUM_3] THEN
    SUBGOAL_THEN `!d. 1 <= d /\ d <= 3 ==> abs((P:num->num->num->real) d b d) <= KP`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "P" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
                         MP_TAC(SPEC `3` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c.
        (u:num->num->real) a b * (P:num->num->num->real) c b a * w c)))) <=
    KP * (&3 * X + &9 * Y) / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c.
          (u:num->num->real) a b * (P:num->num->num->real) c b a * w c))) =
      sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. P c b a * u a b * w c)))`
    SUBST1_TAC THENL [REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    MP_TAC(ISPECL [`\a b c. (P:num->num->num->real) c b a`;
                   `KP:real`; `u:num->num->real`; `w:num->real`] RFA_QB_UW) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    USE_THEN "P" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the I.R + R.I term *)
  SUBGOAL_THEN
   `abs(sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
        sum(1..3) (\e. sum(1..3) (\f.
          (rfa_i4 a e f c * (R:num->num->num->num->real) b e f d +
           R a e f c * rfa_i4 b e f d) * (u:num->num->real) a b * u c d))))))) <=
    &9 * (&9 * KR) * X`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUM_RMUL] THEN EXPAND_TAC "X" THEN
    MP_TAC(ISPECL [`\a b c d. sum(1..3) (\e. sum(1..3) (\f.
                      rfa_i4 a e f c * (R:num->num->num->num->real) b e f d +
                      R a e f c * rfa_i4 b e f d))`;
                   `&9 * KR`; `u:num->num->real`] RFA_QB_UU) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..3) (\e:num. sum(1..3) (\f:num. KR))` THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC RFA_ABS_SUM3_LE THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= k / &2 /\ abs y <= k / &2 ==> abs(x + y) <= k`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x <= inv(&2) * k ==> x <= k / &2`) THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; RFA_I4_ABS] THEN
        USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `x <= k * inv(&2) ==> x <= k / &2`) THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; RFA_I4_ABS] THEN
        USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* combine *)
  SUBGOAL_THEN `sum(1..3) (\a. (M:num->num->real) a a) * Y <= (&3 * KM) * Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP REAL_LE_LMUL (CONJ (ASSUME `&0 <= alpha`)
    (ASSUME `sum(1..3) (\a. (M:num->num->real) a a) * Y <= (&3 * KM) * Y`))) THEN
  W(fun (asl, w) ->
    let abss = map (concl o snd) (filter (fun (_, th) ->
                 let c = concl th in is_binary "real_le" c &&
                 (try rator(lhand c) = `abs:real->real` with Failure _ -> false)) asl) in
    let facts c_t = map (fun c ->
      MATCH_MP RFA_MUL_ABS_LE2 (CONJ (ASSUME (mk_binary "real_le" (`&0`, c_t))) (ASSUME c)))
      abss in
    MAP_EVERY (fun c_t -> MAP_EVERY MP_TAC (facts c_t)) [`alpha:real`; `beta:real`]) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The scalar push (RFA_PUSH_SCALAR).  At a touching point the               *)
(* tested quantity is bounded below by kX |u|^2 + kY |w|^2, with kX, kY the  *)
(* coefficients left after the bounds on DeltaJ, |nabla U|^2, Lap q and the *)
(* cross gradient term; it is positive when kX, kY > 0 and (u, w) is not 0.  *)
(* ========================================================================= *)

let RFA_PUSH_SCALAR = prove
 (`!X Y Zn J0 Jh DX DY EY Qsq MP tau a b c alpha beta ce psi0 B A L C sigma kappa lapq lgi.
     &0 <= X /\ &0 <= Y /\ &0 < X + Y /\ Zn <= kappa * Y /\
     &0 <= Jh /\
     Jh - J0 <= alpha * (DY + &2 * beta) * Y + EY * beta * Y + alpha * (DX + alpha) * X /\
     &0 <= Qsq /\ &0 <= alpha /\ &0 <= ce /\
     alpha = a + c /\ beta = b + c /\ c = ce * psi0 /\
     MP = --(beta * Y) /\
     lapq <= C * psi0 /\ abs lgi <= sigma * psi0 * (X + Y) /\
     &0 < B * a - alpha * (DX + alpha) + (L - &2 * C - &2 * sigma) * c /\
     &0 < &2 / tau * beta + A * b - b / tau - alpha * (DY + &2 * beta) - EY * beta -
          &2 * alpha * kappa + (L - &2 * C - &2 * sigma) * c
     ==> &0 < J0 + Qsq - &2 / tau * MP + B * a * X + (A * b - b / tau) * Y -
              &2 * alpha * Zn + (L * ce - C * ce) * psi0 * (X + Y) -
              ce * ((X + Y) * lapq + &2 * lgi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `MP:real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `alpha:real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `beta:real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `c:real`)) THEN
  ABBREV_TAC `kX = B * a - (a + ce * psi0) * (DX + (a + ce * psi0)) +
                   (L - &2 * C - &2 * sigma) * ce * psi0` THEN
  ABBREV_TAC `kY = &2 / tau * (b + ce * psi0) + A * b - b / tau -
                   (a + ce * psi0) * (DY + &2 * (b + ce * psi0)) - EY * (b + ce * psi0) -
                   &2 * (a + ce * psi0) * kappa + (L - &2 * C - &2 * sigma) * ce * psi0` THEN
  SUBGOAL_THEN `&0 < kX * X + kY * Y` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < X` THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 <= y ==> &0 < x + y`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_LE_MUL; REAL_LT_IMP_LE];
      SUBGOAL_THEN `X = &0 /\ &0 < Y` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_LT_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ce * (X + Y)) * lapq <= (ce * (X + Y)) * (C * psi0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ce:real`; `lgi:real`; `sigma * psi0 * (X + Y)`] RFA_MUL_ABS_LE2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a + ce * psi0) * Zn <= (a + ce * psi0) * kappa * Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < kX * X + kY * Y` THEN
  MAP_EVERY EXPAND_TAC ["kX"; "kY"] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Symmetries of the frame arrays.  M is symmetric in a frame                *)
(* (RFA_ARR_M_SYM, RFA_HM_FT_SYM: the contracted Ricci identity at the array *)
(* level; entries with an index outside 1..3 vanish), the curvature          *)
(* symmetries of lrm4 in the rfa_hz slot convention (RFA_LRM4_FT_SYMS), the  *)
(* antisymmetry of P (RFA_HP_FT_ANTI), the symmetries of the identity        *)
(* 4-array (RFA_I4_SYMS), and the frame form of the gradient norm of a       *)
(* scalar field (RFA_LGRAD2_FRAME0).                                         *)
(* ========================================================================= *)

let RFA_KD_SYM = prove
 (`!i j. rfa_kd i j = rfa_kd j i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_kd] THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let RFA_ARR_R_ANTI34 = prove
 (`!(ric:num->num->real) a b c d. rfa_arr_r ric a b c d = --(rfa_arr_r ric a b d c)`,
  REWRITE_TAC[rfa_arr_r] THEN REAL_ARITH_TAC);;

let RFA_ARR_M_SYM = prove
 (`!(ric:num->num->real) (ddr:num->num->num->num->real) tau a b.
     (!i j. ric i j = ric j i) /\
     (!i j k l. ddr i j k l = ddr j i k l) /\
     (!e. 1 <= e /\ e <= 3
          ==> ddr e e a b - ddr e e b a =
              sum(1..3) (\r. rfa_arr_r ric a b e r * ric r e) +
              sum(1..3) (\r. rfa_arr_r ric a b e r * ric e r))
     ==> rfa_arr_m ric ddr tau a b = rfa_arr_m ric ddr tau b a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ric") (CONJUNCTS_THEN2 (LABEL_TAC "ddr")
    (LABEL_TAC "rid"))) THEN
  SUBGOAL_THEN `sum(1..3) (\e. (ddr:num->num->num->num->real) e e b a) =
                sum(1..3) (\e. ddr e e a b)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..3) (\e. sum(1..3) (\r. --(((ric:num->num->real) r e + ric e r) *
                                                rfa_arr_r ric a b e r)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN BETA_TAC THEN
      REMOVE_THEN "rid" (MP_TAC o SPEC `e:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x - y = z ==> y - x = --z`)) THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_NEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_NEG; REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC RFA_SUM_ANTISYM THEN REPEAT STRIP_TAC THENL
       [REAL_ARITH_TAC; MATCH_ACCEPT_TAC RFA_ARR_R_ANTI34]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..3) (\e. (ddr:num->num->num->num->real) b a e e) =
                sum(1..3) (\e. ddr a b e e)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "ddr" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..3) (\e. (ric:num->num->real) b e * ric e a) =
                sum(1..3) (\e. ric a e * ric e b)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "ric" (fun th -> MP_TAC(SPECL [`b:num`; `e:num`] th) THEN
                              MP_TAC(SPECL [`e:num`; `a:num`] th)) THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ric:num->num->real) b a = ric a b` ASSUME_TAC THENL
   [USE_THEN "ric" MATCH_ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_kd b a = rfa_kd a b` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC RFA_KD_SYM; ALL_TAC] THEN
  REMOVE_THEN "ric" (K ALL_TAC) THEN REMOVE_THEN "ddr" (K ALL_TAC) THEN
  REMOVE_THEN "rid" (K ALL_TAC) THEN
  REWRITE_TAC[rfa_arr_m] THEN ASM_REWRITE_TAC[]);;

let RFA_I4_SYMS = prove
 (`!a b c d. rfa_i4 a b c d = --(rfa_i4 b a c d) /\
             rfa_i4 a b c d = --(rfa_i4 a b d c) /\
             rfa_i4 a b c d = rfa_i4 c d a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_i4] THEN REPEAT CONJ_TAC THEN
  REPEAT COND_CASES_TAC THEN FIRST [REAL_ARITH_TAC; ASM_MESON_TAC[]]);;

let RFA_FT_ZERO = prove
 (`!(S:real^N^N) l m.
     ~(1 <= EL (m - 1) l /\ EL (m - 1) l <= dimindex(:N)) ==> rfa_ft S l m = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ft] THEN
  SUBGOAL_THEN `basis (EL (m - 1) l):real^N = vec 0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG]; REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]]);;

let RFA_TF_ZERO_SLOT = prove
 (`!k U (tf:real^N->(num->real^N)->real) y u i.
     ltensor_field k U tf /\ y IN U /\ 1 <= i /\ i <= k /\ u i = vec 0 ==> tf y u = &0`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `u:num->real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
  SUBGOAL_THEN `(\j. if j = i then vec 0 else (u:num->real^N) j) = u`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]]);;

let RFA_HM_FT_SYM = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t a b.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> rfa_hM s t G y (rfa_ft S [a; b]) = rfa_hM s t G y (rfa_ft S [b; a])`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3` THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `s:real`; `t:real`; `a:num`; `b:num`] RFA_HM_ARR) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `s:real`; `t:real`; `b:num`; `a:num`] RFA_HM_ARR) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC RFA_ARR_M_SYM THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[rfa_ric_a] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_FT_RIC_SYM THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[rfa_ddr_a] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_FT_DDRIC_SYM THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `e:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ddr_a] THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                     `e:num`; `e:num`; `a:num`; `b:num`] RFA_FT_RICCI_ID) THEN
      ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
      BINOP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      BETA_TAC THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                     `a:num`; `b:num`; `e:num`; `r:num`] RFA_LRM4_ARR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[rfa_ric_a]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `s:real`; `t:real`] RFA_SF_HM) THEN
  ASM_REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(1 <= a /\ a <= 3) \/ ~(1 <= b /\ b <= 3)` MP_TAC THENL
   [ASM_MESON_TAC[]; DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC)] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 /\ y = &0 ==> x = y`) THEN CONJ_TAC THEN
  MATCH_MP_TAC RFA_TF_ZERO_SLOT THEN
  MAP_EVERY EXISTS_TAC [`2`; `U:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  (let fin = CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC RFA_FT_ZERO THEN
             CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH; DIMINDEX_3] THEN
             ASM_REWRITE_TAC[] THEN NO_TAC in
   FIRST [EXISTS_TAC `1` THEN fin; EXISTS_TAC `2` THEN fin]));;

let RFA_LRM4_FT_SYMS = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N).
     metric_field U G /\ y IN U
     ==> !a b c d.
           lrm4 G y (rfa_ft S [a; b; d; c]) = --(lrm4 G y (rfa_ft S [b; a; d; c])) /\
           lrm4 G y (rfa_ft S [a; b; d; c]) = --(lrm4 G y (rfa_ft S [a; b; c; d])) /\
           lrm4 G y (rfa_ft S [a; b; d; c]) = lrm4 G y (rfa_ft S [c; d; b; a])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lrm4; RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH] THEN
  ABBREV_TAC `fa = transp(S:real^N^N) ** basis a` THEN
  ABBREV_TAC `fb = transp(S:real^N^N) ** basis b` THEN
  ABBREV_TAC `fc = transp(S:real^N^N) ** basis c` THEN
  ABBREV_TAC `fd = transp(S:real^N^N) ** basis d` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `fa:real^N`; `fb:real^N`; `fc:real^N`; `fd:real^N`] LRG_RM_ANTI1) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `fa:real^N`; `fb:real^N`; `fc:real^N`; `fd:real^N`] LRG_RM_ANTISYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `fa:real^N`; `fb:real^N`; `fc:real^N`; `fd:real^N`] LRIEMANN_PAIR_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `fd:real^N`; `fc:real^N`; `fb:real^N`; `fa:real^N`] LRG_RM_ANTI1) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `fc:real^N`; `fd:real^N`; `fb:real^N`; `fa:real^N`] LRG_RM_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_HP_FT_ANTI = prove
 (`!(G:real^N->real^N^N) y (S:real^N^N) a b c.
     rfa_hP G y (rfa_ft S [a; b; c]) = --(rfa_hP G y (rfa_ft S [b; a; c]))`,
  REWRITE_TAC[rfa_hP; RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH] THEN REAL_ARITH_TAC);;

let RFA_LGRAD2_FRAME0 = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (S:real^N^N) u.
     metric_field U G /\ rfa_sf 0 U tf /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> lgrad2 G (\x. tf x u) y =
         sum(1..dimindex(:N)) (\r. lnabla 0 G tf y (rfa_ft S [r]) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\z. lift((tf:real^N->(num->real^N)->real) z u)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lgrad2] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BETA_RULE(ISPECL
    [`S:real^N^N`;
     `\a. drop(frechet_derivative (\z. lift((tf:real^N->(num->real^N)->real) z u)) (at y)
                                  (basis a))`] RFA_QUAD_FRAME)] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LRG_LNABLA_EQ; ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO] THEN
  REWRITE_TAC[RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH] THEN
  SUBGOAL_THEN
   `frechet_derivative (\x. lift((tf:real^N->(num->real^N)->real) x (rfa_ft S [p]))) (at y) =
    frechet_derivative (\z. lift(tf z u)) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN
    UNDISCH_TAC `ltensor_field 0 U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [GSYM(ISPEC `transp(S:real^N^N) ** basis p` (MATCH_MP LRG_LINEAR_DROP_EXPAND th))]) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC LRG_TRANSP_BASIS_COMPONENT THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The push at the array level (RFA_PUSH_ARRAY).  For arrays                 *)
(* with the curvature symmetries, a positive semidefinite perturbed form     *)
(* with a nonzero null vector (u, w), the 1-jet (10.59) of U, entrywise      *)
(* bounds, the barrier bounds and positive coefficients kX, kY, the quantity *)
(* tested at a touching point (defect of F + c N with the time and space     *)
(* barrier terms) is positive.  Ingredients: the bilinear null conditions    *)
(* (the defect terms of U and W cancel; M(w,w) + P(u,w) = -beta |w|^2),      *)
(* RFA_HARNACK_ALG of pc_rfa_halg for the perturbed arrays, RFA_DJ_BOUND,    *)
(* RFA_DU_BOUND, RFA_GRADN_BOUND, RFA_LGI_BOUND and RFA_PUSH_SCALAR.         *)
(* ========================================================================= *)

let RFA_HZB_ZERO_X = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (u:num->num->real) (w:num->real).
     rfa_hzb 3 R P M u w (\i j. &0) w =
     sum(1..3) (\a. sum(1..3) (\b. M a b * w a * w b)) +
     sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. P a b c * u a b * w c)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hzb] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID; SUM_0] THEN
  REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC);;

let RFA_SUMSQ_POS_TAC =
  REPEAT(MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
  REWRITE_TAC[REAL_LE_POW_2];;

let RFA_PUSH_ARRAY = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (u:num->num->real) (w:num->real) (h:num->num->real) (k:num->real)
    (du:num->num->num->real) (ric:num->num->real)
    tau pa pa' pb pb' ce ce' psi0 C lapq lgi lgq KR KP KM K B A L sigma.
     (!a b c d. R a b c d = --(R b a c d)) /\
     (!a b c d. R a b c d = --(R a b d c)) /\
     (!a b c d. R a b c d = R c d a b) /\
     (!a b c. P a b c = --(P b a c)) /\
     (!a b. M a b = M b a) /\
     (!i j. u i j = --(u j i)) /\
     (!u' w'. (!i j. u' i j = --(u' j i))
              ==> &0 <= rfa_hz 3 (\a b c d. R a b c d + (pa + ce * psi0) * rfa_i4 a b c d) P
                                 (\a b. M a b + (pb + ce * psi0) * rfa_kd a b) u' w') /\
     rfa_hz 3 (\a b c d. R a b c d + (pa + ce * psi0) * rfa_i4 a b c d) P
              (\a b. M a b + (pb + ce * psi0) * rfa_kd a b) u w = &0 /\
     &0 < sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2) /\
     (!i j e. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ 1 <= e /\ e <= 3
              ==> du i j e =
                  inv(&2) * (ric e i * w j - ric e j * w i) +
                  inv(&4 * tau) * ((if e = i then &1 else &0) * w j -
                                   (if e = j then &1 else &0) * w i)) /\
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3 ==> abs(R a b c d) <= KR) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(P a b c) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(M a b) <= KM) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(ric a b) <= K) /\
     &0 < tau /\ &0 <= pa /\ &0 <= pb /\ &0 <= ce /\ &0 <= psi0 /\
     pa' = B * pa /\ pb' = A * pb - pb / tau /\ ce' = L * ce /\
     lapq <= C * psi0 /\ &0 <= C /\
     lgi pow 2 <= lgq * sum(1..3) (\e. (&2 * sum(1..3) (\a. sum(1..3) (\b.
                                         u a b * du a b e))) pow 2) /\
     &0 <= lgq /\ lgq <= C * psi0 pow 2 /\
     &0 <= sigma /\ C * (&18 * K pow 2 + inv(&2 * tau pow 2)) <= sigma pow 2 /\
     &0 < B * pa - (pa + ce * psi0) * ((&12 * KP + &324 * KR) + (pa + ce * psi0)) +
          (L - &2 * C - &2 * sigma) * (ce * psi0) /\
     &0 < &2 / tau * (pb + ce * psi0) + A * pb - pb / tau -
          (pa + ce * psi0) * ((&6 * KM + &36 * KP) + &2 * (pb + ce * psi0)) -
          (&18 * KR) * (pb + ce * psi0) -
          &2 * (pa + ce * psi0) * (&18 * K pow 2 + inv(&2 * tau pow 2)) +
          (L - &2 * C - &2 * sigma) * (ce * psi0)
     ==> &0 < (rfa_hj 3 R P M u w +
               sum(1..3) (\a. sum(1..3) (\b.
                 (sum(1..3) (\c. P a b c * w c) +
                  sum(1..3) (\c. sum(1..3) (\d. R a b d c * u c d))) pow 2)) -
               &2 / tau *
               (sum(1..3) (\a. sum(1..3) (\b. M a b * w a * w b)) +
                sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. P a b c * u a b * w c)))) +
               &2 * (sum(1..3) (\a. sum(1..3) (\b. M a b * k a * w b)) +
                     sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. P a b c *
                       (h a b * w c + u a b * k c)))) +
                     sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                       R a b d c * h a b * u c d))))) +
               pa' * sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) +
               &2 * pa * (sum(1..3) (\a. sum(1..3) (\b. h a b * u a b)) -
                          sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e. du a b e pow 2)))) +
               pb' * sum(1..3) (\a. w a pow 2) +
               &2 * pb * sum(1..3) (\a. k a * w a)) +
              (ce' - C * ce) * psi0 *
              (sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2)) +
              ce * psi0 *
              (&2 * (sum(1..3) (\a. sum(1..3) (\b. h a b * u a b)) -
                     sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e. du a b e pow 2)))) +
               &2 * sum(1..3) (\a. k a * w a)) -
              ce * ((sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2)) *
                    lapq + &2 * lgi)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `alpha = pa + ce * psi0` THEN ABBREV_TAC `beta = pb + ce * psi0` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R1") (CONJUNCTS_THEN2 (LABEL_TAC "R2")
    (CONJUNCTS_THEN2 (LABEL_TAC "R3") (CONJUNCTS_THEN2 (LABEL_TAC "P1")
    (CONJUNCTS_THEN2 (LABEL_TAC "M1") (CONJUNCTS_THEN2 (LABEL_TAC "anti")
    (CONJUNCTS_THEN2 (LABEL_TAC "psd") (CONJUNCTS_THEN2 (LABEL_TAC "null")
    (CONJUNCTS_THEN2 (LABEL_TAC "nz") (CONJUNCTS_THEN2 (LABEL_TAC "du")
    (CONJUNCTS_THEN2 (LABEL_TAC "bR") (CONJUNCTS_THEN2 (LABEL_TAC "bP")
    (CONJUNCTS_THEN2 (LABEL_TAC "bM") (CONJUNCTS_THEN2 (LABEL_TAC "bric")
    STRIP_ASSUME_TAC)))))))))))))) THEN
  (* the bilinear null conditions *)
  SUBGOAL_THEN
   `rfa_hzb 3 (\a b c d. (R:num->num->num->num->real) a b c d + alpha * rfa_i4 a b c d) P
              (\a b. (M:num->num->real) a b + beta * rfa_kd a b) u w
              (\i j. ((h:num->num->real) i j - h j i) / &2) k = &0 /\
    rfa_hzb 3 (\a b c d. R a b c d + alpha * rfa_i4 a b c d) P
              (\a b. M a b + beta * rfa_kd a b) u w (\(i:num) (j:num). &0) w = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_HZ_NULL_BIL THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "psd" ACCEPT_TAC; USE_THEN "anti" ACCEPT_TAC; USE_THEN "null" ACCEPT_TAC;
      REPEAT GEN_TAC THEN REAL_ARITH_TAC;
      USE_THEN "psd" ACCEPT_TAC; USE_THEN "anti" ACCEPT_TAC; USE_THEN "null" ACCEPT_TAC;
      REPEAT GEN_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                 `M:num->num->real`; `u:num->num->real`; `w:num->real`;
                 `\i j. ((h:num->num->real) i j - h j i) / &2`; `k:num->real`;
                 `alpha:real`; `beta:real`] RFA_HZB_PERTURB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "anti" ACCEPT_TAC; REPEAT GEN_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_const(rand(concl th)) = false &&
                             rand(concl th) = `&0` &&
                             can (find_term ((=) `k:num->real`)) (concl th)
                          then REWRITE_TAC[th] else failwith "no") THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                 `M:num->num->real`; `u:num->num->real`; `w:num->real`;
                 `\(i:num) (j:num). &0`; `w:num->real`;
                 `alpha:real`; `beta:real`] RFA_HZB_PERTURB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "anti" ACCEPT_TAC; REPEAT GEN_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `&0` &&
                             can (find_term ((=) `\(i:num) (j:num). &0`)) (concl th)
                          then REWRITE_TAC[th] else failwith "no") THEN
  REWRITE_TAC[RFA_HZB_ZERO_X; REAL_MUL_RZERO; SUM_0; REAL_ADD_RID] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                 `M:num->num->real`; `u:num->num->real`; `w:num->real`;
                 `h:num->num->real`; `k:num->real`] RFA_HV_ID) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "R1" ACCEPT_TAC; USE_THEN "R2" ACCEPT_TAC; USE_THEN "R3" ACCEPT_TAC;
      USE_THEN "P1" ACCEPT_TAC; USE_THEN "M1" ACCEPT_TAC; USE_THEN "anti" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hv") (LABEL_TAC "huu")) THEN
  SUBGOAL_THEN `sum(1..3) (\a. (w:num->real) a * k a) = sum(1..3) (\a. k a * w a) /\
                sum(1..3) (\a. (w:num->real) a * w a) = sum(1..3) (\a. w a pow 2)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "hv" (fun hv -> REMOVE_THEN "huu" (fun huu ->
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM hv; GSYM huu]))) THEN
  (* RFA_HARNACK_ALG: J of the perturbed arrays is nonnegative *)
  MP_TAC(REWRITE_RULE[RFA_HARNACK_ALG_STATEMENT; DIMINDEX_3] (ISPEC `(:3)` RFA_HARNACK_ALG)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\a b c d. (R:num->num->num->num->real) a b c d + alpha * rfa_i4 a b c d`;
    `P:num->num->num->real`; `\a b. (M:num->num->real) a b + beta * rfa_kd a b`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN BETA_TAC THEN
      MP_TAC(SPECL [`a:num`; `b:num`; `c:num`; `d:num`] RFA_I4_SYMS) THEN
      USE_THEN "R1" (MP_TAC o SPECL [`a:num`; `b:num`; `c:num`; `d:num`]) THEN
      USE_THEN "R2" (MP_TAC o SPECL [`a:num`; `b:num`; `c:num`; `d:num`]) THEN
      USE_THEN "R3" (MP_TAC o SPECL [`a:num`; `b:num`; `c:num`; `d:num`]) THEN
      CONV_TAC REAL_RING;
      USE_THEN "P1" ACCEPT_TAC;
      REPEAT GEN_TAC THEN BETA_TAC THEN
      USE_THEN "M1" (fun th -> REWRITE_TAC[SPECL [`a:num`; `b:num`] th]) THEN
      REWRITE_TAC[SPECL [`a:num`; `b:num`] RFA_KD_SYM];
      USE_THEN "psd" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:num->num->real`; `w:num->real`]) THEN
  ANTS_TAC THENL [USE_THEN "anti" ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= ce * psi0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= alpha /\ &0 <= beta` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["alpha"; "beta"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the change of J *)
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                 `M:num->num->real`; `u:num->num->real`; `w:num->real`;
                 `alpha:real`; `beta:real`; `KR:real`; `KP:real`; `KM:real`] RFA_DJ_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "anti" ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "bR" ACCEPT_TAC; USE_THEN "bP" ACCEPT_TAC; USE_THEN "bM" ACCEPT_TAC];
    DISCH_TAC] THEN
  (* |nabla U|^2 *)
  SUBGOAL_THEN
   `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e. (du:num->num->num->real) a b e pow 2))) <=
    (&18 * K pow 2 + inv(&2 * tau pow 2)) * sum(1..3) (\a. (w:num->real) a pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e.
        (inv(&2) * ((ric:num->num->real) e a * (w:num->real) b - ric e b * w a) +
         inv(&4 * tau) * ((if e = a then &1 else &0) * w b -
                          (if e = b then &1 else &0) * w a)) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      REPEAT(MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN USE_THEN "du" MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC RFA_DU_BOUND THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; USE_THEN "bric" ACCEPT_TAC]];
    ALL_TAC] THEN
  (* the gradient term *)
  MP_TAC(ISPECL [`u:num->num->real`; `du:num->num->num->real`] RFA_GRADN_BOUND) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`lgi:real`; `lgq:real`;
    `sum(1..3) (\e. (&2 * sum(1..3) (\a. sum(1..3) (\b.
       (u:num->num->real) a b * (du:num->num->num->real) a b e))) pow 2)`;
    `sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2))`;
    `sum(1..3) (\a. (w:num->real) a pow 2)`;
    `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e. (du:num->num->num->real) a b e pow 2)))`;
    `C:real`; `psi0:real`; `&18 * K pow 2 + inv(&2 * tau pow 2)`;
    `sigma:real`] RFA_LGI_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RFA_SUMSQ_POS_TAC); ALL_TAC] THEN
  SUBGOAL_THEN `abs psi0 = psi0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  (* the scalar push *)
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `pa':real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `pb':real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `ce':real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `alpha:real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `beta:real`)) THEN
  MP_TAC(ISPECL
   [`sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2))`;
    `sum(1..3) (\a. (w:num->real) a pow 2)`;
    `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e. (du:num->num->num->real) a b e pow 2)))`;
    `rfa_hj 3 (R:num->num->num->num->real) P M u w`;
    `rfa_hj 3 (\a b c d. (R:num->num->num->num->real) a b c d + (pa + ce * psi0) * rfa_i4 a b c d)
             P (\a b. (M:num->num->real) a b + (pb + ce * psi0) * rfa_kd a b) u w`;
    `&12 * KP + &324 * KR`; `&6 * KM + &36 * KP`; `&18 * KR`;
    `sum(1..3) (\a. sum(1..3) (\b.
       (sum(1..3) (\c. (P:num->num->num->real) a b c * (w:num->real) c) +
        sum(1..3) (\c. sum(1..3) (\d. (R:num->num->num->num->real) a b d c *
                                      (u:num->num->real) c d))) pow 2))`;
    `sum(1..3) (\a. sum(1..3) (\b. (M:num->num->real) a b * (w:num->real) a * w b)) +
     sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. (P:num->num->num->real) a b c *
                                                 (u:num->num->real) a b * w c)))`;
    `tau:real`; `pa:real`; `pb:real`; `ce * psi0`; `pa + ce * psi0`; `pb + ce * psi0`;
    `ce:real`; `psi0:real`; `B:real`; `A:real`; `L:real`; `C:real`; `sigma:real`;
    `&18 * K pow 2 + inv(&2 * tau pow 2)`; `lapq:real`; `lgi:real`] RFA_PUSH_SCALAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; RFA_SUMSQ_POS_TAC THEN NO_TAC; REFL_TAC;
     (FIRST_ASSUM(fun th -> if is_binary "real_le" (concl th) &&
                               can (find_term ((=) `KM:real`)) (concl th)
                            then MP_TAC th else failwith "no") THEN REAL_ARITH_TAC);
     (FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs(concl th) = `&0` &&
                               not (can (find_term ((=) `k:num->real`)) (concl th))
                            then MP_TAC th else failwith "no") THEN REAL_ARITH_TAC)];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs(concl th) = `&0` &&
                           can (find_term ((=) `k:num->real`)) (concl th)
                        then MP_TAC th else failwith "no") THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The push in a chart (RFA_PUSH_CHART).  At (t0, y0), in an                 *)
(* orthonormal frame S of G t0, for fields U, W with the 1-jet (10.59) at y0 *)
(* (U antisymmetric, nabla W = 0, nabla U given by Ric and W), when the      *)
(* perturbed Harnack form is positive semidefinite with the nonzero null     *)
(* vector (U, W) at y0 and the constants satisfy kX, kY > 0, the quantity    *)
(* bounded above by 0 in RFA_TOUCH_INEQ is positive.  It combines the        *)
(* defect identity RFA_HARNACK_DEFECT_3D_PERT, the norm lemmas of            *)
(* pc_rfa_hext, the frame gradient (RFA_LGRAD2_FRAME0, RFA_NRM2_GRAD_3D),     *)
(* Cauchy-Schwarz (RFA_LGINNER_CS) and RFA_PUSH_ARRAY.                       *)
(* ========================================================================= *)

let RFA_PUSH_CHART = prove
 (`!U a b (G:real->real^3->real^3^3) s t0 y0 (S:real^3^3) Uf HUf Wf HWf (u:num->real^3)
    q pa pa' pb pb' ce ce' psi0 C KR KP KM K B A L sigma.
     lricci_flow U a b G /\ s <= a /\ a < t0 /\ t0 < b /\ y0 IN U /\
     invertible S /\ matrix_inv(G t0 y0) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 2 U HUf /\ rfa_sf 1 U Wf /\ rfa_sf 1 U HWf /\
     (!i j. Uf y0 (rfa_ft S [i; j]) = --(Uf y0 (rfa_ft S [j; i]))) /\
     (!w. lnabla 1 (G t0) Wf y0 w = &0) /\
     (!i j e. lnabla 2 (G t0) Uf y0 (rfa_ft S [i; j; e]) =
              inv(&2) * (lric2 (G t0) y0 (rfa_ft S [e; i]) * Wf y0 (rfa_ft S [j]) -
                         lric2 (G t0) y0 (rfa_ft S [e; j]) * Wf y0 (rfa_ft S [i])) +
              inv(&4 * (t0 - s)) * (lmetric2 (G t0) y0 (rfa_ft S [e; i]) * Wf y0 (rfa_ft S [j]) -
                                    lmetric2 (G t0) y0 (rfa_ft S [e; j]) * Wf y0 (rfa_ft S [i]))) /\
     (!u' w'. (!i j. u' i j = --(u' j i))
              ==> &0 <= rfa_hz 3 (\a b c d. lrm4 (G t0) y0 (rfa_ft S [a; b; d; c]) +
                                            (pa + ce * psi0) * rfa_i4 a b c d)
                                 (\a b c. rfa_hP (G t0) y0 (rfa_ft S [a; b; c]))
                                 (\a b. rfa_hM s t0 (G t0) y0 (rfa_ft S [a; b]) +
                                        (pb + ce * psi0) * rfa_kd a b) u' w') /\
     rfa_hz 3 (\a b c d. lrm4 (G t0) y0 (rfa_ft S [a; b; d; c]) +
                         (pa + ce * psi0) * rfa_i4 a b c d)
              (\a b c. rfa_hP (G t0) y0 (rfa_ft S [a; b; c]))
              (\a b. rfa_hM s t0 (G t0) y0 (rfa_ft S [a; b]) + (pb + ce * psi0) * rfa_kd a b)
              (\a b. Uf y0 (rfa_ft S [a; b])) (\a. Wf y0 (rfa_ft S [a])) = &0 /\
     &0 < sum(1..3) (\a. sum(1..3) (\b. Uf y0 (rfa_ft S [a; b]) pow 2)) +
          sum(1..3) (\a. Wf y0 (rfa_ft S [a]) pow 2) /\
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3
                ==> abs(lrm4 (G t0) y0 (rfa_ft S [a; b; d; c])) <= KR) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(rfa_hP (G t0) y0 (rfa_ft S [a; b; c])) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
            ==> abs(rfa_hM s t0 (G t0) y0 (rfa_ft S [a; b])) <= KM) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
            ==> abs(lric2 (G t0) y0 (rfa_ft S [a; b])) <= K) /\
     &0 <= pa /\ &0 <= pb /\ &0 <= ce /\ &0 <= psi0 /\
     pa' = B * pa /\ pb' = A * pb - pb / (t0 - s) /\ ce' = L * ce /\
     llap (G t0) q y0 <= C * psi0 /\ &0 <= C /\ lgrad2 (G t0) q y0 <= C * psi0 pow 2 /\
     &0 <= sigma /\ C * (&18 * K pow 2 + inv(&2 * (t0 - s) pow 2)) <= sigma pow 2 /\
     &0 < B * pa - (pa + ce * psi0) * ((&12 * KP + &324 * KR) + (pa + ce * psi0)) +
          (L - &2 * C - &2 * sigma) * (ce * psi0) /\
     &0 < &2 / (t0 - s) * (pb + ce * psi0) + A * pb - pb / (t0 - s) -
          (pa + ce * psi0) * ((&6 * KM + &36 * KP) + &2 * (pb + ce * psi0)) -
          (&18 * KR) * (pb + ce * psi0) -
          &2 * (pa + ce * psi0) * (&18 * K pow 2 + inv(&2 * (t0 - s) pow 2)) +
          (L - &2 * C - &2 * sigma) * (ce * psi0)
     ==> &0 < rfa_hqform (G t0) (\y u. rfa_hM s t0 (G t0) y u + pb * lmetric2 (G t0) y u)
                (\y u. rfa_hhM s t0 (G t0) y u + pb' * lmetric2 (G t0) y u) (rfa_hP (G t0))
                (\y u. rfa_hdr (G t0) y (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) -
                       rfa_hdr (G t0) y (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2))
                (\y u. lrm4 (G t0) y u + pa * rfa_ifld (G t0) y u)
                (\y u. rfa_h3 (G t0) (rfa_hric (G t0)) y u + pa' * rfa_ifld (G t0) y u)
                Uf HUf Wf HWf y0 u +
              (ce' - C * ce) * psi0 * rfa_nrm2 (G t0) Uf Wf y0 u +
              ce * psi0 * rfa_hnrm2 (G t0) Uf HUf Wf HWf y0 u -
              ce * (rfa_nrm2 (G t0) Uf Wf y0 u * llap (G t0) q y0 +
                    &2 * rfa_lginner (G t0) q (\x. rfa_nrm2 (G t0) Uf Wf x u) y0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "anti") (CONJUNCTS_THEN2 (LABEL_TAC "dW")
    (CONJUNCTS_THEN2 (LABEL_TAC "dU") (CONJUNCTS_THEN2 (LABEL_TAC "psd")
    (CONJUNCTS_THEN2 (LABEL_TAC "null") (CONJUNCTS_THEN2 (LABEL_TAC "nz")
    (CONJUNCTS_THEN2 (LABEL_TAC "bR") (CONJUNCTS_THEN2 (LABEL_TAC "bP")
    (CONJUNCTS_THEN2 (LABEL_TAC "bM") (CONJUNCTS_THEN2 (LABEL_TAC "bric")
    STRIP_ASSUME_TAC))))))))))))))))))))) THEN
  MP_TAC(MATCH_MP LRG_FLOW_BASIC (ASSUME `lricci_flow U a b (G:real->real^3->real^3^3)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `t0:real` o el 4 o CONJUNCTS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  (* the defect of the perturbed quadratic *)
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`; `s:real`;
                 `t0:real`; `y0:real^3`; `S:real^3^3`;
                 `Uf:real^3->(num->real^3)->real`; `HUf:real^3->(num->real^3)->real`;
                 `Wf:real^3->(num->real^3)->real`; `HWf:real^3->(num->real^3)->real`;
                 `u:num->real^3`; `pa:real`; `pa':real`; `pb:real`; `pb':real`]
         RFA_HARNACK_DEFECT_3D_PERT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  (* the norm, its defect and its gradient *)
  SUBGOAL_THEN
   `!i j e. lnabla 2 ((G:real->real^3->real^3^3) t0) Uf y0 (rfa_ft S [i; j; e]) =
            --(lnabla 2 (G t0) Uf y0 (rfa_ft S [j; i; e]))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN USE_THEN "dU" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`; `S:real^3^3`;
                 `Uf:real^3->(num->real^3)->real`; `HUf:real^3->(num->real^3)->real`;
                 `Wf:real^3->(num->real^3)->real`; `HWf:real^3->(num->real^3)->real`;
                 `u:num->real^3`] RFA_NRM2_DEFECT_3D) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`; `S:real^3^3`;
                 `Uf:real^3->(num->real^3)->real`; `HUf:real^3->(num->real^3)->real`;
                 `Wf:real^3->(num->real^3)->real`; `HWf:real^3->(num->real^3)->real`;
                 `u:num->real^3`] RFA_NRM2_FRAME) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `rfa_sf 0 U (rfa_nrm2 ((G:real->real^3->real^3^3) t0) Uf Wf)` ASSUME_TAC THENL
   [(fun g ->
      let mf = ASSUME `metric_field U ((G:real->real^3->real^3^3) t0)` in
      let saved = RFA_ENGINE_SAVE () in
      RFA_ENGINE_RESET ();
      rfa_sf_bases := [ASSUME `rfa_sf 2 U (Uf:real^3->(num->real^3)->real)`;
                       ASSUME `rfa_sf 1 U (Wf:real^3->(num->real^3)->real)`];
      rfa_sf_unfolds := [rfa_nrm2];
      let th = try RFA_SF_PROVE mf `rfa_nrm2 ((G:real->real^3->real^3^3) t0) Uf Wf`
               with e -> (RFA_ENGINE_RESTORE saved; raise e) in
      RFA_ENGINE_RESTORE saved; ACCEPT_TAC th g);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`;
                 `rfa_nrm2 ((G:real->real^3->real^3^3) t0) Uf Wf`; `y0:real^3`; `S:real^3^3`;
                 `u:num->real^3`] RFA_LGRAD2_FRAME0) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `lgrad2 ((G:real->real^3->real^3^3) t0) (\x. rfa_nrm2 (G t0) Uf Wf x u) y0 =
    sum(1..3) (\e. (&2 * sum(1..3) (\a. sum(1..3) (\b.
      (Uf:real^3->(num->real^3)->real) y0 (rfa_ft S [a; b]) *
      lnabla 2 (G t0) Uf y0 (rfa_ft S [a; b; e])))) pow 2)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                               (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "lgrad2"
                                with Failure _ -> false)
                            then SUBST1_TAC th else failwith "no") THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                   `S:real^3^3`;
                   `Uf:real^3->(num->real^3)->real`; `HUf:real^3->(num->real^3)->real`;
                   `Wf:real^3->(num->real^3)->real`; `HWf:real^3->(num->real^3)->real`;
                   `e:num`] RFA_NRM2_GRAD_3D) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "dW" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_MUL_RZERO; SUM_0; REAL_ADD_RID];
    ALL_TAC] THEN
  (* Cauchy-Schwarz for the cross gradient term *)
  SUBGOAL_THEN
   `&0 <= lgrad2 ((G:real->real^3->real^3^3) t0) q y0 /\
    &0 <= lgrad2 ((G:real->real^3->real^3^3) t0) (\x. rfa_nrm2 (G t0) Uf Wf x u) y0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LGRAD2_POS THEN EXISTS_TAC `U:real^3->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `q:real^3->real`;
                 `\x. rfa_nrm2 ((G:real->real^3->real^3^3) t0) Uf Wf x u`; `y0:real^3`]
         RFA_LGINNER_CS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `rfa_lginner ((G:real->real^3->real^3^3) t0) q (\x. rfa_nrm2 (G t0) Uf Wf x u) y0 pow 2 <=
    lgrad2 (G t0) q y0 * lgrad2 (G t0) (\x. rfa_nrm2 (G t0) Uf Wf x u) y0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sqrt(lgrad2 ((G:real->real^3->real^3^3) t0) q y0) *
                 sqrt(lgrad2 (G t0) (\x. rfa_nrm2 (G t0) Uf Wf x u) y0)) pow 2` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[REAL_ABS_POS] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN
      MP_TAC(ISPEC `lgrad2 ((G:real->real^3->real^3^3) t0) q y0` SQRT_POW_2) THEN
      MP_TAC(ISPEC `lgrad2 ((G:real->real^3->real^3^3) t0) (\x. rfa_nrm2 (G t0) Uf Wf x u) y0`
             SQRT_POW_2) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the array-level push *)
  MP_TAC(BETA_RULE(ISPECL
   [`\a b c d. lrm4 ((G:real->real^3->real^3^3) t0) y0 (rfa_ft (S:real^3^3) [a; b; d; c])`;
    `\a b c. rfa_hP ((G:real->real^3->real^3^3) t0) y0 (rfa_ft (S:real^3^3) [a; b; c])`;
    `\a b. rfa_hM s t0 ((G:real->real^3->real^3^3) t0) y0 (rfa_ft (S:real^3^3) [a; b])`;
    `\a b. (Uf:real^3->(num->real^3)->real) y0 (rfa_ft (S:real^3^3) [a; b])`;
    `\a. (Wf:real^3->(num->real^3)->real) y0 (rfa_ft (S:real^3^3) [a])`;
    `\a b. (HUf:real^3->(num->real^3)->real) y0 (rfa_ft (S:real^3^3) [a; b])`;
    `\a. (HWf:real^3->(num->real^3)->real) y0 (rfa_ft (S:real^3^3) [a])`;
    `\a b e. lnabla 2 ((G:real->real^3->real^3^3) t0) Uf y0 (rfa_ft (S:real^3^3) [a; b; e])`;
    `\a b. lric2 ((G:real->real^3->real^3^3) t0) y0 (rfa_ft (S:real^3^3) [a; b])`;
    `t0 - s:real`; `pa:real`; `pa':real`; `pb:real`; `pb':real`; `ce:real`; `ce':real`;
    `psi0:real`; `C:real`; `llap ((G:real->real^3->real^3^3) t0) q y0`;
    `rfa_lginner ((G:real->real^3->real^3^3) t0) q (\x. rfa_nrm2 (G t0) Uf Wf x u) y0`;
    `lgrad2 ((G:real->real^3->real^3^3) t0) q y0`;
    `KR:real`; `KP:real`; `KM:real`; `K:real`; `B:real`; `A:real`; `L:real`; `sigma:real`]
   RFA_PUSH_ARRAY)) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                   `S:real^3^3`] RFA_LRM4_FT_SYMS) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
      MATCH_ACCEPT_TAC RFA_HP_FT_ANTI;
      REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_HM_FT_SYM THEN EXISTS_TAC `U:real^3->bool` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "anti" ACCEPT_TAC; USE_THEN "psd" ACCEPT_TAC; USE_THEN "null" ACCEPT_TAC;
      USE_THEN "nz" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `e:num`] THEN STRIP_TAC THEN
      USE_THEN "dU" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                     `S:real^3^3`; `e:num`; `i:num`] RFA_FT_METRIC) THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                     `S:real^3^3`; `e:num`; `j:num`] RFA_FT_METRIC) THEN
      REWRITE_TAC[DIMINDEX_3] THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      REFL_TAC;
      USE_THEN "bR" ACCEPT_TAC;
      USE_THEN "bP" ACCEPT_TAC; USE_THEN "bM" ACCEPT_TAC; USE_THEN "bric" ACCEPT_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      (* lgi^2 <= lgq |grad N|^2 in the frame *)
      FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                                 (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "lgrad2"
                                  with Failure _ -> false) &&
                                 can (find_term ((=) `rfa_nrm2:(real^3->real^3^3)->(real^3->(num->real^3)->real)->(real^3->(num->real^3)->real)->real^3->(num->real^3)->real`)) (lhs(concl th))
                              then SUBST_ALL_TAC th else failwith "no") THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Positivity of the perturbed form away from a touching                     *)
(* point.  |Z| <= C_Z (|u|^2 + |w|^2) from entrywise bounds                  *)
(* (RFA_HZ_ABS_BOUND, C_Z = 3 KM + 9 KP + 9 KR); a form that is not          *)
(* positive at (u, w) has barrier coefficient c <= C_Z (RFA_NULL_C_LE); at  *)
(* small times the form is positive definite when R(u,u) >= 0, Ric >= 0 and  *)
(* beta > 3 KM0 + 9 KP (6 KP + 1) / alpha (RFA_HZ_PD_SMALL, with the         *)
(* weighted bound RFA_QB_UW_W).                                              *)
(* ========================================================================= *)

let RFA_HZ_ABS_BOUND = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (u:num->num->real) (w:num->real) KR KP KM.
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3 ==> abs(R a b c d) <= KR) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(P a b c) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(M a b) <= KM)
     ==> abs(rfa_hz 3 R P M u w) <=
         (&3 * KM + &9 * KP + &9 * KR) *
         (sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R") (CONJUNCTS_THEN2 (LABEL_TAC "P") (LABEL_TAC "M"))) THEN
  SUBGOAL_THEN `&0 <= KR /\ &0 <= KP /\ &0 <= KM` STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "R" (MP_TAC o SPECL [`1`; `1`; `1`; `1`]) THEN
    REMOVE_THEN "P" (MP_TAC o SPECL [`1`; `1`; `1`]) THEN
    REMOVE_THEN "M" (MP_TAC o SPECL [`1`; `1`]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:num->num->real`; `KM:real`; `w:num->real`] RFA_QB_WW) THEN
  ANTS_TAC THENL [USE_THEN "M" ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`P:num->num->num->real`; `KP:real`; `u:num->num->real`; `w:num->real`]
         RFA_QB_UW) THEN
  ANTS_TAC THENL [USE_THEN "P" ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\a b c d. (R:num->num->num->num->real) a b d c`; `KR:real`;
                 `u:num->num->real`] RFA_QB_UU) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
      (R:num->num->num->num->real) a b c d * (u:num->num->real) a b * u d c)))) =
    sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
      R a b d c * u a b * u c d))))`
  ASSUME_TAC THENL [REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2)) /\
    &0 <= sum(1..3) (\a. (w:num->real) a pow 2)`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RFA_SUMSQ_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= KM * sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2)) /\
    &0 <= KP * sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2)) /\
    &0 <= KR * sum(1..3) (\a. (w:num->real) a pow 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfa_hz] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) then SUBST1_TAC th else failwith "no") THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
           (try rator(lhand(concl th)) = `abs:real->real` with Failure _ -> false)))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th)))) THEN
  REAL_ARITH_TAC);;

let RFA_NULL_C_LE = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (u:num->num->real) (w:num->real) pa pb cc KR KP KM.
     (!i j. u i j = --(u j i)) /\
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3 ==> abs(R a b c d) <= KR) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(P a b c) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(M a b) <= KM) /\
     &0 <= pa /\ &0 <= pb /\
     &0 < sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2) /\
     rfa_hz 3 (\a b c d. R a b c d + (pa + cc) * rfa_i4 a b c d) P
              (\a b. M a b + (pb + cc) * rfa_kd a b) u w <= &0
     ==> cc <= &3 * KM + &9 * KP + &9 * KR`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "anti") (CONJUNCTS_THEN2 (LABEL_TAC "bR")
    (CONJUNCTS_THEN2 (LABEL_TAC "bP") (CONJUNCTS_THEN2 (LABEL_TAC "bM") STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`; `M:num->num->real`;
                 `u:num->num->real`; `w:num->real`; `pa + cc:real`; `pb + cc:real`]
         RFA_HZ_PERTURB) THEN
  ANTS_TAC THENL [USE_THEN "anti" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM rfa_kd] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`; `M:num->num->real`;
                 `u:num->num->real`; `w:num->real`; `KR:real`; `KP:real`; `KM:real`]
         RFA_HZ_ABS_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [USE_THEN "bR" ACCEPT_TAC; USE_THEN "bP" ACCEPT_TAC;
                           USE_THEN "bM" ACCEPT_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2)) /\
    &0 <= sum(1..3) (\a. (w:num->real) a pow 2)`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RFA_SUMSQ_POS_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2))` THEN
  ABBREV_TAC `Y = sum(1..3) (\a. (w:num->real) a pow 2)` THEN
  ABBREV_TAC `CZ = &3 * KM + &9 * KP + &9 * KR` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (cc - CZ) * (X + Y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pa * X /\ &0 <= pb * Y` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
           can (find_term ((=) `rfa_hz:num->(num->num->num->num->real)->(num->num->num->real)->(num->num->real)->(num->num->real)->(num->real)->real`)) (concl th)))) THEN
  REAL_ARITH_TAC);;

let RFA_AMGM_W = prove
 (`!x y lam. &0 < lam ==> abs x * abs y <= (lam * x pow 2 + y pow 2 / lam) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `lam * abs x - abs y` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `(lam * x pow 2 + y pow 2 / lam) / &2 =
                (lam pow 2 * abs x pow 2 + abs y pow 2) / (&2 * lam)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW2_ABS] THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < lam ==> &0 < &2 * lam`] THEN
  REAL_ARITH_TAC);;

let RFA_QB_UW_W = prove
 (`!(A:num->num->num->real) B (u:num->num->real) (w:num->real) lam.
     &0 < lam /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 ==> abs(A a b c) <= B)
     ==> abs(sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. A a b c * u a b * w c)))) <=
         B * (&3 * lam * sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) +
              &9 * sum(1..3) (\a. w a pow 2) / lam) / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c.
                B * (lam * (u:num->num->real) a b pow 2 + (w:num->real) c pow 2 / lam) / &2)))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC RFA_ABS_SUM3_LE THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B * abs((u:num->num->real) i i') * abs((w:num->real) i'')` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_ABS_POS];
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC RFA_AMGM_W THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC]);;

let RFA_HZ_PD_SMALL = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M0:num->num->real)
    (ric:num->num->real) (u:num->num->real) (w:num->real) tau alpha beta KM0 KP.
     (!i j. u i j = --(u j i)) /\
     &0 <= sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
              R a b c d * u a b * u d c)))) /\
     &0 <= sum(1..3) (\a. sum(1..3) (\b. ric a b * w a * w b)) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(P a b c) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 ==> abs(M0 a b) <= KM0) /\
     &0 < sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2) /\
     &0 < tau /\ &0 < alpha /\
     &3 * KM0 + &9 * KP * (&6 * KP + &1) / alpha < beta
     ==> &0 < rfa_hz 3 (\a b c d. R a b c d + alpha * rfa_i4 a b c d) P
                     (\a b. (M0 a b + inv(&2 * tau) * ric a b) + beta * rfa_kd a b) u w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "anti") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bP")
    (CONJUNCTS_THEN2 (LABEL_TAC "bM") STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                 `\a b. (M0:num->num->real) a b + inv(&2 * tau) * (ric:num->num->real) a b`;
                 `u:num->num->real`; `w:num->real`; `alpha:real`; `beta:real`]
         RFA_HZ_PERTURB) THEN
  ANTS_TAC THENL [USE_THEN "anti" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM rfa_kd] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfa_hz] THEN
  SUBGOAL_THEN `&0 <= KP /\ &0 <= KM0` STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "bP" (MP_TAC o SPECL [`1`; `1`; `1`]) THEN
    REMOVE_THEN "bM" (MP_TAC o SPECL [`1`; `1`]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\a. sum(1..3) (\b. ((M0:num->num->real) a b + inv(&2 * tau) * ric a b) *
                                  (w:num->real) a * w b)) =
    sum(1..3) (\a. sum(1..3) (\b. M0 a b * w a * w b)) +
    inv(&2 * tau) * sum(1..3) (\a. sum(1..3) (\b. (ric:num->num->real) a b * w a * w b))`
  SUBST1_TAC THENL [REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`M0:num->num->real`; `KM0:real`; `w:num->real`] RFA_QB_WW) THEN
  ANTS_TAC THENL [USE_THEN "bM" ACCEPT_TAC; DISCH_TAC] THEN
  ABBREV_TAC `lam = alpha / (&6 * KP + &1)` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`P:num->num->num->real`; `KP:real`; `u:num->num->real`; `w:num->real`;
                 `lam:real`] RFA_QB_UW_W) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; USE_THEN "bP" ACCEPT_TAC];
                  DISCH_TAC] THEN
  ABBREV_TAC `X = sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2))` THEN
  ABBREV_TAC `Y = sum(1..3) (\a. (w:num->real) a pow 2)` THEN
  SUBGOAL_THEN `&0 <= X /\ &0 <= Y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN CONJ_TAC THEN RFA_SUMSQ_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `KP * (&3 * lam * X) <= alpha / &2 * X` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN
    SUBGOAL_THEN `KP * (&3 * alpha / (&6 * KP + &1) * X) =
                  ((&3 * KP) / (&6 * KP + &1)) * (alpha * X)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 <= KP` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `alpha / &2 * X = inv(&2) * (alpha * X)`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < &6 * KP + &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_LE_LDIV_EQ th]) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `KP * (&9 * Y / lam) = (&9 * KP * (&6 * KP + &1) / alpha) * Y` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN UNDISCH_TAC `&0 < alpha` THEN UNDISCH_TAC `&0 <= KP` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(&2 * tau) * sum(1..3) (\a. sum(1..3) (\b.
                  (ric:num->num->real) a b * (w:num->real) a * w b))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (alpha / &2) * X + (beta - (&3 * KM0 + &9 * KP * (&6 * KP + &1) / alpha)) * Y`
  MP_TAC THENL
   [ASM_CASES_TAC `&0 < X` THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 <= y ==> &0 < x + y`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `X = &0 /\ &0 < Y` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
           (try rator(lhand(concl th)) = `abs:real->real` with Failure _ -> false)))) THEN
  UNDISCH_TAC `KP * (&3 * lam * X) <= alpha / &2 * X` THEN
  UNDISCH_TAC `KP * (&9 * Y / lam) = (&9 * KP * (&6 * KP + &1) / alpha) * Y` THEN
  UNDISCH_TAC `&0 <= inv(&2 * tau) * sum(1..3) (\a. sum(1..3) (\b.
                  (ric:num->num->real) a b * (w:num->real) a * w b))` THEN
  UNDISCH_TAC `&0 <= sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
              (R:num->num->num->num->real) a b c d * (u:num->num->real) a b * u d c))))` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The choice of the constants (RFA_PUSH_COEFFS).  With                      *)
(* B = 12 KP + 324 KR + 2, A = 18 KR + 2, pa = d exp(B tau),                 *)
(* pb = e exp(A tau) / tau, sigma = (C + 1)(5 K + 1/tau) and L as below,     *)
(* the coefficients kX, kY of RFA_PUSH_CHART are positive for tau in         *)
(* [tau0, tauM] and 0 <= c <= C_Z, once d exp(B tauM) <= 1 and               *)
(* d exp(B tauM) (tauM^2 (6 KM0 + 36 KP + 36 K^2) + 3 K tauM + 1) < e.       *)
(* ========================================================================= *)

let RFA_PUSH_COEFFS = prove
 (`!KR KP KM0 K C CZ e d tau0 tauM tau cc B A pa pb KM sigma L.
     &0 <= KR /\ &0 <= KP /\ &0 <= KM0 /\ &0 <= K /\ &0 <= C /\ &0 <= CZ /\
     &0 < e /\ &0 < d /\ &0 < tau0 /\ tau0 <= tau /\ tau <= tauM /\
     &0 <= cc /\ cc <= CZ /\
     B = &12 * KP + &324 * KR + &2 /\ A = &18 * KR + &2 /\
     pa = d * exp(B * tau) /\ pb = e * exp(A * tau) / tau /\
     KM = KM0 + K / (&2 * tau) /\ sigma = (C + &1) * (&5 * K + inv tau) /\
     L = &2 * C + &2 * ((C + &1) * (&5 * K + inv tau0)) +
         (&6 * (KM0 + K / (&2 * tau0)) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
         &2 * (e * exp(A * tauM) / tau0) + &2 * CZ + &18 * KR +
         &2 * (&18 * K pow 2 + inv(&2 * tau0 pow 2)) + &1 /\
     d * exp(B * tauM) <= &1 /\
     d * exp(B * tauM) *
       (tauM pow 2 * (&6 * KM0 + &36 * KP + &36 * K pow 2) + &3 * K * tauM + &1) < e
     ==> &0 <= sigma /\ C * (&18 * K pow 2 + inv(&2 * tau pow 2)) <= sigma pow 2 /\
         &0 < B * pa - (pa + cc) * ((&12 * KP + &324 * KR) + (pa + cc)) +
              (L - &2 * C - &2 * sigma) * cc /\
         &0 < &2 / tau * (pb + cc) + A * pb - pb / tau -
              (pa + cc) * ((&6 * KM + &36 * KP) + &2 * (pb + cc)) -
              (&18 * KR) * (pb + cc) -
              &2 * (pa + cc) * (&18 * K pow 2 + inv(&2 * tau pow 2)) +
              (L - &2 * C - &2 * sigma) * cc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau /\ &0 < tauM /\ &0 <= B /\ &0 <= A` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv tau /\ inv tau <= inv tau0 /\ &0 < inv tau0 /\
                &1 <= tauM * inv tau` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM real_div] THEN
      FIRST_ASSUM(fun th -> if concl th = `&0 < tau` then REWRITE_TAC[MATCH_MP REAL_LE_RDIV_EQ th]
                            else failwith "no") THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = d * exp(B * tauM)` THEN
  (* pa *)
  SUBGOAL_THEN `&0 < pa /\ pa <= D` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pa = d * exp(B * tau)` THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "D" THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* pb *)
  SUBGOAL_THEN `&1 <= exp(A * tau) /\ exp(A * tau) <= exp(A * tauM)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + A * tau` THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pb = e * exp(A * tau) * inv tau` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `pb = e * exp(A * tau) / tau` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * exp(A * tau) * inv tau /\
                e * exp(A * tau) * inv tau <= e * exp(A * tauM) / tau0 /\
                e * inv tau pow 2 <= (e * exp(A * tau) * inv tau) * inv tau`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* normal forms with inv tau, inv tau0 *)
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `L:real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `sigma:real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `KM:real`)) THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_POW_INV] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_div; REAL_INV_MUL; GSYM REAL_POW_INV]) THEN
  ABBREV_TAC `it = inv tau` THEN ABBREV_TAC `it0 = inv tau0` THEN
  ABBREV_TAC `pbt = e * exp(A * tau) * it` THEN
  ABBREV_TAC `pb0 = e * exp(A * tauM) * it0` THEN
  (* sigma *)
  SUBGOAL_THEN `&0 <= &5 * K + it /\ &5 * K + it <= &5 * K + it0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (C + &1) * (&5 * K + it) /\
                (C + &1) * (&5 * K + it) <= (C + &1) * (&5 * K + it0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * (&18 * K pow 2 + inv(&2) * it pow 2) <= ((C + &1) * (&5 * K + it)) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C + &1) pow 2 * (&25 * K pow 2 + it pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * (&25 * K pow 2 + it pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(SPEC `K:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `it:real` REAL_LE_POW_2) THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MP_TAC(SPEC `C:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
          MP_TAC(SPEC `K:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `it:real` REAL_LE_POW_2) THEN
          REAL_ARITH_TAC]];
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      SUBGOAL_THEN `&0 <= K * it` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* products for the bounds of the brackets *)
  SUBGOAL_THEN `K * it <= K * it0 /\ it pow 2 <= it0 pow 2 /\ &0 <= it pow 2 /\
                &0 < it pow 2 /\ &0 <= pb0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "pb0" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K pow 2 /\ &0 <= it0 pow 2 /\ &0 <= K * it /\ &0 <= K * it0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the bracket of cc is nonnegative in both coefficients *)
  ABBREV_TAC `sg = (C + &1) * (&5 * K + it)` THEN
  ABBREV_TAC `sg0 = (C + &1) * (&5 * K + it0)` THEN
  SUBGOAL_THEN `&0 <= cc * ((&2 * C + &2 * sg0 +
         (&6 * (KM0 + K * inv(&2) * it0) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
         &2 * pb0 + &2 * CZ + &18 * KR +
         &2 * (&18 * K pow 2 + inv(&2) * it0 pow 2) + &1) - &2 * C - &2 * sg -
         (&12 * KP + &324 * KR) - &2 * pa - cc)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cc * (&2 * it + (&2 * C + &2 * sg0 +
         (&6 * (KM0 + K * inv(&2) * it0) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
         &2 * pb0 + &2 * CZ + &18 * KR +
         &2 * (&18 * K pow 2 + inv(&2) * it0 pow 2) + &1) - &2 * C - &2 * sg -
         (&6 * (KM0 + K * inv(&2) * it) + &36 * KP) - &2 * pa - &2 * pbt - &2 * cc -
         &18 * KR - &2 * (&18 * K pow 2 + inv(&2) * it pow 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pa <= pa * (&2 - pa) /\ &0 <= pbt * (&2 - &2 * pa)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= pa * (&1 - pa) ==> pa <= pa * (&2 - pa)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the main term of kY *)
  ABBREV_TAC `Z0 = &6 * KM0 + &36 * KP + &36 * K pow 2` THEN
  SUBGOAL_THEN `&0 <= Z0` ASSUME_TAC THENL [EXPAND_TAC "Z0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pa * (Z0 + &3 * K * it + it pow 2) <=
                D * (tauM pow 2 * Z0 + &3 * K * tauM + &1) * it pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * (Z0 + &3 * K * it + it pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= K * it` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= (tauM * it) pow 2 /\ it <= (tauM * it) * it` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `Z0 <= Z0 * (tauM * it) pow 2 /\ K * it <= K * ((tauM * it) * it)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D * (tauM pow 2 * Z0 + &3 * K * tauM + &1) * it pow 2 < e * it pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `D * (tauM pow 2 * Z0 + &3 * K * tauM + &1) < e` ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`D * (tauM pow 2 * Z0 + &3 * K * tauM + &1)`; `e:real`; `it pow 2`]
           REAL_LT_RMUL) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `B:real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `A:real`)) THEN
  let has v th = can (find_term ((=) v)) (concl th) in
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `pa <= pa * (&2 - pa)`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `&0 < pa`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> has `sg0:real` th && has `cc:real` th &&
                                            not (has `it:real` th))) THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `&0 <= pbt * (&2 - &2 * pa)`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `e * it pow 2 <= pbt * it`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
                                            has `Z0:real` th && has `pa:real` th)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_lt" (concl th) &&
                                            has `Z0:real` th && has `e:real` th)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> has `sg0:real` th && has `cc:real` th &&
                                            has `it:real` th)) THEN
    EXPAND_TAC "Z0" THEN REAL_ARITH_TAC]);;

