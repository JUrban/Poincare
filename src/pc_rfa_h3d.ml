(* ========================================================================= *)
(* Unit pc_rfa_h3d: the pointwise evaluation of the heat defect of           *)
(* Hamilton's Harnack quadratic at a point of a 3-dimensional chart Ricci    *)
(* flow, in a frame orthonormal for the metric there, and the identity       *)
(* defect = J + |Q|^2 (CLN 10.62, in the form with nabla W = 0, nabla U from *)
(* (10.59), and the terms of the defects of U, W kept):                      *)
(* RFA_HARNACK_DEFECT_3D.  Part 1 (general N): a small engine for smooth     *)
(* tensor fields (predicate rfa_sf, closure rules, a Leibniz conversion for  *)
(* lnabla over the tensor-algebra generators, frame evaluation).             *)
(* ========================================================================= *)

needs "src/pc_rfa_htens.ml";;
needs "src/pc_rfa_u17iface.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Smooth tensor fields and their closure rules.                             *)
(* ========================================================================= *)

let rfa_sf = new_definition
 `rfa_sf k (U:real^N->bool) (tf:real^N->(num->real^N)->real) <=>
    ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))`;;

let RFA_SF_LTPROD = prove
 (`!p q U (G:real^N->real^N^N) A B.
     metric_field U G /\ rfa_sf p U A /\ rfa_sf q U B ==> rfa_sf (p + q) U (ltprod p A B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_LTPROD_SMOOTH THEN ASM_MESON_TAC[metric_field]]);;

let RFA_SF_LTPERM = prove
 (`!k s U (A:real^N->(num->real^N)->real).
     s permutes 1..k /\ rfa_sf k U A ==> rfa_sf k U (ltperm s A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_LTPERM_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let RFA_SF_LTCONTR = prove
 (`!k U (G:real^N->real^N^N) A.
     metric_field U G /\ rfa_sf (k + 2) U A ==> rfa_sf k U (ltcontr G A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTCONTR_FIELD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_LTCONTR_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let RFA_SF_LNABLA = prove
 (`!k U (G:real^N->real^N^N) A.
     metric_field U G /\ rfa_sf k U A ==> rfa_sf (k + 1) U (lnabla k G A)`,
  REWRITE_TAC[rfa_sf] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_SIMP_TAC[]);;

let RFA_SF_ADD = prove
 (`!k U (G:real^N->real^N^N) A B.
     metric_field U G /\ rfa_sf k U A /\ rfa_sf k U B ==> rfa_sf k U (\y u. A y u + B y u)`,
  REWRITE_TAC[rfa_sf] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_MESON_TAC[metric_field]]);;

let RFA_SF_SUB = prove
 (`!k U (G:real^N->real^N^N) A B.
     metric_field U G /\ rfa_sf k U A /\ rfa_sf k U B ==> rfa_sf k U (\y u. A y u - B y u)`,
  REWRITE_TAC[rfa_sf] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RFA_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_MESON_TAC[metric_field]]);;

let RFA_SF_CMUL = prove
 (`!k U (G:real^N->real^N^N) A c.
     metric_field U G /\ rfa_sf k U A ==> rfa_sf k U (\y u. c * A y u)`,
  REWRITE_TAC[rfa_sf] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_MESON_TAC[metric_field]]);;

(* Base fields.                                                               *)

let RFA_SF_LRIC2 = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> rfa_sf 2 U (lric2 G)`,
  SIMP_TAC[rfa_sf; LRG_LRIC2_FIELD]);;

let RFA_SF_LMETRIC2 = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> rfa_sf 2 U (lmetric2 G)`,
  SIMP_TAC[rfa_sf; LRG_LMETRIC2_FIELD]);;

let RFA_SF_LRM4 = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> rfa_sf 4 U (lrm4 G)`,
  SIMP_TAC[rfa_sf; LRM4_TENSOR_FIELD]);;

let RFA_SF_SC = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> rfa_sf 0 U (rfa_sc G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rfa_sc (G:real^N->real^N^N) = ltcontr G (lric2 G)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfa_sc; ltcontr; lric2; lscalar] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MATCH_MP_TAC RFA_SF_LTCONTR THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[RFA_SF_LRIC2]]);;

let RFA_SF_HRIC = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> rfa_sf 2 U (rfa_hric G)`,
  SIMP_TAC[rfa_sf; RFA_HRIC_FIELD]);;

let RFA_SF_RMCOMM = prove
 (`!k U (G:real^N->real^N^N) A.
     metric_field U G /\ rfa_sf k U A ==> rfa_sf (k + 1) U (rfa_rmcomm k G A)`,
  REWRITE_TAC[rfa_sf] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`] RFA_RMCOMM_FIELD) THEN
  ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* An automatic prover for rfa_sf, and permutation proofs.                   *)
(* ========================================================================= *)

let RFA_SF_ZERO = prove
 (`!k U. open U ==> rfa_sf k (U:real^N->bool) (\y u. &0)`,
  REWRITE_TAC[rfa_sf; ltensor_field; LIFT_NUM; LINEAR_ZERO; SMOOTH_MAP_ON_CONST]);;

(* s permutes 1..k for an explicit s, by computing the inverse.             *)

let RFA_PERMUTES_CONV tm =
  let s, nk = dest_comb tm in
  let s = rand s in
  let k = dest_small_numeral (rand (rand tm)) in
  let ev n = dest_small_numeral (rhs(concl((REWRITE_CONV[swap] THENC DEPTH_CONV BETA_CONV THENC
                 REWRITE_CONV[ARITH] THENC NUM_REDUCE_CONV) (mk_comb(s, mk_small_numeral n))))) in
  let imgs = map (fun n -> (n, ev n)) (1--k) in
  let inv = map (fun (a, b) -> (b, a)) imgs in
  let mvar = `m:num` in
  let body = itlist (fun (b, a) acc ->
                 mk_cond(mk_eq(mvar, mk_small_numeral b), mk_small_numeral a, acc)) inv mvar in
  let invtm = mk_abs(mvar, body) in
  EQT_INTRO (prove(tm, MATCH_MP_TAC PERMUTES_BIJECTIONS THEN EXISTS_TAC invtm THEN
                       REWRITE_TAC[IN_NUMSEG; swap] THEN REPEAT STRIP_TAC THEN
                       REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC));;

(* A fast prover for  s permutes 1..k  (explicit s, numeral k): numerals are *)
(* substituted before the conditionals are evaluated.                       *)

let RFA_PERM_EVAL_CONV =
  REWRITE_CONV[swap] THENC DEPTH_CONV BETA_CONV THENC
  REPEATC (CHANGED_CONV (NUM_REDUCE_CONV THENC REWRITE_CONV[ARITH]));;

let RFA_PERMUTES_FAST tm =
  let s = rand(rator tm) in
  let numseg = rand tm in
  let k = dest_small_numeral (rand numseg) in
  let kt = mk_small_numeral k in
  let ev t = dest_small_numeral(rhs(concl(RFA_PERM_EVAL_CONV t))) in
  let imgs = map (fun n -> (n, ev (mk_comb(s, mk_small_numeral n)))) (1--k) in
  let mvar = `m:num` in
  let inv = itlist (fun (a, b) acc ->
              mk_cond(mk_eq(mvar, mk_small_numeral b), mk_small_numeral a, acc)) imgs mvar in
  let q = mk_abs(mvar, inv) in
  let xv = `x:num` in
  let inset t = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, t), numseg) in
  let numerals = map mk_small_numeral (1--k) in
  let split_in =
    SUBGOAL_THEN (list_mk_disj (map (fun i -> mk_eq(xv, i)) numerals)) MP_TAC THENL
     [UNDISCH_TAC (inset xv) THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) in
  let facts_out =
    list_mk_conj (map (fun i -> mk_neg(mk_eq(xv, i))) numerals @
                  map (fun j -> mk_neg(mk_comb(mk_comb(`(<=):num->num->bool`, xv),
                                              mk_small_numeral j))) (0--k)) in
  let out_tac =
    SUBGOAL_THEN (mk_disj(mk_eq(xv, `0`), mk_comb(mk_comb(`(<):num->num->bool`, kt), xv)))
      MP_TAC THENL
     [UNDISCH_TAC (mk_neg(inset xv)) THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
     [CONV_TAC(LAND_CONV RFA_PERM_EVAL_CONV) THEN REFL_TAC;
      SUBGOAL_THEN facts_out STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC (mk_comb(mk_comb(`(<):num->num->bool`, kt), xv)) THEN ARITH_TAC;
        ALL_TAC] THEN
      BETA_TAC THEN ASM_REWRITE_TAC[swap]] in
  let c1 f = prove(mk_forall(xv, mk_imp(inset xv, inset (mk_comb(f, xv)))),
                   X_GEN_TAC xv THEN DISCH_TAC THEN split_in THEN
                   CONV_TAC(LAND_CONV RFA_PERM_EVAL_CONV) THEN
                   REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC) in
  let c2 f = prove(mk_forall(xv, mk_imp(mk_neg(inset xv), mk_eq(mk_comb(f, xv), xv))),
                   X_GEN_TAC xv THEN DISCH_TAC THEN out_tac) in
  let th1 = c1 s and th2 = c2 s and th3 = c1 q and th4 = c2 q in
  let c5 f g thg thf =
    prove(mk_forall(xv, mk_eq(mk_comb(f, mk_comb(g, xv)), xv)),
          X_GEN_TAC xv THEN ASM_CASES_TAC (inset xv) THENL
           [split_in THEN CONV_TAC(LAND_CONV RFA_PERM_EVAL_CONV) THEN REFL_TAC;
            FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP thg th)) THEN
            FIRST_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP thf th))]) in
  let th5 = c5 s q th4 th2 and th6 = c5 q s th2 th4 in
  let pb = INST [numseg, `s:num->bool`] (ISPECL [s; q] PERMUTES_BIJECTIONS) in
  MP pb (end_itlist CONJ [th1; th2; th3; th4; th5; th6]);;


let rfa_perm_cache = Hashtbl.create 100;;

let RFA_PERMUTES_PROVE tm =
  try Hashtbl.find rfa_perm_cache tm with Not_found ->
  let th = try RFA_PERMUTES_FAST tm with Failure _ -> EQT_ELIM(RFA_PERMUTES_CONV tm) in
  (Hashtbl.add rfa_perm_cache tm th; th);;

let RFA_SF_XGRAD = prove
 (`!p q U (G:real^N->real^N^N) A B.
     metric_field U G /\ rfa_sf p U A /\ rfa_sf q U B
     ==> rfa_sf (p + q) U (rfa_xgrad p q G A B)`,
  REWRITE_TAC[rfa_sf] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`; `B:real^N->(num->real^N)->real`]
         RFA_XGRAD_FIELD) THEN
  ASM_SIMP_TAC[]);;

let rfa_sf_unfolds = ref ([] : thm list);;

(* The rfa_sf prover.  mf: |- metric_field U G.  Returns |- rfa_sf k U X.    *)

let rfa_sf_bases = ref [RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4; RFA_SF_SC; RFA_SF_HRIC];;

let rfa_sf_cache = Hashtbl.create 1000;;

let rec RFA_SF_PROVE mf tm =
  let key = (Hashtbl.hash_param 500 2000 tm, concl mf, tm) in
  try Hashtbl.find rfa_sf_cache key with Not_found ->
  let th = RFA_SF_PROVE_RAW mf tm in
  (Hashtbl.add rfa_sf_cache key th; th)
and RFA_SF_PROVE_RAW mf tm =
  let reduce = CONV_RULE NUM_REDUCE_CONV in
  try tryfind (fun th -> let th' = try MATCH_MP th mf with Failure _ -> th in
                         if aconv (rand(concl th')) tm then th' else failwith "")
              (!rfa_sf_bases)
  with Failure _ ->
  if is_abs tm then
    let y, b1 = dest_abs tm in let u, e = dest_abs b1 in
    (* eta *)
    if is_comb e && rand e = u && is_comb(rator e) && rand(rator e) = y &&
       not (vfree_in y (rator(rator e))) && not (vfree_in u (rator(rator e))) then
      let f = rator(rator e) in
      let th = RFA_SF_PROVE mf f in
      let eq = (ABS_CONV ETA_CONV THENC ETA_CONV) tm in
      CONV_RULE (RAND_CONV (REWR_CONV (SYM eq))) th
    else if is_const e && fst(dest_const e) = "real_of_num" || e = `&0` then
      let U = rand(rator(concl mf)) in
      MATCH_MP (SPECL [`0`; U] RFA_SF_ZERO) (CONJUNCT1(REWRITE_RULE[metric_field] mf))
    else
    let mklam e' = mk_abs(y, mk_abs(u, e')) in
    let sub2 th0 e1 e2 =
      let thA = RFA_SF_PROVE mf (mklam e1) and thB = RFA_SF_PROVE mf (mklam e2) in
      let th1 = BETA_RULE (MATCH_MP th0 (CONJ mf (CONJ thA thB))) in th1 in
    if is_binary "real_add" e then
      sub2 RFA_SF_ADD (lhand e) (rand e)
    else if is_binary "real_sub" e then
      sub2 RFA_SF_SUB (lhand e) (rand e)
    else if is_binary "real_mul" e && not (vfree_in y (lhand e)) && not (vfree_in u (lhand e)) then
      let la = mklam (rand e) in
      let thA = RFA_SF_PROVE mf la in
      let k = hd(snd(strip_comb(concl thA))) in
      let uu = rand(rator(concl mf)) and gg = rand(concl mf) in
      BETA_RULE (MP (ISPECL [k; uu; gg; la; lhand e] RFA_SF_CMUL) (CONJ mf thA))
    else failwith "RFA_SF_PROVE: lambda"
  else
  let f, args = strip_comb tm in
  let fname = if is_const f then fst(dest_const f) else "" in
  let unf = try Some(tryfind (fun th -> let th1 = SPEC_ALL th in
                                         let i = term_match [] (lhs(concl th1)) tm in
                                         INSTANTIATE i th1) (!rfa_sf_unfolds))
            with Failure _ -> None in
  match unf with
    Some eq -> CONV_RULE (RAND_CONV (REWR_CONV (SYM eq))) (RFA_SF_PROVE mf (rhs(concl eq)))
  | None ->
  if fname = "rfa_xgrad" then
    let [p; q; g; a; b] = args in
    let thA = RFA_SF_PROVE mf a and thB = RFA_SF_PROVE mf b in
    reduce (MATCH_MP (ISPECL [p; q] RFA_SF_XGRAD) (CONJ mf (CONJ thA thB)))
  else if fname = "ltprod" then
    let [p; a; b] = args in
    let thA = RFA_SF_PROVE mf a and thB = RFA_SF_PROVE mf b in
    let q = hd(snd(strip_comb(concl thB))) in
    reduce (MATCH_MP (ISPECL [p; q] RFA_SF_LTPROD) (CONJ mf (CONJ thA thB)))
  else if fname = "ltperm" then
    let [s; a] = args in
    let thA = RFA_SF_PROVE mf a in
    let k = hd(snd(strip_comb(concl thA))) in
    let pth = RFA_PERMUTES_PROVE (mk_comb(mk_comb(`(permutes):(num->num)->(num->bool)->bool`, s),
                                   mk_comb(mk_comb(`(..):num->num->num->bool`, `1`), k))) in
    MATCH_MP (ISPECL [k; s] RFA_SF_LTPERM) (CONJ pth thA)
  else if fname = "ltcontr" then
    let [g; a] = args in
    let thA = RFA_SF_PROVE mf a in
    let n = dest_small_numeral(hd(snd(strip_comb(concl thA)))) in
    MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPEC (mk_small_numeral(n - 2)) RFA_SF_LTCONTR))
             (CONJ mf thA)
  else if fname = "lnabla" then
    let [k; g; a] = args in
    let thA = RFA_SF_PROVE mf a in
    reduce (MATCH_MP RFA_SF_LNABLA (CONJ mf thA))
  else if fname = "rfa_rmcomm" then
    let [k; g; a] = args in
    let thA = RFA_SF_PROVE mf a in
    reduce (MATCH_MP RFA_SF_RMCOMM (CONJ mf thA))
  else failwith ("RFA_SF_PROVE: " ^ fname);;


(* ========================================================================= *)
(* Equality of fields on U, its congruences, and the Leibniz                 *)
(* rules for lnabla in field form.                                          *)
(* ========================================================================= *)

let rfa_eqon = new_definition
 `rfa_eqon (U:real^N->bool) (tf:real^N->(num->real^N)->real) tg <=>
    !y u. y IN U ==> tf y u = tg y u`;;

let RFA_EQON_REFL = prove
 (`!U (tf:real^N->(num->real^N)->real). rfa_eqon U tf tf`,
  REWRITE_TAC[rfa_eqon]);;

let RFA_EQON_TRANS = prove
 (`!U (f:real^N->(num->real^N)->real) g h.
     rfa_eqon U f g /\ rfa_eqon U g h ==> rfa_eqon U f h`,
  REWRITE_TAC[rfa_eqon] THEN MESON_TAC[]);;

let RFA_EQON_LTPROD = prove
 (`!p U (A:real^N->(num->real^N)->real) A' B B'.
     rfa_eqon U A A' /\ rfa_eqon U B B' ==> rfa_eqon U (ltprod p A B) (ltprod p A' B')`,
  REWRITE_TAC[rfa_eqon; ltprod] THEN MESON_TAC[]);;

let RFA_EQON_LTPERM = prove
 (`!s U (A:real^N->(num->real^N)->real) A'.
     rfa_eqon U A A' ==> rfa_eqon U (ltperm s A) (ltperm s A')`,
  REWRITE_TAC[rfa_eqon; ltperm] THEN MESON_TAC[]);;

let RFA_EQON_LTCONTR = prove
 (`!U (G:real^N->real^N^N) A A'.
     rfa_eqon U A A' ==> rfa_eqon U (ltcontr G A) (ltcontr G A')`,
  REWRITE_TAC[rfa_eqon; ltcontr] THEN REPEAT STRIP_TAC THEN
  RFA_SUM_EQ_TAC `a:num` THEN RFA_SUM_EQ_TAC `b:num` THEN ASM_SIMP_TAC[]);;

let RFA_EQON_ADD = prove
 (`!U (A:real^N->(num->real^N)->real) A' B B'.
     rfa_eqon U A A' /\ rfa_eqon U B B'
     ==> rfa_eqon U (\y u. A y u + B y u) (\y u. A' y u + B' y u)`,
  REWRITE_TAC[rfa_eqon] THEN MESON_TAC[]);;

let RFA_EQON_SUB = prove
 (`!U (A:real^N->(num->real^N)->real) A' B B'.
     rfa_eqon U A A' /\ rfa_eqon U B B'
     ==> rfa_eqon U (\y u. A y u - B y u) (\y u. A' y u - B' y u)`,
  REWRITE_TAC[rfa_eqon] THEN MESON_TAC[]);;

let RFA_EQON_CMUL = prove
 (`!U (A:real^N->(num->real^N)->real) A' c.
     rfa_eqon U A A' ==> rfa_eqon U (\y u. c * A y u) (\y u. c * A' y u)`,
  REWRITE_TAC[rfa_eqon] THEN MESON_TAC[]);;

let RFA_EQON_LNABLA = prove
 (`!k U (G:real^N->real^N^N) A A'.
     open U /\ rfa_eqon U A A' ==> rfa_eqon U (lnabla k G A) (lnabla k G A')`,
  REWRITE_TAC[rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[]);;

(* Leibniz rules in field form.                                             *)

let RFA_LNE_LTPROD = prove
 (`!p q U (G:real^N->real^N^N) A B.
     metric_field U G /\ rfa_sf p U A /\ rfa_sf q U B
     ==> rfa_eqon U (lnabla (p + q) G (ltprod p A B))
           (\y u. ltperm (\m. if m <= p then m else if m = p + 1 then p + q + 1
                              else if m <= p + q + 1 then m - 1 else m)
                    (ltprod (p + 1) (lnabla p G A) B) y u +
                  ltprod p A (lnabla q G B) y u)`,
  REWRITE_TAC[rfa_sf; rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`; `B:real^N->(num->real^N)->real`;
                 `y:real^N`; `u:num->real^N`] RFA_LNABLA_LTPROD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ltperm; ltprod] THEN BINOP_TAC THENL
   [BINOP_TAC THENL
     [MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`p + 1`; `U:real^N->bool`] THEN
      ASM_SIMP_TAC[LNABLA_TENSOR_FIELD] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      RFA_HC_TUPLE_TAC;
      MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`q:num`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((m + p + 1) <= p) /\ ~(m + p + 1 = p + 1) /\ (m + p + 1) <= p + q + 1 /\
                    (m + p + 1) - 1 = m + p` (fun th -> REWRITE_TAC[th]) THEN
      RFA_ARITH_TAC];
    REFL_TAC]);;

let RFA_LNE_LTPERM = prove
 (`!k s U (G:real^N->real^N^N) A.
     s permutes 1..k ==> rfa_eqon U (lnabla k G (ltperm s A)) (ltperm s (lnabla k G A))`,
  SIMP_TAC[rfa_eqon; RFA_LNABLA_LTPERM]);;

let RFA_LNE_LTCONTR = prove
 (`!k U (G:real^N->real^N^N) A.
     metric_field U G /\ rfa_sf (k + 2) U A
     ==> rfa_eqon U (lnabla k G (ltcontr G A)) (ltcontr G (lnabla (k + 2) G A))`,
  REWRITE_TAC[rfa_sf; rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RFA_LNABLA_LTCONTR THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RFA_LNE_ADD = prove
 (`!k U (G:real^N->real^N^N) A B.
     metric_field U G /\ rfa_sf k U A /\ rfa_sf k U B
     ==> rfa_eqon U (lnabla k G (\y u. A y u + B y u))
                    (\y u. lnabla k G A y u + lnabla k G B y u)`,
  REWRITE_TAC[rfa_sf; rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_MESON_TAC[metric_field]);;

let RFA_LNE_SUB = prove
 (`!k U (G:real^N->real^N^N) A B.
     metric_field U G /\ rfa_sf k U A /\ rfa_sf k U B
     ==> rfa_eqon U (lnabla k G (\y u. A y u - B y u))
                    (\y u. lnabla k G A y u - lnabla k G B y u)`,
  REWRITE_TAC[rfa_sf; rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_MESON_TAC[metric_field]);;

let RFA_LNE_CMUL = prove
 (`!k U (G:real^N->real^N^N) A c.
     metric_field U G /\ rfa_sf k U A
     ==> rfa_eqon U (lnabla k G (\y u. c * A y u)) (\y u. c * lnabla k G A y u)`,
  REWRITE_TAC[rfa_sf; rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_CMUL THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_MESON_TAC[metric_field]);;

let RFA_LNE_METRIC = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G ==> rfa_eqon U (lnabla 2 G (lmetric2 G)) (\y u. &0)`,
  SIMP_TAC[rfa_eqon] THEN MESON_TAC[LNABLA_METRIC]);;

let RFA_LNE_ZERO = prove
 (`!k U (G:real^N->real^N^N). rfa_eqon U (lnabla k G (\y u. &0)) (\y u. &0)`,
  REWRITE_TAC[rfa_eqon; RFA_LNABLA_ZERO]);;


(* ========================================================================= *)
(* The conversion pushing lnabla to the leaves.  RFA_LNF mf tm,              *)
(* for mf: |- metric_field U G and tm = lnabla k G X (a field), returns      *)
(* |- rfa_eqon U tm X' where X' is built from the generators with lnabla      *)
(* applied only to atoms.  rfa_lnf_unfolds: theorems                          *)
(* |- !U G. metric_field U G ==> rfa_eqon U (C G) L  or  |- C G = L  used to *)
(* rewrite non-generator fields before differentiating.                      *)
(* ========================================================================= *)

let RFA_EQON_OF_EQ = prove
 (`!U (f:real^N->(num->real^N)->real) g. f = g ==> rfa_eqon U f g`,
  SIMP_TAC[rfa_eqon]);;

let RFA_LTPROD_ZERO_R = prove
 (`!p (A:real^N->(num->real^N)->real). ltprod p A (\y u. &0) = (\y u. &0)`,
  REWRITE_TAC[FUN_EQ_THM; ltprod; REAL_MUL_RZERO]);;

let RFA_LTPROD_ZERO_L = prove
 (`!p (B:real^N->(num->real^N)->real). ltprod p (\y u. &0) B = (\y u. &0)`,
  REWRITE_TAC[FUN_EQ_THM; ltprod; REAL_MUL_LZERO]);;

let RFA_LTPERM_ZERO = prove
 (`!s. ltperm s ((\y u. &0):real^N->(num->real^N)->real) = (\y u. &0)`,
  REWRITE_TAC[FUN_EQ_THM; ltperm]);;

let RFA_LTCONTR_ZERO = prove
 (`!(G:real^N->real^N^N). ltcontr G (\y u. &0) = (\y u. &0)`,
  REWRITE_TAC[FUN_EQ_THM; ltcontr; REAL_MUL_RZERO; SUM_0]);;

let RFA_ZERO_CONV =
  TOP_DEPTH_CONV BETA_CONV THENC
  REWRITE_CONV[RFA_LTPROD_ZERO_R; RFA_LTPROD_ZERO_L; RFA_LTPERM_ZERO; RFA_LTCONTR_ZERO;
               REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID; REAL_ADD_LID; REAL_SUB_RZERO;
               REAL_SUB_REFL];;

let rfa_lnf_unfolds = ref ([] : thm list);;

let rfa_eqon_hooks = ref ([] : (thm -> term -> thm) list);;

let rfa_lnf_cache = Hashtbl.create 1000;;

let rec RFA_LNF mf tm =
  let key = (Hashtbl.hash_param 500 2000 tm, concl mf, tm) in
  try Hashtbl.find rfa_lnf_cache key with Not_found ->
  let th = RFA_LNF_RAW mf tm in
  (Hashtbl.add rfa_lnf_cache key th; th)
and RFA_LNF_RAW mf tm =
  let uu = rand(rator(concl mf)) and gg = rand(concl mf) in
  let openU = CONJUNCT1(REWRITE_RULE[metric_field] mf) in
  let refl t = ISPECL [uu; t] RFA_EQON_REFL in
  let has_zero t = can (find_term (fun s -> is_abs s && (let _, b = dest_abs s in
                        is_abs b && snd(dest_abs b) = `&0`))) t in
  let trans th1 th2 =
    let th = BETA_RULE (MATCH_MP RFA_EQON_TRANS (CONJ th1 th2)) in
    if has_zero (rand(concl th)) then CONV_RULE (RAND_CONV RFA_ZERO_CONV) th else th in
  let reduce = CONV_RULE NUM_REDUCE_CONV in
  let f0, args0 = strip_comb tm in
  let [k; g; x] = args0 in
  let kn = dest_small_numeral k in
  let lnab n t = list_mk_comb(f0, [mk_small_numeral n; g; t]) in
  (* try an unfolding of x first *)
  let unfolded =
    try Some(tryfind (fun th ->
      let th1 = SPEC_ALL(try MATCH_MP th mf with Failure _ -> th) in
      if is_eq(concl th1) then
        let i = term_match [] (lhs(concl th1)) x in
        let eqth = INSTANTIATE i th1 in
        MP (ISPECL [uu; lhs(concl eqth); rhs(concl eqth)] RFA_EQON_OF_EQ) eqth
      else
        let i = term_match [] (rand(rator(concl th1))) x in
        INSTANTIATE i th1) (!rfa_lnf_unfolds))
    with Failure _ ->
      try Some(tryfind (fun f -> f mf x) (!rfa_eqon_hooks)) with Failure _ -> None in
  match unfolded with
    Some th ->
      let x' = rand(concl th) in
      let th0 = MATCH_MP (ISPECL [k; uu; gg] RFA_EQON_LNABLA) (CONJ openU th) in
      trans th0 (RFA_LNF mf (lnab kn x'))
  | None ->
  if is_abs x then
    let y, b1 = dest_abs x in let u, e = dest_abs b1 in
    if is_comb e && rand e = u && is_comb(rator e) && rand(rator e) = y &&
       not (vfree_in y (rator(rator e))) && not (vfree_in u (rator(rator e))) then
      let f = rator(rator e) in
      let eq = (ABS_CONV ETA_CONV THENC ETA_CONV) x in
      let eq2 = AP_TERM (mk_comb(mk_comb(f0, k), g)) eq in
      let th0 = MP (ISPECL [uu; lhs(concl eq2); rhs(concl eq2)] RFA_EQON_OF_EQ) eq2 in
      trans th0 (RFA_LNF mf (lnab kn f))
    else if e = `&0` then ISPECL [k; uu; gg] RFA_LNE_ZERO
    else
    let mklam e' = mk_abs(y, mk_abs(u, e')) in
    let lin rule e1 e2 cong =
      let thA = RFA_SF_PROVE mf (mklam e1) and thB = RFA_SF_PROVE mf (mklam e2) in
      let th0 = BETA_RULE (MATCH_MP rule (CONJ mf (CONJ thA thB))) in
      let thL1 = RFA_LNF mf (lnab kn (mklam e1)) and thL2 = RFA_LNF mf (lnab kn (mklam e2)) in
      trans th0 (MATCH_MP cong (CONJ thL1 thL2)) in
    if is_binary "real_add" e then lin RFA_LNE_ADD (lhand e) (rand e) RFA_EQON_ADD
    else if is_binary "real_sub" e then lin RFA_LNE_SUB (lhand e) (rand e) RFA_EQON_SUB
    else if is_binary "real_mul" e && not (vfree_in y (lhand e)) && not (vfree_in u (lhand e)) then
      let la = mklam (rand e) in
      let thA = RFA_SF_PROVE mf la in
      let th0 = BETA_RULE (MP (ISPECL [k; uu; gg; la; lhand e] RFA_LNE_CMUL) (CONJ mf thA)) in
      let thL = RFA_LNF mf (lnab kn la) in
      let fl = rand(rator(concl thL)) and fr = rand(concl thL) in
      trans th0 (MP (ISPECL [uu; fl; fr; lhand e] RFA_EQON_CMUL) thL)
    else failwith "RFA_LNF: lambda"
  else
  let fx, ax = strip_comb x in
  let fname = if is_const fx then fst(dest_const fx) else "" in
  if fname = "ltprod" then
    let [p; a; b] = ax in
    let thA = RFA_SF_PROVE mf a and thB = RFA_SF_PROVE mf b in
    let q = hd(snd(strip_comb(concl thB))) in
    let th0 = reduce (MATCH_MP (ISPECL [p; q] RFA_LNE_LTPROD) (CONJ mf (CONJ thA thB))) in
    let pn = dest_small_numeral p and qn = dest_small_numeral q in
    let thLA = RFA_LNF mf (lnab pn a) and thLB = RFA_LNF mf (lnab qn b) in
    (* congruence for  \y u. ltperm s (ltprod (p+1) LA b) y u + ltprod p a LB y u *)
    let r0 = rand(concl th0) in
    let y, b1 = dest_abs r0 in let u, e = dest_abs b1 in
    let t1 = rator(rator(lhand e)) and t2 = rator(rator(rand e)) in
    let s = rand(rator t1) in
    let th1 = MATCH_MP (ISPEC s RFA_EQON_LTPERM)
                (MATCH_MP (ISPEC (mk_small_numeral(pn + 1)) RFA_EQON_LTPROD)
                          (CONJ thLA (refl b))) in
    let th2 = MATCH_MP (ISPEC p RFA_EQON_LTPROD) (CONJ (refl a) thLB) in
    trans th0 (MATCH_MP RFA_EQON_ADD (CONJ th1 th2))
  else if fname = "ltperm" then
    let [s; a] = ax in
    let pth = RFA_PERMUTES_PROVE
      (mk_comb(mk_comb(`(permutes):(num->num)->(num->bool)->bool`, s),
               mk_comb(mk_comb(`(..):num->num->num->bool`, `1`), k))) in
    let th0 = MATCH_MP (ISPECL [k; s; uu; gg; a] RFA_LNE_LTPERM) pth in
    let thL = RFA_LNF mf (lnab kn a) in
    trans th0 (MATCH_MP (ISPEC s RFA_EQON_LTPERM) thL)
  else if fname = "ltcontr" then
    let [g2; a] = ax in
    let thA = RFA_SF_PROVE mf a in
    let th0 = reduce (MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPEC k RFA_LNE_LTCONTR))
                               (CONJ mf thA)) in
    let thL = RFA_LNF mf (lnab (kn + 2) a) in
    trans th0 (MATCH_MP (ISPECL [uu; gg] RFA_EQON_LTCONTR) thL)
  else if fname = "lmetric2" then MATCH_MP RFA_LNE_METRIC mf
  else if fname = "lnabla" then
    let [j; g2; yy] = ax in
    let thY = RFA_LNF mf x in
    if aconv (rand(concl thY)) x then refl tm else
    let th0 = MATCH_MP (ISPECL [k; uu; gg] RFA_EQON_LNABLA) (CONJ openU thY) in
    trans th0 (RFA_LNF mf (lnab kn (rand(concl thY))))
  else refl tm;;


(* ========================================================================= *)
(* Frame evaluation of contractions.  S is a frame matrix at y:              *)
(* matrix_inv(G y) = transp S ** S; the frame vectors are transp S ** basis i.*)
(* ========================================================================= *)

let RFA_TF_BILIN12 = prove
 (`!k U (A:real^N->(num->real^N)->real) y w.
     ltensor_field (k + 2) U A /\ y IN U
     ==> (!z. linear (\x. lift(A y (\m. if m = 1 then x else if m = 2 then z else w(m - 2))))) /\
         (!x. linear (\z. lift(A y (\m. if m = 1 then x else if m = 2 then z else w(m - 2)))))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`k + 2`; `U:real^N->bool`; `A:real^N->(num->real^N)->real`; `y:real^N`;
                   `1`; `\v:real^N. \m. if m = 1 then v else if m = 2 then z else
                                        (w:num->real^N)(m - 2)`] RFA_TF_LINEAR_SLOT);
    MP_TAC(ISPECL [`k + 2`; `U:real^N->bool`; `A:real^N->(num->real^N)->real`; `y:real^N`;
                   `2`; `\v:real^N. \m. if m = 1 then x else if m = 2 then v else
                                        (w:num->real^N)(m - 2)`] RFA_TF_LINEAR_SLOT)] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN REPEAT STRIP_TAC THEN
                   ASM_REWRITE_TAC[ARITH] THEN TRY(RFA_HC_TUPLE_TAC); ALL_TAC]) THEN
  REWRITE_TAC[ETA_AX]);;

let RFA_LTCONTR_FRAMEV = prove
 (`!k U (G:real^N->real^N^N) A y (S:real^N^N) w.
     ltensor_field (k + 2) U A /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> ltcontr G A y w =
         sum(1..dimindex(:N)) (\s. A y (\m. if m = 1 then transp S ** basis s
                                           else if m = 2 then transp S ** basis s
                                           else w(m - 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltcontr] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `\x z. (A:real^N->(num->real^N)->real) y
                          (\m. if m = 1 then x else if m = 2 then z else (w:num->real^N)(m - 2))`]
         RFA_TRACE_FRAME) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_TF_BILIN12 THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC]);;

let RFA_XGRAD_FRAMEV = prove
 (`!p q U (G:real^N->real^N^N) A B y (S:real^N^N) u.
     ltensor_field (p + 1) U (lnabla p G A) /\ ltensor_field (q + 1) U (lnabla q G B) /\
     y IN U /\ matrix_inv(G y) = transp S ** S
     ==> rfa_xgrad p q G A B y u =
         sum(1..dimindex(:N)) (\s.
           lnabla p G A y (\m. if m = p + 1 then transp S ** basis s else u m) *
           lnabla q G B y (\m. if m = q + 1 then transp S ** basis s else u(m + p)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_xgrad] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `\x z. lnabla p (G:real^N->real^N^N) A y
                          (\m. if m = p + 1 then x else (u:num->real^N) m) *
                        lnabla q G B y (\m. if m = q + 1 then z else u(m + p))`]
         RFA_TRACE_FRAME) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THENL
     [MATCH_MP_TAC RFA_LINEAR_LIFT_MUL_L THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p + 1`; `U:real^N->bool`; `lnabla p (G:real^N->real^N^N) A`; `y:real^N`;
                     `p + 1`; `\v:real^N. \m. if m = p + 1 then v else (u:num->real^N) m`]
             RFA_TF_LINEAR_SLOT);
      MATCH_MP_TAC RFA_LINEAR_LIFT_MUL_R THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`q + 1`; `U:real^N->bool`; `lnabla q (G:real^N->real^N^N) B`; `y:real^N`;
                     `q + 1`; `\v:real^N. \m. if m = q + 1 then v else (u:num->real^N)(m + p)`]
             RFA_TF_LINEAR_SLOT)] THEN
    BETA_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_THEN ACCEPT_TAC]);;


(* ========================================================================= *)
(* rfa_rmcomm through the generators (for its covariant                      *)
(* derivative and its frame value).                                         *)
(* ========================================================================= *)

let RFA_SUM3_ROT = prove
 (`!n k (f:num->num->num->real).
     sum(1..n) (\a. sum(1..n) (\b. sum(1..k) (\i. f a b i))) =
     sum(1..k) (\i. sum(1..n) (\a. sum(1..n) (\b. f a b i)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN REFL_TAC);;

let RFA_RMCOMM_COMB = prove
 (`!k U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field k U A /\ (!u. smooth_map_on U (\x. lift(A x u))) /\
     y IN U
     ==> rfa_rmcomm k G A y u =
         sum(1..k) (\i.
           ltcontr G (ltcontr G
             (ltperm (\m. if m = 1 then 4 else if m = 2 then k + 5 else if m = 3 then 1
                          else if m = 4 then i + 4 else if m = i + 4 then 2
                          else if m = k + 5 then 3 else m)
                     (ltprod 4 (lrm4 G) (lnabla k G A)))) y u +
           ltcontr G (ltcontr G
             (ltperm (\m. if m = 1 then 3 else if m = 2 then k + 5 else if m = 3 then 1
                          else if m = 4 then i + 4 else if m = i + 4 then 2
                          else if m = k + 5 then 4 else m)
                     (ltprod 4 (lrm4 G) (lnabla k G A)))) y u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field (k + 1) U (lnabla k (G:real^N->real^N^N) A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LNABLA_TENSOR_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 4 U (lrm4 (G:real^N->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRM4_TENSOR_FIELD]; ALL_TAC] THEN
  REWRITE_TAC[rfa_rmcomm] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN GEN_REWRITE_TAC LAND_CONV [RFA_SUM3_ROT] THEN
  RFA_SUM_EQ_TAC `i:num` THEN
  REWRITE_TAC[ltcontr; ltperm; ltprod] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  BINOP_TAC THEN (RFA_SUM_EQ_TAC `a:num` THEN RFA_SUM_EQ_TAC `b:num` THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THEN
  MATCH_MP_TAC RFA_TF_AGREE THENL
   [MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL
     [RFA_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN BETA_TAC THEN
    REWRITE_TAC[ARITH] THEN
    (SUBGOAL_THEN `~(k + 5 = 1) /\ ~(k + 5 = 2) /\ (k + 5) - 2 = k + 3 /\ ~(k + 3 = 1) /\
                   ~(k + 3 = 2) /\ (k + 3) - 2 = k + 1 /\ ~(i + 4 = 1) /\ ~(i + 4 = 2) /\
                   (i + 4) - 2 = i + 2 /\ ~(i + 2 = 1) /\ ~(i + 2 = 2) /\ (i + 2) - 2 = i`
     STRIP_ASSUME_TAC THENL [RFA_ARITH_TAC; ASM_REWRITE_TAC[]]);
    MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(m + 4 = 1) /\ ~(m + 4 = 2) /\ ~(m + 4 = 3) /\ ~(m + 4 = 4) /\
                  (m + 4 = i + 4 <=> m = i) /\ (m + 4 = k + 5 <=> m = k + 1) /\
                  (m + 4) - 2 = m + 2 /\ ~(m + 2 = 1) /\ ~(m + 2 = 2) /\ (m + 2) - 2 = m`
    STRIP_ASSUME_TAC THENL [RFA_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH] THEN
    ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[ARITH] THEN
    ASM_CASES_TAC `m = k + 1` THEN ASM_REWRITE_TAC[ARITH]]));;


(* ========================================================================= *)
(* Frame evaluation.  Frame tuples rfa_ft S l (l a list of                   *)
(* indices).  RFA_FRV_CONV mf yth sth (mf: |- metric_field U G,              *)
(* yth: |- y IN U, sth: |- matrix_inv(G y) = transp S ** S) expands           *)
(* applications X y w of composite fields into arithmetic over atoms;        *)
(* RFA_ATOM_CONV then puts each atom A y w into the form A y (rfa_ft S l).    *)
(* ========================================================================= *)

let rfa_ft = new_definition
 `rfa_ft (S:real^N^N) (l:num list) = \m. transp S ** basis (EL (m - 1) l)`;;

let RFA_LTPROD_APP = prove
 (`!p (A:real^N->(num->real^N)->real) B y w.
     ltprod p A B y w = A y w * B y (\m. w(m + p))`,
  REWRITE_TAC[ltprod]);;

let RFA_LTPERM_APP = prove
 (`!s (A:real^N->(num->real^N)->real) y w. ltperm s A y w = A y (\m. w(s m))`,
  REWRITE_TAC[ltperm]);;

let RFA_EQON_APP = prove
 (`!U (f:real^N->(num->real^N)->real) g y w.
     rfa_eqon U f g /\ y IN U ==> f y w = g y w`,
  SIMP_TAC[rfa_eqon]);;

let rfa_frv_unfolds = ref ([] : thm list);;


(* Atom normalization: A y w  ->  A y (rfa_ft S [v1; ...; vk]) for a k-field   *)
(* atom A, when w m reduces to transp S ** basis v_m for m = 1..k.            *)

let RFA_TV_RW1 = REWRITE_CONV[rfa_ft; swap];;
let RFA_TV_RW2 = REWRITE_CONV[EL_CONS; ARITH; COND_ID];;

let RFA_TUPLE_VAL_CONV =
  RFA_TV_RW1 THENC DEPTH_CONV BETA_CONV THENC
  REPEATC (CHANGED_CONV (NUM_REDUCE_CONV THENC RFA_TV_RW2));;

let rfa_atom_heads = ref ["lric2"; "lnabla"; "lrm4"; "lmetric2"];;

let rfa_numseg_cases_cache = Hashtbl.create 10;;

let RFA_NUMSEG_CASES k =
  try Hashtbl.find rfa_numseg_cases_cache k with Not_found ->
  let mv = `m:num` in
  let le = `(<=):num->num->bool` in
  let hyp = mk_conj(mk_comb(mk_comb(le, `1`), mv), mk_comb(mk_comb(le, mv), mk_small_numeral k)) in
  let concl = list_mk_disj (map (fun i -> mk_eq(mv, mk_small_numeral i)) (1--k)) in
  let th = GEN mv (ARITH_RULE (mk_imp(hyp, concl))) in
  (Hashtbl.add rfa_numseg_cases_cache k th; th);;

let rfa_atom_cache = Hashtbl.create 1000;;

let RFA_TUPNORM_RAW mf yth stm tm =
  let x, args = strip_comb tm in
  if length args < 2 then failwith "RFA_TUPNORM" else
  let fld = list_mk_comb(x, butlast(butlast args)) in
  let y = el (length args - 2) args and w = last args in
  if not (aconv y (lhand(concl yth))) then failwith "RFA_TUPNORM: point" else
  let thA = REWRITE_RULE[rfa_sf] (RFA_SF_PROVE mf fld) in
  let kt = hd(snd(strip_comb(concl(CONJUNCT1 thA)))) in
  let k = dest_small_numeral kt in
  (match (try Some(dest_comb(rator w), rand w) with Failure _ -> None) with
     Some((c, s0), l0) when is_const c && fst(dest_const c) = "rfa_ft" &&
                                (try length(dest_list l0) = k with Failure _ -> false) ->
       failwith "canonical"
   | _ -> ());
  let vals = map (fun i -> RFA_TUPLE_VAL_CONV (mk_comb(w, mk_small_numeral i))) (1--k) in
  let vs = map (fun th -> rand(rand(rhs(concl th)))) vals in
  let lst = mk_list(vs, `:num`) in
  let w' = list_mk_icomb "rfa_ft" [stm; lst] in
  let vals' = map (fun i -> RFA_TUPLE_VAL_CONV (mk_comb(w', mk_small_numeral i))) (1--k) in
  let eqs = map2 (fun th th' -> TRANS th (SYM th')) vals vals' in
  let mv = `m:num` in
  let le = `(<=):num->num->bool` in
  let hyp = mk_conj(mk_comb(mk_comb(le, `1`), mv), mk_comb(mk_comb(le, mv), kt)) in
  let goal = mk_forall(mv, mk_imp(hyp, mk_eq(mk_comb(w, mv), mk_comb(w', mv)))) in
  let slots = if k = 0 then prove(goal, ARITH_TAC) else
    prove(goal, GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SPEC mv (RFA_NUMSEG_CASES k))) THEN
                DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC eqs) in
  let th = MP (ISPECL [kt; rand(rator(concl(CONJUNCT1 thA))); fld; y; w; w'] RFA_TF_AGREE)
             (CONJ (CONJUNCT1 thA) (CONJ yth slots)) in
  th;;

let RFA_TUPNORM_CONV mf yth stm tm =
  let key = (Hashtbl.hash_param 500 2000 tm, concl mf, tm) in
  try Hashtbl.find rfa_atom_cache key with Not_found ->
  let th = RFA_TUPNORM_RAW mf yth stm tm in
  (Hashtbl.add rfa_atom_cache key th; th);;

let RFA_ATOM_CONV = RFA_TUPNORM_CONV;;

let RFA_FRV_STEP0 mf yth sth tm =
  let x, args = strip_comb tm in
  if length args < 2 then failwith "RFA_FRV_STEP" else
  let fld = list_mk_comb(x, butlast(butlast args)) in
  let y = el (length args - 2) args in
  if not (aconv y (lhand(concl yth))) then failwith "RFA_FRV_STEP: point" else
  if is_abs fld then (RATOR_CONV BETA_CONV THENC BETA_CONV) tm else
  let fh, fa = strip_comb fld in
  let fname = if is_const fh then fst(dest_const fh) else "" in
  if fname = "ltprod" then REWR_CONV RFA_LTPROD_APP tm
  else if fname = "ltperm" then REWR_CONV RFA_LTPERM_APP tm
  else if fname = "ltcontr" then
    let [g; a] = fa in
    let thA = REWRITE_RULE[rfa_sf] (RFA_SF_PROVE mf a) in
    let n = dest_small_numeral(hd(snd(strip_comb(concl(CONJUNCT1 thA))))) in
    let uu = rand(rator(concl mf)) in
    let lem = CONV_RULE NUM_REDUCE_CONV (ISPECL [mk_small_numeral(n - 2); uu; g] RFA_LTCONTR_FRAMEV) in
    REWR_CONV (MATCH_MP lem (CONJ (CONJUNCT1 thA) (CONJ yth sth))) tm
  else if fname = "rfa_xgrad" then
    let [p; q; g; a; b] = fa in
    let la = list_mk_icomb "lnabla" [p; g; a] and lb = list_mk_icomb "lnabla" [q; g; b] in
    let thA = CONJUNCT1(REWRITE_RULE[rfa_sf] (RFA_SF_PROVE mf la))
    and thB = CONJUNCT1(REWRITE_RULE[rfa_sf] (RFA_SF_PROVE mf lb)) in
    let lem = ISPECL [p; q; rand(rator(concl mf)); g] RFA_XGRAD_FRAMEV in
    let th = MATCH_MP (CONV_RULE NUM_REDUCE_CONV lem)
               (CONJ (CONV_RULE NUM_REDUCE_CONV thA) (CONJ (CONV_RULE NUM_REDUCE_CONV thB)
                     (CONJ yth sth))) in
    (REWR_CONV th THENC NUM_REDUCE_CONV) tm
  else if fname = "lnabla" then
    let thL = RFA_LNF mf fld in
    if aconv (rand(concl thL)) fld then failwith "RFA_FRV_STEP: atom" else
    REWR_CONV (MATCH_MP RFA_EQON_APP (CONJ thL yth)) tm
  else
    try REWR_CONV (MATCH_MP RFA_EQON_APP (CONJ (tryfind (fun f -> f mf fld) (!rfa_eqon_hooks)) yth)) tm
    with Failure _ ->
    tryfind (fun th -> let th1 = SPEC_ALL(try MATCH_MP th mf with Failure _ -> th) in
                       let th2 = if is_eq(concl th1) then th1
                                 else MATCH_MP RFA_EQON_APP (CONJ th1 yth) in
                       try REWR_CONV th2 tm with Failure _ ->
                       (RATOR_CONV (RATOR_CONV (REWR_CONV th2)) THENC
                        TRY_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV)) tm) (!rfa_frv_unfolds);;

let RFA_FRV_STEP mf yth sth tm =
  let stm = rand(rand(concl sth)) in
  let th = RFA_FRV_STEP0 mf yth sth tm in
  CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV (RFA_TUPNORM_CONV mf yth stm))) th;;

let RFA_FRV_CONV mf yth sth =
  TOP_DEPTH_CONV (fun t -> RFA_FRV_STEP mf yth sth t) THENC DEPTH_CONV BETA_CONV;;


(* ========================================================================= *)
(* Unfoldings used by the engine for the Harnack tensors.                    *)
(* ========================================================================= *)

let RFA_SC_CONTR = prove
 (`!(G:real^N->real^N^N). rfa_sc G = ltcontr G (lric2 G)`,
  REWRITE_TAC[FUN_EQ_THM; rfa_sc; ltcontr; lric2; lscalar] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let RFA_LAMBDA_OF_PTWISE th =
  (* from |- !x1..xn y u. C x1..xn y u = e  to  |- !x1..xn. C x1..xn = \y u. e *)
  let th1 = SPEC_ALL th in
  let l, r = dest_eq(concl th1) in
  let c, args = strip_comb l in
  let n = length args in
  let y = el (n - 2) args and u = el (n - 1) args in
  let f = list_mk_comb(c, butlast(butlast args)) in
  let goal = mk_eq(f, mk_abs(y, mk_abs(u, r))) in
  GEN_ALL(prove(goal, REWRITE_TAC[FUN_EQ_THM; th]));;

let RFA_HRIC3_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_hric3;;
let RFA_HDR_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_hdr;;
let RFA_HDDR_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_hddr;;
let RFA_HP_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_hP;;
let RFA_HM_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_hM;;
let RFA_HHM_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_hhM;;
let RFA_HHRIC3_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_hhric3;;
let RFA_H3_LAMBDA = RFA_LAMBDA_OF_PTWISE rfa_h3;;

(* In dimension 3, as equalities on U.                                        *)

let RFA_EQON_HRIC_3D = prove
 (`!U (G:real^3->real^3^3). metric_field U G ==> rfa_eqon U (rfa_hric G) (rfa_hric3 G)`,
  REWRITE_TAC[rfa_eqon] THEN MESON_TAC[RFA_HRIC_3D]);;

let RFA_EQON_LRM4_3D = prove
 (`!U (G:real^3->real^3^3). metric_field U G ==> rfa_eqon U (lrm4 G) (rfa_h3 G (lric2 G))`,
  REWRITE_TAC[rfa_eqon] THEN MESON_TAC[RFA_LRM4_H3]);;

(* rfa_rmcomm k G A for numeral k as an explicit sum of generator terms, on U. *)

let RFA_SUM_EXPAND_CONV =
  REWRITE_CONV[SUM_1; SUM_2; SUM_3; SUM_4] THENC DEPTH_CONV BETA_CONV THENC
  NUM_REDUCE_CONV;;

let RFA_RMCOMM_EQON mf tm =
  let fh, fargs = strip_comb tm in
  if not (is_const fh && fst(dest_const fh) = "rfa_rmcomm" && length fargs = 3)
  then failwith "RFA_RMCOMM_EQON" else
  let [k; g; a] = fargs in
  let uu = rand(rator(concl mf)) in
  let thA = REWRITE_RULE[rfa_sf] (RFA_SF_PROVE mf a) in
  let ty = hd(snd(dest_type(type_of g))) in
  let yv = mk_var("y", ty) and uv = mk_var("u", mk_type("fun", [`:num`; ty])) in
  let yth = ASSUME (mk_comb(mk_comb(mk_const("IN", [ty, aty]), yv), uu)) in
  let th0 = MATCH_MP (ISPECL [k; uu; g; a; yv; uv] RFA_RMCOMM_COMB)
                     (CONJ mf (CONJ (CONJUNCT1 thA) (CONJ (CONJUNCT2 thA) yth))) in
  let th1 = CONV_RULE (RAND_CONV RFA_SUM_EXPAND_CONV) th0 in
  let e = rand(concl th1) in
  let lam = mk_abs(yv, mk_abs(uv, e)) in
  let gth = GEN yv (GEN uv (DISCH (concl yth) th1)) in
  let dth = CONV_RULE (RAND_CONV (DEPTH_CONV BETA_CONV)) (ISPECL [uu; tm; lam] rfa_eqon) in
  EQ_MP (SYM dth) gth;;

rfa_eqon_hooks := [RFA_RMCOMM_EQON];;

(* Engine forms (generators only) of P, Lap Ric, M and the defect of M.      *)

let RFA_EQON_HP = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> rfa_eqon U (rfa_hP G)
           (\y u. ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m)
                    (lnabla 2 G (lric2 G)) y u -
                  ltperm (swap(2,3)) (lnabla 2 G (lric2 G)) y u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_eqon; rfa_hP; ltperm] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 3 U (lnabla 2 (G:real^N->real^N^N) (lric2 G))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           LNABLA_TENSOR_FIELD) THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
  MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  RFA_HT_SLOTS_TAC 3);;

let RFA_LAP2_CONTR = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
     ltensor_field 4 U tf
     ==> rfa_eqon U
           (\y u. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                    matrix_inv(G y)$p$q *
                    tf y (\m. if m = 3 then basis p else if m = 4 then basis q else u m))))
           (ltcontr G (ltperm (\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                                   else if m = 4 then 2 else m) tf))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_eqon; ltcontr; ltperm] THEN REPEAT STRIP_TAC THEN
  RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN RFA_HT_SLOTS_TAC 4);;

let RFA_EQON_HM = prove
 (`!U (G:real^N->real^N^N) s t.
     metric_field U G
     ==> rfa_eqon U (rfa_hM s t G)
           (\y u. ltcontr G (ltperm (\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                                         else if m = 4 then 2 else m)
                                    (lnabla 3 G (lnabla 2 G (lric2 G)))) y u -
                  inv(&2) * lnabla 1 G (lnabla 0 G (rfa_sc G)) y u + rfa_hric G y u -
                  rfa_ric2sq G y u + inv(&2 * (t - s)) * lric2 G y u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 4 U (lnabla 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_SF_LRIC2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 2 (G:real^N->real^N^N) (lric2 G)`] RFA_SF_LNABLA) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[rfa_sf];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LAP2_CONTR)) THEN
  REWRITE_TAC[rfa_eqon; rfa_hM; ltlap; RFA_LNABLA_ITER_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

rfa_sf_unfolds := [RFA_HDDR_LAMBDA; RFA_HDR_LAMBDA] @ !rfa_sf_unfolds;;

let RFA_EQON_HHM = prove
 (`!U (G:real^N->real^N^N) s t.
     metric_field U G
     ==> rfa_eqon U (rfa_hhM s t G)
           (\y u. ltcontr G (ltperm (\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                                         else if m = 4 then 2 else m) (rfa_hddr G)) y u -
                  inv(&2) * (lnabla 1 G (lnabla 0 G (ltcontr G (rfa_hric G))) y u +
                             rfa_rmcomm 1 G (lnabla 0 G (rfa_sc G)) y u) +
                  rfa_hhric3 G y u - rfa_hric2sq G y u +
                  (--(inv(&2 * (t - s) pow 2)) * lric2 G y u +
                   inv(&2 * (t - s)) * rfa_hric G y u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 4 U (rfa_hddr (G:real^N->real^N^N))` ASSUME_TAC THENL
   [MP_TAC(RFA_SF_PROVE (ASSUME `metric_field U (G:real^N->real^N^N)`)
                        `rfa_hddr (G:real^N->real^N^N)`) THEN
    SIMP_TAC[rfa_sf];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LAP2_CONTR)) THEN
  REWRITE_TAC[rfa_eqon; rfa_hhM] THEN SIMP_TAC[]);;

(* From |- !y u. y IN U ==> X y u = E y u  to  |- rfa_eqon U X (\y u. E y u).   *)

let RFA_EQON_OF_PTWISE uu x th =
  (* th: |- y IN U ==> X y u = e   with y, u free variables *)
  let ant, eq = dest_imp(concl th) in
  let yv = lhand ant in
  let l = lhs eq in
  let uv = rand l in
  let lam = mk_abs(yv, mk_abs(uv, rhs eq)) in
  let gth = GEN yv (GEN uv th) in
  let dth = CONV_RULE (RAND_CONV (DEPTH_CONV BETA_CONV)) (ISPECL [uu; x; lam] rfa_eqon) in
  EQ_MP (SYM dth) gth;;

let RFA_H3_EQON mf tm =
  let fh, args = strip_comb tm in
  if not (is_const fh && fst(dest_const fh) = "rfa_h3") then failwith "RFA_H3_EQON" else
  let [g; tf] = args in
  let uu = rand(rator(concl mf)) in
  let thA = CONJUNCT1(REWRITE_RULE[rfa_sf] (RFA_SF_PROVE mf tf)) in
  let ty = hd(snd(dest_type(type_of g))) in
  let yv = mk_var("y", ty) and uv = mk_var("u", mk_type("fun", [`:num`; ty])) in
  let yin = mk_comb(mk_comb(mk_const("IN", [ty, aty]), yv), uu) in
  let th0 = MATCH_MP (ISPECL [uu; g; tf; yv; uv] RFA_H3_COMB) (CONJ thA (ASSUME yin)) in
  RFA_EQON_OF_PTWISE uu (list_mk_comb(fh, args)) (DISCH yin th0);;

rfa_eqon_hooks := RFA_H3_EQON :: !rfa_eqon_hooks;;

let RFA_HEAT_SF_AT = prove
 (`!k U a b (G:real->real^N->real^N^N) Tf Hf t.
     rfa_heat k U a b G Tf Hf /\ open U /\ a < t /\ t < b
     ==> rfa_sf k U (Tf t) /\ rfa_sf k U (Hf t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `Tf:real->real^N->(num->real^N)->real`;
                 `Hf:real->real^N->(num->real^N)->real`; `t:real`] RFA_HEAT_SLICE) THEN
  UNDISCH_TAC `rfa_heat k U a b (G:real->real^N->real^N^N) Tf Hf` THEN
  REWRITE_TAC[rfa_heat; rfa_sf] THEN ASM_SIMP_TAC[] THEN MESON_TAC[]);;


(* ========================================================================= *)
(* Relations between the frame atoms: symmetries, the metric,                *)
(* the contracted Bianchi identity and its derivative, the Ricci identity.   *)
(* ========================================================================= *)

let RFA_FT_EL = prove
 (`!(S:real^N^N) l m. rfa_ft S l m = transp S ** basis (EL (m - 1) l)`,
  REWRITE_TAC[rfa_ft]);;

let RFA_FT_RIC_SYM = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) i j.
     metric_field U G /\ y IN U
     ==> lric2 G y (rfa_ft S [i; j]) = lric2 G y (rfa_ft S [j; i])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lric2; RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL; HD; TL; num_CONV `1`] THEN
  MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RFA_FT_DRIC_SYM = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) i j k.
     metric_field U G /\ y IN U
     ==> lnabla 2 G (lric2 G) y (rfa_ft S [i; j; k]) =
         lnabla 2 G (lric2 G) y (rfa_ft S [j; i; k])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `rfa_ft (S:real^N^N) [i; j; k]`] LRG_N2_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[RFA_FT_EL; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_FT_DDRIC_SYM = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) i j k l.
     metric_field U G /\ y IN U
     ==> lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; j; k; l]) =
         lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [j; i; k; l])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `rfa_ft (S:real^N^N) [i; j; k; l]`] LRG_N3_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[RFA_FT_EL; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_FT_METRIC = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) i j.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> lmetric2 G y (rfa_ft S [i; j]) = if i = j then &1 else &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lmetric2; RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH] THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
  ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]);;

let RFA_CBIANCHI_EQON = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> rfa_eqon U (ltcontr G (ltperm (swap(2,3)) (lnabla 2 G (lric2 G))))
                    (\y u. inv(&2) * ltcontr G (lnabla 2 G (lric2 G)) y u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_eqon; ltcontr; ltperm] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `(u:num->real^N) 1`]
         LRG_CONTRACTED_BIANCHI) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:num->real^N`]
         LRG_DSCALAR_CONTRACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  RFA_SUM_EQ_TAC `a:num` THEN RFA_SUM_EQ_TAC `b:num` THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[swap] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* The Ricci identity for nabla^2 Ric in a frame.                            *)

let RFA_RIC_RIEM_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) a b c w.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> lricci G y (lriemann G y a b c) w =
         sum(1..dimindex(:N)) (\r. lrm4 G y (\m. if m = 1 then a else if m = 2 then b
                                                else if m = 3 then transp S ** basis r else c) *
                                  lricci G y (transp S ** basis r) w) /\
         lricci G y w (lriemann G y a b c) =
         sum(1..dimindex(:N)) (\r. lrm4 G y (\m. if m = 1 then a else if m = 2 then b
                                                else if m = 3 then transp S ** basis r else c) *
                                  lricci G y w (transp S ** basis r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `lriemann (G:real^N->real^N^N) y a b c`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV)
    [th]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x. lricci (G:real^N->real^N^N) y x w`; `1..dimindex(:N)`;
                   `\r. (transp (S:real^N^N) ** basis r) dot
                         ((G:real^N->real^N^N) y ** lriemann G y a b c)`;
                   `\r. transp (S:real^N^N) ** basis r`] RFA_LINEAR_SUM_EXPAND);
    MP_TAC(ISPECL [`\x. lricci (G:real^N->real^N^N) y w x`; `1..dimindex(:N)`;
                   `\r. (transp (S:real^N^N) ** basis r) dot
                         ((G:real^N->real^N^N) y ** lriemann G y a b c)`;
                   `\r. transp (S:real^N^N) ** basis r`] RFA_LINEAR_SUM_EXPAND)] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX]);;

let RFA_FT_RICCI_ID = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) i j k l.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; j; k; l]) -
         lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; j; l; k]) =
         sum(1..dimindex(:N)) (\r. lrm4 G y (rfa_ft S [k; l; r; i]) *
                                  lric2 G y (rfa_ft S [r; j])) +
         sum(1..dimindex(:N)) (\r. lrm4 G y (rfa_ft S [k; l; r; j]) *
                                  lric2 G y (rfa_ft S [i; r]))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`; `rfa_ft (S:real^N^N) [i; j; k; l]`] RFA_RICCI_IDENTITY) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD; RFA_LNABLA_ITER_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `lnabla 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G)) y
      (\m. if m = 3 then rfa_ft S [i; j; k; l] 4 else if m = 4 then rfa_ft S [i; j; k; l] 3
           else rfa_ft S [i; j; k; l] m) =
    lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; j; l; k])`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`]
         RFA_RIC_RIEM_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  BINOP_TAC THEN (RFA_SUM_EQ_TAC `r:num` THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH]));;

(* ========================================================================= *)
(* A memoizing polynomial normalizer for frame expressions.                  *)
(* RFA_MPOLY tm returns |- tm = p with p in the normal form of REAL_POLY_CONV *)
(* (the same variable order), expanding sum(1..3) and sum(1..dimindex(:3)),  *)
(* evaluating numeral conditionals, and rewriting atoms with the hook        *)
(* rfa_mp_hook (a function returning |- atom = expr, or failing for an atom  *)
(* in canonical form).  Results are cached on the term (deep hash keys).     *)
(* ========================================================================= *)

let RFA_SUM3D = prove
 (`!f. sum(1..dimindex(:3)) f = f 1 + f 2 + f 3`,
  REWRITE_TAC[DIMINDEX_3; SUM_3]);;

let rfa_mp_hook = ref (fun (tm:term) -> (failwith "rfa_mp_hook" : thm));;

let rfa_mp_cache = Hashtbl.create 100000;;

let RFA_MP_COND_CONV = NUM_REDUCE_CONV THENC REWRITE_CONV[COND_CLAUSES];;

let RFA_MPOLY =
  let add_tm = `(+):real->real->real` and sub_tm = `(-):real->real->real`
  and mul_tm = `( * ):real->real->real` and neg_tm = `(--):real->real`
  and pow_tm = `(pow):real->num->real` and inv_tm = `inv:real->real`
  and div_tm = `(/):real->real->real` in
  let sum_conv = (REWR_CONV RFA_SUM3D ORELSEC REWR_CONV SUM_3) THENC
                 BINOP_CONV (BINOP_CONV (TRY_CONV BETA_CONV) ORELSEC TRY_CONV BETA_CONV) in
  let rec mpoly tm =
    let key = (Hashtbl.hash_param 500 2000 tm, tm) in
    try Hashtbl.find rfa_mp_cache key with Not_found ->
    let th = mpoly_raw tm in
    (Hashtbl.add rfa_mp_cache key th; th)
  and mpoly_raw tm =
    if not(is_comb tm) || is_ratconst tm then REFL tm else
    let lop, r = dest_comb tm in
    if lop = neg_tm then
      let th1 = AP_TERM lop (mpoly r) in TRANS th1 (REAL_POLY_NEG_CONV (rand(concl th1)))
    else if lop = inv_tm then
      if is_comb r && is_comb(rator r) && rator(rator r) = mul_tm then
        let th1 = REWR_CONV REAL_INV_MUL tm in TRANS th1 (mpoly (rand(concl th1)))
      else if is_comb r && is_comb(rator r) && rator(rator r) = pow_tm then
        let th1 = REWR_CONV REAL_INV_POW tm in TRANS th1 (mpoly (rand(concl th1)))
      else
      let th1 = AP_TERM lop (mpoly r) in
      if is_ratconst (rand(rand(concl th1))) then TRANS th1 (REAL_RAT_INV_CONV (rand(concl th1)))
      else th1
    else if is_cond tm then
      let th1 = RFA_MP_COND_CONV tm in
      if is_cond (rand(concl th1)) then failwith "RFA_MPOLY: condition"
      else TRANS th1 (mpoly (rand(concl th1)))
    else if is_comb lop && (let op = rator lop in op = add_tm || op = sub_tm || op = mul_tm) then
      let op, l = dest_comb lop in
      let th1 = MK_COMB(AP_TERM op (mpoly l), mpoly r) in
      let fn = if op = add_tm then REAL_POLY_ADD_CONV
               else if op = mul_tm then REAL_POLY_MUL_CONV else REAL_POLY_SUB_CONV in
      TRANS th1 (fn (rand(concl th1)))
    else if is_comb lop && rator lop = pow_tm then
      let l = rand lop in
      let th1 = AP_THM (AP_TERM pow_tm (mpoly l)) r in
      TRANS th1 (REAL_POLY_POW_CONV (rand(concl th1)))
    else if is_comb lop && rator lop = div_tm then
      let th1 = REWR_CONV real_div tm in TRANS th1 (mpoly (rand(concl th1)))
    else if (is_comb lop && is_const(rator lop) && fst(dest_const(rator lop)) = "sum") then
      let th1 = sum_conv tm in TRANS th1 (mpoly (rand(concl th1)))
    else
      match (try Some(!rfa_mp_hook tm) with Failure _ -> None) with
        Some th1 -> TRANS th1 (mpoly (rand(concl th1)))
      | None -> REFL tm in
  mpoly;;

(* ========================================================================= *)
(* The pointwise identity for the heat defect of Hamilton's                  *)
(* Harnack quadratic in dimension 3 (CLN (10.62), in the form with           *)
(* nabla W = 0 at the point, nabla U given by (10.59), and the terms with    *)
(* the defects HU, HW of U, W kept): in a frame S orthonormal for G t at y,  *)
(*   defect of Z(U,W) = J(U,W) + sum_ab Q_ab^2 - (2/(t-s)) (M(W,W)+P(U,W))   *)
(*                      + 2 (M(HW,W) + P(HU,W) + P(U,HW) + R(HU,U)),         *)
(*   Q_ab = P_abc W_c + R_abcd U_cd   (lrm4 slots; rfa_hj of pc_rfa_u17iface). *)
(* Proof: the engine evaluates both sides at the frame (phase 1 the          *)
(* skeleton, phase 2 the coefficient tensors at symbolic indices), then      *)
(* RFA_MPOLY normalizes both sides to the same polynomial in the frame       *)
(* components of Ric, nabla Ric, nabla^2 Ric, U, W, HU, HW and inv(t - s),   *)
(* after the symmetries of these, the antisymmetry of U, the Ricci identity  *)
(* and the contracted Bianchi identity with its derivative (each solved for  *)
(* one pivot component) have been applied.                                   *)
(* ========================================================================= *)

let rfa_is_ft w = match (try Some(dest_comb(rator w), rand w) with Failure _ -> None) with
    Some((c, _), _) -> is_const c && fst(dest_const c) = "rfa_ft"
  | _ -> false;;

let rfa_coeff_of p d =
  let mul_tm = `( * ):real->real->real` in
  let ms = striplist (dest_binop `(+):real->real->real`) d in
  tryfind (fun m -> if m = p then `&1` else
                    let c, x = dest_binop mul_tm m in
                    if x = p && is_ratconst c then c else failwith "rfa_coeff_of") ms;;

(* From |- L = R, linear in the atom p with a rational coefficient after     *)
(* normalization, derive |- p = e with e free of p.                           *)

let RFA_SOLVE_PIVOT rel p =
  let sub_tm = `(-):real->real->real` and mul_tm = `( * ):real->real->real`
  and inv_tm = `inv:real->real` in
  let l = lhs(concl rel) and r = rhs(concl rel) in
  let th0 = EQ_MP (SYM (ISPECL [l; r] REAL_SUB_0)) rel in
  let thD = RFA_MPOLY (mk_binop sub_tm l r) in
  let thD0 = TRANS (SYM thD) th0 in
  let d = lhs(concl thD0) in
  let c = rfa_coeff_of p d in
  let ic = mk_comb(inv_tm, c) in
  let th_e = REAL_POLY_CONV (mk_binop sub_tm p (mk_binop mul_tm ic d)) in
  let th1 = AP_TERM (mk_comb(sub_tm, p)) (AP_TERM (mk_comb(mul_tm, ic)) thD0) in
  let th3 = CONV_RULE (LAND_CONV REAL_POLY_CONV) (TRANS (SYM th1) th_e) in
  if lhs(concl th3) <> p || free_in p (rhs(concl th3)) then failwith "RFA_SOLVE_PIVOT"
  else th3;;

let RFA_UDIAG = REAL_ARITH `!x:real. x = --x ==> x = &0`;;

let RFA_HDEF_DERIVE asm w =
  let hs = map ASSUME (conjuncts asm) in
  let h k = el k hs in
  let h_flow = h 0 and h_sa = h 1 and h_at = h 2 and h_tb = h 3 and h_y = h 4
  and h_invS = h 5 and h_frame = h 6 and h_sfU = h 7 and h_sfHU = h 8 and h_sfW = h 9
  and h_sfHW = h 10 and h_anti = h 11 and h_dW = h 12 and h_dU = h 13 in
  let b_flow = MATCH_MP LRG_FLOW_BASIC h_flow in
  let b_open = CONJUNCT1 b_flow in
  let mf = MP (SPEC `t:real` (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 b_flow))))))
              (CONJ h_at h_tb) in
  let sfat th = MATCH_MP RFA_HEAT_SF_AT (CONJ th (CONJ b_open (CONJ h_at h_tb))) in
  let s_HM = sfat (MATCH_MP RFA_HEAT_HM3 (CONJ h_flow h_sa)) in
  let s_HP = sfat (MATCH_MP RFA_HEAT_HP h_flow) in
  let s_RM = sfat (MATCH_MP RFA_HEAT_RM3 h_flow) in
  let s_bases = map BETA_RULE (CONJUNCTS s_HM @ CONJUNCTS s_HP @ CONJUNCTS s_RM) @
                [h_sfU; h_sfHU; h_sfW; h_sfHW] in
  let saved = (!rfa_sf_bases, !rfa_sf_unfolds, !rfa_lnf_unfolds, !rfa_frv_unfolds, !rfa_mp_hook) in
  Hashtbl.reset rfa_sf_cache; Hashtbl.reset rfa_lnf_cache;
  Hashtbl.reset rfa_atom_cache; Hashtbl.reset rfa_mp_cache;
  (* phase 1: the skeleton, with M, P, R and their defects as atoms *)
  rfa_sf_bases := s_bases @ [RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4; RFA_SF_SC; RFA_SF_HRIC];
  rfa_sf_unfolds := [RFA_HDDR_LAMBDA; RFA_HDR_LAMBDA; rfa_hprod; RFA_HRIC3_LAMBDA; rfa_ric2sq;
                     rfa_nric2; RFA_SC_CONTR; RFA_HHRIC3_LAMBDA; rfa_hsc; rfa_hnric2; rfa_hric2sq];
  rfa_lnf_unfolds := [];
  rfa_frv_unfolds := [rfa_hqform; rfa_hprod];
  let p1 = RFA_FRV_CONV mf h_y h_frame (lhs w) in
  let p1 = CONV_RULE (RAND_CONV (REWRITE_CONV[h_dW; h_dU; REAL_MUL_LZERO; REAL_MUL_RZERO;
             REAL_ADD_LID; REAL_ADD_RID; REAL_SUB_RZERO; SUM_0])) p1 in
  (* phase 2: the atoms at symbolic frame indices *)
  Hashtbl.reset rfa_lnf_cache;
  rfa_lnf_unfolds := [RFA_SC_CONTR; RFA_EQON_HRIC_3D; RFA_EQON_LRM4_3D; RFA_HRIC3_LAMBDA;
                      rfa_ric2sq; rfa_nric2; RFA_HDR_LAMBDA; RFA_EQON_HP];
  rfa_frv_unfolds := [RFA_EQON_HHM; RFA_EQON_HM; RFA_HDDR_LAMBDA; RFA_HHRIC3_LAMBDA; rfa_hsc;
                      rfa_hnric2; rfa_hric2sq; RFA_EQON_HP; RFA_HDR_LAMBDA; RFA_EQON_HRIC_3D;
                      RFA_EQON_LRM4_3D; RFA_HRIC3_LAMBDA; rfa_ric2sq; rfa_nric2; RFA_SC_CONTR];
  let evc tm = RFA_FRV_CONV mf h_y h_frame tm in
  let comps = map evc
   [`rfa_hhM s t ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2])`;
    `rfa_hM s t ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2])`;
    `rfa_hdr ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2; i3])`;
    `rfa_hP ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2; i3])`;
    `lnabla 3 ((G:real->real^3->real^3^3) t) (rfa_hP (G t)) y (rfa_ft (S:real^3^3) [i1; i2; i3; i4])`;
    `lrm4 ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2; i3; i4])`;
    `lnabla 4 ((G:real->real^3->real^3^3) t) (lrm4 (G t)) y (rfa_ft (S:real^3^3) [i1; i2; i3; i4; i5])`;
    `rfa_hric ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2])`] in
  let comp_list = map (fun th -> (rator(rator(lhs(concl th))), th)) comps in
  (* phase 3: the normalizer hook *)
  let ric_f = `lric2 ((G:real->real^3->real^3^3) t)`
  and dr_f = `lnabla 2 ((G:real->real^3->real^3^3) t) (lric2 (G t))`
  and ddr_f = `lnabla 3 ((G:real->real^3->real^3^3) t) (lnabla 2 (G t) (lric2 (G t)))`
  and met_f = `lmetric2 ((G:real->real^3->real^3^3) t)`
  and u_f = `Uf:real^3->(num->real^3)->real`
  and yv = `y:real^3` and uu = `U:real^3->bool` and gt = `(G:real->real^3->real^3^3) t`
  and sv = `S:real^3^3`
  and ivars = [`i1:num`; `i2:num`; `i3:num`; `i4:num`; `i5:num`] in
  let nm = mk_small_numeral in
  let h_mfy = CONJ mf h_y and h_all = end_itlist CONJ [mf; h_y; h_invS; h_frame] in
  let met_th i j =
    MP (REWRITE_RULE[DIMINDEX_3; ARITH] (ISPECL [uu; gt; yv; sv; nm i; nm j] RFA_FT_METRIC)) h_all in
  let dest_fatom tm = match (try Some(dest_comb(rator tm), rand tm) with Failure _ -> None) with
      Some((f, yy), wt) when yy = yv && rfa_is_ft wt ->
        (f, map dest_small_numeral (dest_list (rand wt)))
    | _ -> failwith "dest_fatom" in
  let pivots_on = ref false and pivot_tbl = ref [] in
  let pivot tm = if !pivots_on then assoc tm !pivot_tbl else failwith "canonical" in
  let anti_th i j = ISPECL [nm i; nm j] h_anti in
  let hook_raw tm =
    let f, l = dest_fatom tm in
    if f = met_f then (match l with [i;j] -> met_th i j | _ -> failwith "met")
    else if f = ric_f then
      (match l with
         [i;j] when i > j -> MP (ISPECL [uu; gt; yv; sv; nm i; nm j] RFA_FT_RIC_SYM) h_mfy
       | _ -> failwith "canonical")
    else if f = dr_f then
      (match l with
         [i;j;k] when i > j -> MP (ISPECL [uu; gt; yv; sv; nm i; nm j; nm k] RFA_FT_DRIC_SYM) h_mfy
       | _ -> pivot tm)
    else if f = ddr_f then
      (match l with
         [i;j;k;l4] when i > j ->
           MP (ISPECL [uu; gt; yv; sv; nm i; nm j; nm k; nm l4] RFA_FT_DDRIC_SYM) h_mfy
       | [i;j;k;l4] when k > l4 ->
           CONV_RULE (REWR_CONV REAL_EQ_SUB_RADD)
             (MP (ISPECL [uu; gt; yv; sv; nm i; nm j; nm k; nm l4] RFA_FT_RICCI_ID) h_all)
       | _ -> pivot tm)
    else if f = u_f then
      (match l with
         [i;j] when i > j -> anti_th i j
       | [i;j] when i = j -> MP (ISPEC tm RFA_UDIAG) (anti_th i j)
       | _ -> failwith "canonical")
    else
      let th = assoc f comp_list in
      INST (map2 (fun n v -> (nm n, v)) l (fst(chop_list (length l) ivars))) th in
  rfa_mp_hook := (fun tm -> try hook_raw tm with Failure s -> failwith s
                                               | Not_found -> failwith "rfa_mp_hook"
                                               | Match_failure _ -> failwith "rfa_mp_hook");
  Hashtbl.reset rfa_mp_cache;
  (* the contracted Bianchi identity at [j] and its derivative at [j; l] *)
  let mk_ft l = list_mk_comb(`rfa_ft:real^3^3->num list->num->real^3`,
                             [sv; mk_list(map nm l, `:num`)]) in
  let mk_at f l = mk_comb(mk_comb(f, yv), mk_ft l) in
  let bth = MATCH_MP RFA_CBIANCHI_EQON mf in
  let openU = CONJUNCT1(REWRITE_RULE[metric_field] mf) in
  let bth1 = MATCH_MP (ISPECL [`1`; uu; gt] RFA_EQON_LNABLA) (CONJ openU bth) in
  let app_rel eqth l =
    let a = rand(rator(concl eqth)) and b = rand(concl eqth) in
    let th = MP (ISPECL [uu; a; b; yv; mk_ft l] RFA_EQON_APP) (CONJ eqth h_y) in
    let th1 = CONV_RULE (RAND_CONV (TRY_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV))) th in
    CONV_RULE (BINOP_CONV (RFA_FRV_CONV mf h_y h_frame)) th1 in
  let piv_ddr (j,l) =
    if j = l then mk_at ddr_f [j;j;j;j] else
    let c = 6 - j - l in mk_at ddr_f [min c j; max c j; min c l; max c l] in
  let pv1 = map (fun j -> let p = mk_at dr_f [j;j;j] in
                          (p, RFA_SOLVE_PIVOT (app_rel bth [j]) p)) (1--3) in
  let pv2 = map (fun (j,l) -> let p = piv_ddr (j,l) in
                              (p, RFA_SOLVE_PIVOT (app_rel bth1 [j;l]) p))
                (allpairs (fun j l -> (j,l)) (1--3) (1--3)) in
  pivot_tbl := pv1 @ pv2; pivots_on := true;
  Hashtbl.reset rfa_mp_cache;
  (* phase 4: normal forms of both sides *)
  let nfL = RFA_MPOLY (rand(concl p1)) in
  let rhs_unf = (REWRITE_CONV[rfa_hj] THENC DEPTH_CONV BETA_CONV) (rhs w) in
  let nfR = RFA_MPOLY (rand(concl rhs_unf)) in
  let (b1, b2, b3, b4, b5) = saved in
  rfa_sf_bases := b1; rfa_sf_unfolds := b2; rfa_lnf_unfolds := b3; rfa_frv_unfolds := b4;
  rfa_mp_hook := b5;
  Hashtbl.reset rfa_sf_cache; Hashtbl.reset rfa_lnf_cache;
  Hashtbl.reset rfa_atom_cache; Hashtbl.reset rfa_mp_cache;
  if not (aconv (rand(concl nfL)) (rand(concl nfR))) then failwith "RFA_HDEF_DERIVE: normal forms"
  else itlist PROVE_HYP (CONJUNCTS (ASSUME asm))
         (TRANS p1 (TRANS nfL (SYM (TRANS rhs_unf nfR))));;

(* The main identity RFA_HARNACK_DEFECT_3D (CLN (10.62)).                     *)

let RFA_HARNACK_DEFECT_3D = prove
 (`!U a b (G:real->real^3->real^3^3) s t y (S:real^3^3) Uf HUf Wf HWf (u:num->real^3).
     lricci_flow U a b G /\ s <= a /\ a < t /\ t < b /\ y IN U /\
     invertible S /\ matrix_inv(G t y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 2 U HUf /\ rfa_sf 1 U Wf /\ rfa_sf 1 U HWf /\
     (!i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i]))) /\
     (!w. lnabla 1 (G t) Wf y w = &0) /\
     (!i j e. lnabla 2 (G t) Uf y (rfa_ft S [i; j; e]) =
              inv(&2) * (lric2 (G t) y (rfa_ft S [e; i]) * Wf y (rfa_ft S [j]) -
                         lric2 (G t) y (rfa_ft S [e; j]) * Wf y (rfa_ft S [i])) +
              inv(&4 * (t - s)) * ((if e = i then &1 else &0) * Wf y (rfa_ft S [j]) -
                                   (if e = j then &1 else &0) * Wf y (rfa_ft S [i])))
     ==> rfa_hqform (G t) (rfa_hM s t (G t)) (rfa_hhM s t (G t)) (rfa_hP (G t))
           (\y u. rfa_hdr (G t) y (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) -
                  rfa_hdr (G t) y (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2))
           (lrm4 (G t)) (rfa_h3 (G t) (rfa_hric (G t))) Uf HUf Wf HWf y u =
         rfa_hj 3 (\a b c d. lrm4 (G t) y (rfa_ft S [a; b; d; c]))
                  (\a b c. rfa_hP (G t) y (rfa_ft S [a; b; c]))
                  (\a b. rfa_hM s t (G t) y (rfa_ft S [a; b]))
                  (\a b. Uf y (rfa_ft S [a; b])) (\a. Wf y (rfa_ft S [a])) +
         sum(1..3) (\a. sum(1..3) (\b.
           (sum(1..3) (\c. rfa_hP (G t) y (rfa_ft S [a; b; c]) * Wf y (rfa_ft S [c])) +
            sum(1..3) (\c. sum(1..3) (\d. lrm4 (G t) y (rfa_ft S [a; b; c; d]) *
                                         Uf y (rfa_ft S [c; d])))) pow 2)) -
         &2 / (t - s) *
         (sum(1..3) (\a. sum(1..3) (\b. rfa_hM s t (G t) y (rfa_ft S [a; b]) *
                                      Wf y (rfa_ft S [a]) * Wf y (rfa_ft S [b]))) +
          sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. rfa_hP (G t) y (rfa_ft S [a; b; c]) *
                                      Uf y (rfa_ft S [a; b]) * Wf y (rfa_ft S [c]))))) +
         &2 * (sum(1..3) (\a. sum(1..3) (\b. rfa_hM s t (G t) y (rfa_ft S [a; b]) *
                                            HWf y (rfa_ft S [a]) * Wf y (rfa_ft S [b]))) +
               sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. rfa_hP (G t) y (rfa_ft S [a; b; c]) *
                    (HUf y (rfa_ft S [a; b]) * Wf y (rfa_ft S [c]) +
                     Uf y (rfa_ft S [a; b]) * HWf y (rfa_ft S [c]))))) +
               sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                    lrm4 (G t) y (rfa_ft S [a; b; c; d]) * HUf y (rfa_ft S [a; b]) *
                    Uf y (rfa_ft S [c; d]))))))`,
  REPEAT GEN_TAC THEN
  W(fun (_, w) -> let a, c = dest_imp w in ACCEPT_TAC (DISCH a (RFA_HDEF_DERIVE a c))));;

