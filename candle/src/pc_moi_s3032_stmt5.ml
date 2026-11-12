(* ========================================================================= *)
(* pc_moi_s3032_stmt5: the Secs 30-32 full glue with the restated            *)
(* statements.  The full glue theorems of pc_moi_s3032_stmt.ml (section 6,   *)
(* moi_std_glue) take the dependency closure of their cores over the         *)
(* original statements.  Five of those are restated (stmt2: DISK_CHART_2,    *)
(* NULL_POLYGON_2 with the foundation term BALL_2 in place of the n <= 3     *)
(* BALL; stmt3: LEVEL_2, ITERATE_2; stmt4: HANDLES_2), and the original      *)
(* DISK_CHART and NULL_POLYGON would carry the n <= 3 term moi_n3            *)
(* MOI_FND_DERIVED_NBHD_BALL, which is not proved, into the closures of      *)
(* 30.3, 32.4 and 31.4 (the bridge MOI_FS4_BALL_2 of pc_moi_fnd_stmt4.ml     *)
(* goes BALL ==> BALL_2 only).  Here the closure prefers the restated        *)
(* statements: a needed consequent is first looked up among DISK_CHART_2,    *)
(* NULL_POLYGON_2, LEVEL_2, ITERATE_2, HANDLES_2 (same consequents as the    *)
(* original statements, except LEVEL_2 and HANDLES_2, whose consequents are  *)
(* those used by ITERATE_2 and by the 32.3 core of stmt4).  The affected     *)
(* glue items are re-proved with the same cores and tactic:                  *)
(*   MOI_S3S5_303, MOI_S3S5_324, MOI_S3S5_314, MOI_S3S5_322;                 *)
(*   moi_s3s5_glue: the nine items with these, MOI_S3S4_323 (stmt4) and the  *)
(*     unaffected MOI_STD_304, 306, 307, 311;                                *)
(*   moi_s3s5_check: every glue has no hypotheses, concludes its item, and   *)
(*     uses none of the five original statements nor the n <= 3 BALL; each   *)
(*     new hypothesis is an original one or one of the restated terms and    *)
(*     their antecedents (no new input term).                                *)
(* For 32.2 the main theorem uses MOI_S3S6_322 of pc_moi_s3032_stmt6.ml      *)
(* instead of MOI_S3S5_322.                                                  *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt2.ml";;
needs "src/pc_moi_s3032_stmt3.ml";;
needs "src/pc_moi_s3032_stmt4.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_s3s5_new_targets =
  [MOI_S30_DISK_CHART_2; MOI_S31_NULL_POLYGON_2; MOI_S32_LEVEL_2; MOI_S32_ITERATE_2;
   MOI_S32_HANDLES_2];;

let moi_s3s5_old_targets =
  [MOI_S30_DISK_CHART; MOI_S31_NULL_POLYGON; MOI_S32_LEVEL; MOI_S32_ITERATE;
   MOI_S32_HANDLES];;

let moi_s3s5_find_target a =
  let cands = moi_s3s5_new_targets @ map moi_n3 moi_s3s5_new_targets in
  try Some(find (fun t -> aconv (moi_std_csq t) a) cands)
  with Failure _ -> moi_std_find_target a;;

let rec moi_s3s5_closure stop acc tms =
  match tms with
    [] -> acc
  | a::rest ->
      if exists (aconv a) stop || exists (aconv a) acc
      then moi_s3s5_closure stop acc rest else
      match moi_s3s5_find_target a with
        Some t ->
          if exists (aconv t) acc then moi_s3s5_closure stop acc rest else
          let ants = if is_imp t then conjuncts(fst(dest_imp t)) else [] in
          moi_s3s5_closure stop (t::acc) (ants @ rest)
      | None -> moi_s3s5_closure stop (a::acc) rest;;

let moi_s3s5_full_stmt hyps prod =
  let stop = if is_imp prod then conjuncts(fst(dest_imp prod)) else [] in
  mk_imp(list_mk_conj(rev(moi_s3s5_closure stop [] hyps)), prod);;

let moi_s3s5_full core prod =
  moi_s3s5_full_stmt (conjuncts(fst(dest_imp(concl core)))) prod;;

let MOI_S3S5_303 = prove
 (moi_s3s5_full_stmt [`MOISE_303_STATEMENT`] `MOISE_303_STATEMENT`,
  REPEAT STRIP_TAC THEN MOI_STD_DISCHARGE_TAC);;

let MOI_S3S5_324 = prove
 (moi_s3s5_full MOI_STD_324_CORE `MOISE_324_STATEMENT`,
  MOI_STD_FULL_TAC MOI_STD_324_CORE);;

let MOI_S3S5_314 = prove
 (moi_s3s5_full MOI_STD_314_CORE MOI_PROD_314,
  MOI_STD_FULL_TAC MOI_STD_314_CORE);;

let MOI_S3S5_322 = prove
 (moi_s3s5_full MOI_STD_322_CORE MOI_PROD_322_CELLS,
  MOI_STD_FULL_TAC MOI_STD_322_CORE);;

let moi_s3s5_glue =
  ["MOISE_303_STATEMENT",MOI_S3S5_303,`MOISE_303_STATEMENT`;
   "MOISE_324_STATEMENT",MOI_S3S5_324,`MOISE_324_STATEMENT`;
   "MOI_PROD_304",MOI_STD_304,MOI_PROD_304;
   "MOI_PROD_306",MOI_STD_306,MOI_PROD_306;
   "MOI_PROD_307",MOI_STD_307,MOI_PROD_307;
   "MOI_PROD_311",MOI_STD_311,MOI_PROD_311;
   "MOI_PROD_314",MOI_S3S5_314,MOI_PROD_314;
   "MOI_PROD_322_CELLS",MOI_S3S5_322,MOI_PROD_322_CELLS;
   "MOI_PROD_323",MOI_S3S4_323,MOI_PROD_323];;

(* The mechanical check.  forbidden: the five original statements (and their *)
(* N = 3 instances) and the n <= 3 BALL.  allowed_new: the restated terms    *)
(* and their antecedents.                                                    *)

let moi_s3s5_forbidden =
  moi_s3s5_old_targets @ map moi_n3 moi_s3s5_old_targets @
  [MOI_FND_DERIVED_NBHD_BALL; moi_n3 MOI_FND_DERIVED_NBHD_BALL];;

let moi_s3s5_allowed_new =
  let ts = moi_s3s5_new_targets @ map moi_n3 moi_s3s5_new_targets in
  ts @ itlist (fun t acc -> (if is_imp t then conjuncts(fst(dest_imp t)) else []) @ acc) ts [];;

let moi_s3s5_item_ok (n,th,item) =
  let hs = conjuncts(lhand(concl th)) in
  let old_hs = conjuncts(lhand(concl(
      let (_,oth,_) = find (fun (m,_,_) -> m = n) moi_std_glue in oth))) in
  hyp th = [] && aconv (rand(concl th)) item &&
  not (exists (fun h -> exists (aconv h) moi_s3s5_forbidden) hs) &&
  forall (fun h -> exists (aconv h) old_hs || exists (aconv h) moi_s3s5_allowed_new) hs;;

let moi_s3s5_check = forall moi_s3s5_item_ok moi_s3s5_glue;;

print_string ("S3S5 " ^
   string_of_bool (moi_s3s5_check) ^
   " " ^
   ((String.concat " " (map (fun (n,th,_) -> n ^ ":" ^ string_of_int (length(conjuncts(lhand(concl th))))) moi_s3s5_glue))) ^
   "\n");;

