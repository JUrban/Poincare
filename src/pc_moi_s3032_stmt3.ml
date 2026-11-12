(* ========================================================================= *)
(* pc_moi_s3032_stmt3: the s32 Step 1 statements restated with a members     *)
(* clause.  MOI_S32_LEVEL (pc_moi_s3032_stmt.ml) constrains only the set of  *)
(* the new state outside the interior R of the 2i-th even torus, not its     *)
(* members, so MOI_S32_ITERATE has no stable members to form the limit       *)
(* family.  MOI_S32_LEVEL_2 adds: the members of the state that miss R are   *)
(* unchanged.  Sanity: the 30.3 surgery of Step 1 at level i cuts and caps   *)
(* only inside Int S'_(2i), a subset of R, so a member that misses R is not  *)
(* touched and every new piece contains a cap inside R.                      *)
(*   MOI_S32_LEVEL_2, MOI_S32_ITERATE_2 (antecedent: the consequent of      *)
(*   LEVEL_2; the body of ITERATE unchanged);                               *)
(*   MOI_S3S3_LEVEL_BRIDGE : |- MOI_S32_LEVEL_2 ==> MOI_S32_LEVEL.          *)
(* With LEVEL_2, LIMIT and ITERATE_2 the body of ITERATE is a theorem, so    *)
(* MOI_S32_ITERATE follows and the glue MOI_STD_322 applies unchanged.  The  *)
(* main theorem uses instead the forms with a member invariant of            *)
(* pc_moi_s3032_stmt6.ml.                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_S32_LEVEL_2 =
  mk_imp(list_mk_conj [`MOISE_303_STATEMENT`; `MOISE_268_STATEMENT`;
                       moi_n3 MOI_FND_BICOLLAR_CURVE_2;
                       moi_std_csq (moi_n3 MOI_S30_SURFACE_TRIANG)],
 `!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ ~(i IN lev)
     ==> ?fam'. moi_s32_state g dd s2 (i INSERT lev) fam' /\
                moi_s32_set g s2 fam' DIFF interior (IMAGE g (revolution (dd (&2 * i)))) =
                moi_s32_set g s2 fam DIFF interior (IMAGE g (revolution (dd (&2 * i)))) /\
                {c | c IN fam' /\
                     DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
                {c | c IN fam /\
                     DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`);;

let MOI_S32_ITERATE_2 =
  mk_imp(list_mk_conj [moi_std_csq MOI_S32_LEVEL_2; moi_n3 MOI_S32_LIMIT],
         moi_std_csq MOI_S32_ITERATE);;

let MOI_S3S3_LEVEL_BRIDGE = prove
 (mk_imp(MOI_S32_LEVEL_2,MOI_S32_LEVEL),
  DISCH_THEN(fun th -> DISCH_THEN(fun a -> MP_TAC(MP th a))) THEN
  MESON_TAC[]);;

Printf.printf "S3S3 %b\n%!"
  (aconv (concl MOI_S3S3_LEVEL_BRIDGE) (mk_imp(MOI_S32_LEVEL_2,MOI_S32_LEVEL)) &&
   hyp MOI_S3S3_LEVEL_BRIDGE = [] &&
   frees MOI_S32_LEVEL_2 = [] && frees MOI_S32_ITERATE_2 = []);;

