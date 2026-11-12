# Notes on the sources

This file records what the HOL Light formalization found in its sources:

- Morgan-Tian (MT): J. Morgan and G. Tian, Ricci Flow and the Poincare Conjecture, Clay Mathematics Monographs 3 (AMS and Clay Mathematics Institute, 2007), the blueprint of the smooth proof;
- Moise: E. E. Moise, Geometric Topology in Dimensions 2 and 3, Graduate Texts in Mathematics 47 (Springer, 1977), the source of the topological form (every compact 3-manifold has a smooth structure);
- other sources in which the formalization found something (Section 7): J. Morgan and G. Tian's correction of their Section 19.2 (arXiv:1512.00699) and A. Bahri's note on it (arXiv:1512.02098); T. Colding and W. Minicozzi, Width and finite extinction time of Ricci flow (Geom. Topol. 12, 2008); B. Chow, P. Lu and L. Ni, Hamilton's Ricci Flow (AMS, 2006); B. Kleiner and J. Lott, Notes on Perelman's papers; B. Kotschwar's energy approach to uniqueness of the Ricci flow; J. Sacks and K. Uhlenbeck's existence of minimal 2-spheres; and T. Tao's lecture notes on Perelman's proof in Poincare's Legacies, Part II.

Conventions:

- MT locations give the chapter, section, result or equation number, and the printed page; in the PDF used, the printed page is the PDF page minus 43 in the body of the book. Every MT location was checked on the PDF page.
- Moise locations give the section, result and printed page of the 1977 edition; in the scanned copy used, the printed page is the PDF page minus 9.
- HOL locations are theorem or definition names and files src/<name>.ml of this repository. "Not used" or "not formalized" means that the result is not part of the formalization because its route does not need it (see below); such items come from reading the source against the formal statements, not from a formal proof.
- Lean locations are file:line in the two Lean 4 proofs of the Poincare conjecture, read at fixed commits (the Lean code was not rebuilt for this comparison):
  - FrenzyMath: frenzymath/PoincareConjecture at commit 62db01af, and its blueprint repository frenzymath/Poincare-Conjecture at commit 432c38f2 (paths from the repository roots);
  - Qin et al.: qinz1yang/differential-geometry at commit 7a48598d (release v0.1.3).

  A Lean part appears only where a Lean repository records or states the same correction. FrenzyMath's own list of corrections is not public, so their file documentation and blueprint are cited instead; the Qin et al. code has no comments, so only its statements can be compared.
- Each note has an ID (MT1, MT2, ... for Morgan-Tian; MO1, MO2, ... for Moise; S1, S2, ... for other sources) and one of these kinds:
  - error: a numbered result, definition or equation is false as written; "error (misprint)" when one symbol or word is wrong and the intended statement is evident;
  - gap: a fact used later but not stated, or a step asserted without argument or resting on a citation that does not apply, while the result itself is true;
  - imprecision: an inexact wording, condition or quantifier that does no harm;
  - typo;
  - cross-reference error: a wrong label or citation;
  - unclear: a correction recorded elsewhere that could be neither confirmed nor refuted.

  An entry of Sections 4-7 may group a few slips of one passage; its kind is the dominant one.
- The route of the formalization, which decides what "not used" means: MT's simply connected route (Cor 0.2(a) from Thm 15.9, Prop 15.3, Cor 15.4 and Thm 18.1), with these deviations:
  - a Ricci flow with surgery is a finite history of smooth flows on fixed manifolds joined by cut-and-cap events (src/pc_rfs_history.ml), not a space-time with charts;
  - uniqueness of Ricci flow (Thm 3.11) is proved by Kotschwar's energy method (PDE_UNIQUENESS, src/pc_rf_unique.ml), and uniqueness of the standard solution (Thm 12.5(1)) by the same method for complete flows of bounded curvature (RFU_A14, src/pc_rf_unique_a14u.ml), not by the harmonic map heat flow of Secs 12.6-12.8;
  - Thm 9.59 and Lemma 9.65 follow Tao's notes (Props 3.18.3 and 3.18.7, pp. 587 and 589), and noncollapsing through surgery follows Kleiner-Lott (Def 69.1, Lemma 79.12), without the positive-curvature exemption;
  - the Appendix is formalized in its separating form, completed by the smooth Schoenflies theorem in R^3 (src/pc_sch_*.ml, following Hatcher's proof of Alexander's theorem);
  - finite extinction uses the width of Colding-Minicozzi inside the frame of Sec 18.3.2 (src/pc_p4_*.ml, src/pc_cm*.ml), so Ch 19, Sec 18.2 and Prop 18.24 are not formalized;
  - the endgame is an induction over the history, with Smale's theorem on the diffeomorphisms of S^2 (src/pc_smt_*.ml);
  - the topological form adds Moise's theorem (src/pc_moi_*.ml).

## Summary

- The notes are 343 items:

  | kind | Morgan-Tian | Moise | other sources | total |
  |---|---|---|---|---|
  | error | 44 (18 misprints) | 5 (4 misprints) | 1 | 50 |
  | gap | 128 | 42 | 4 | 174 |
  | imprecision | 17 | 15 | 3 | 35 |
  | typo | 58 | 7 | 1 | 66 |
  | cross-reference error | 8 | 8 | 1 | 17 |
  | unclear | 1 | 0 | 0 | 1 |
  | total | 256 | 77 | 10 | 343 |

- Every Morgan-Tian item was checked on the PDF page; 26 further candidate items, from surveys of the book and from the corrections recorded by FrenzyMath, turned out not to be errors and are not listed. One item is unclear (MT129).
- Where the formalization uses a result, it states and proves a corrected form or takes another route; none of the items affects the truth of the main theorems. 20 of the 44 Morgan-Tian errors and 36 of its 128 gaps concern results that the formalization does not use (Sections 3 and 5, and the notes marked "not used" or "not formalized").
- The items with the most effect on the formal development:
  - The uniqueness of the standard solution (Thm 12.5(1)), which Ch 16 uses, rests on a false decay estimate (MT24; also MT22, MT23, MT97, MT140, MT141, MT143). The formalization proves uniqueness instead for complete flows of bounded curvature with Kotschwar's energy method.
  - Finite extinction: the book's Lemma 19.7 misses a term linear in the curvature (MT228), which invalidates (19.5), Claim 19.8, Lemma 19.9 and Cor 19.10 as printed (MT229-MT230); the authors' 2015 correction is right (S9), and a note disputing it is wrong (S10). The formalization uses the width of Colding-Minicozzi instead of Ch 19, and fills a gap in their Lemma 3.11 on S^2 (S3).
  - Noncollapsing through surgery: the proof of Prop 17.1 needs noncollapsing without the positive-curvature exemption that Prop 16.1 keeps (MT117), and the proof of Prop 16.1 treats only one scale at each point (MT112). The formalization follows Kleiner-Lott here.
  - Part 3 of the book (Chs 13-17) has further steps that fail or are missing as written: the choice of theta1 in Claim 17.3 (MT31), the persistence of larger balls in Prop 16.5 (MT113), the strong neck inside the surgery neck in Lemma 17.7 (MT119), the sequence for T' in Prop 17.1 (MT120), Claim 17.6 (MT118) and the positivity of the surgery cap in Ch 13 (MT102).
  - The topology of the Appendix and of Prop 15.3: Prop A.19 says "do not separate" for "separate" (MT36), Prop A.11(5) is false in general (MT35), the end of A.21 Case I needs Alexander's theorem (MT127), and the proof of Prop 15.3 misses a tight-shell case (MT105). The formalization proves the Appendix in its separating form, with the smooth Schoenflies theorem in R^3.
  - Analysis in Chs 3-11: the time endpoints of the compactness theorems (MT8), the curvature hypothesis of Prop 3.33 (MT5, MT47), maximum principles for time-dependent metrics (MT48), the smoothness of the limit reduced length (MT63), the Harnack inequality under bounds on each slice (MT90), zero eigenvalues of Rm versus Ric (MT49, MT88, MT89), and the derivative bounds at canonical neighbourhoods (MT87).
  - Conventions: the normalization of the curvature operator and of |Rm| is never fixed (MT38, MT39); the formalization uses the sectional normalization throughout.
  - Moise: one theorem is false as stated, 26.7, which needs compactness and a nonempty common boundary (MO23), and four statements or definitions have misprints (MO25, MO29, MO53, MO60). Most notes concern proofs in Secs 17 and 25-35 that are sketched or left to the reader, which the formalization completes; some formal statements are stronger or more uniform than the book's because later proofs need it (32.4 with the disk in the ball, MO46; 33.1 in tube form, MO48; Sec 34 in locally finite form, MO65).
  - Other sources: a gap in Colding-Minicozzi's Lemma 3.11 on S^2 (above), the same smoothness gap as in Prop 9.20 in Kleiner-Lott (S5), an imprecision in Colding-Minicozzi's proof of Thm 1.7 (S4), and slips in Chow-Lu-Ni, Kotschwar, Sacks-Uhlenbeck and Tao's notes (S1, S2, S6, S7, S8).
- Lean: where FrenzyMath or Qin et al. record a correction of the same passage, the note says so. Some corrections recorded by FrenzyMath concern passages found correct here: their sign correction of Prop 4.1 (the printed bound is the exact solution of the comparison ODE), the scaling of |Rm|, the set-up of Thm 9.11 (only slips, MT186), the statements (not the proofs) of Thm 7.13 and Lemma 7.15 - Cor 7.24, and the "first empty time" of Thm 18.1.

## 1. Morgan-Tian: errors

A numbered result, definition or equation of Morgan-Tian that is false as written. Errors in Chapter 19 are in Section 5.

### MT1. Lemma 1.32: no completeness hypothesis
- Location: Ch 1, Sec 5, Lemma 1.32, p. 19 (restated with compact closure on p. 50). Kind: error.
- Issue: If |Rm| <= K on B(p, pi/sqrt K), exp_p is said to be a local diffeomorphism from B(0, pi/sqrt K). Without completeness or compact closure of the ball, exp_p need not even be defined on that tangent ball (the flat open unit ball with K = 1). The restated version on p. 50 ("B(p,r) has compact closure") is correct and is the one used (proof of Thm 3.29).
- HOL: CMP_CONJUGATE_RADIUS (src/pc_cmp_conj.ml) assumes that the tangent ball lies in the domain of exp_x and only sec <= K, and concludes that d(exp_x) is injective there; compact closure of the metric ball supplies the domain hypothesis (CMPQ_COMPACT_DOM, src/pc_cmp_seg.ml).

### MT2. Prop 2.19: connectedness is missing
- Location: Ch 2, Sec 6, Prop 2.19, p. 31. Kind: error.
- Issue: "Let (M,g) be a complete, positively curved Riemannian 3-manifold. Then (M,g) does not contain eps-necks of arbitrarily small scale" omits connectedness, which the book's notion of manifold (p. 3) does not include: a disjoint union of shrinking copies of one elongated positively curved ellipsoid is complete and positively curved and has eps-necks with R -> infinity. The proof (a soul and connected level sets) assumes M connected.
- HOL: P2_PROP_2_19_STATEMENT and its route form P2_PROP_2_19_SEP_STATEMENT (src/pc_p3_iface.ml) assume connected_space; the route form (sec >= 0 and separating neck spheres) is P2AS_PROP_2_19_SEP (src/pc_p2a_219.ml).
- Lean: FrenzyMath states Prop 2.19 with ConnectedSpace (PoincareLib/Geometry/RicciFlow/Surgery/Control/SmallNecks.lean:26, M45SmallNeckScaleBound), without recording it as a correction.

### MT3. Prop 2.23: only for space-times
- Location: Ch 2, Sec 7, Prop 2.23, pp. 33-34. Kind: error.
- Issue: The forward-difference bound for F_max is stated for any smooth manifold with a vector field chi and a function t with chi(t) = 1, and fails in that generality: on M = (R x [0,1]) minus the open disc of radius 1/4 about (0,1/2), with chi = d/dt, F = -x^2 and psi = 0, F_max increases on (1/2, 3/4). It is true for space-times (products, as in Def 3.34), which is how it is used.
- HOL: the scalar maximum principles (RFA_MAXP_BARRIER and RFA_MINP_BARRIER, src/pc_rfa_maxp.ml) are stated on products U x [a,b) with U compact and open, a time-dependent metric and psi locally Lipschitz in its second argument.

### MT4. (3.6): an index order in the evolution of Ric
- Location: Ch 3, Sec 4, Thm 3.13, (3.6), p. 41. Kind: error (misprint).
- Issue: With the book's convention R(X,Y,Z,W) = g(R(X,Y)W,Z), the curvature factor in (3.6) must be R_pjrk, not R_pjkr. As printed, the right side on a round sphere of curvature lambda is -4(n-1)^2 lambda^2 g although Ric is constant in t, and the trace gives dR/dt = Delta R - 2|Ric|^2, contradicting (3.7). (3.5) is right.
- HOL: the Ricci evolution with the corrected index order is RFA_LRICCI_EVOLUTION, with the 3-dimensional form RFA_LRICCI_EVOLUTION_3D (src/pc_rfa_pevol.ml).
- Lean: FrenzyMath records the same correction (PoincareLib/Geometry/RicciFlow/Curvature/Reaction.lean:47, ricciReaction).

### MT5. Prop 3.33: a curvature bound at time 0 only
- Location: Ch 3, Sec 7, Prop 3.33, p. 53. Kind: error.
- Issue: The hypothesis bounds |Rm| only at time 0, on B(p,0,r), but conclusions (3) |Delta_{g(t)} eta| <= C2 and (4) |grad eta|^2_{g(t)}/eta <= C2'(alpha,n)/r^2 are asserted for all t in [0,T], T <= alpha/K. False: for a shrinking round S^3 with r its initial radius and T near the extinction time, g(T) = c g(0) with c -> 0, so (4) fails for every admissible eta. The hypothesis must be |Rm| <= K on B(p,0,r) x [0,T]. The only use, the proof of Thm 3.29, assumes that, so Thm 3.29 survives.
- HOL: the cutoff of the local Shi estimates is a radial bump in exponential coordinates, whose gradient and Laplacian at later times are bounded from curvature bounds on the whole space-time region (RFA_CUT_GRAD, RFA_CUT_LAP and RFA_GAMMA_CHANGE, src/pc_rfa_slcut.ml), as in Thm 3.29 (RFA_P2_THM_3_29, src/pc_rfa_shi329.ml).
- Lean: FrenzyMath records that the Shi cutoff argument needs the full space-time slab (PoincareLib/Geometry/RicciFlow/Surgery/Induction/ScalarPersistence.lean:54, M47LocalScalarPersistenceStatement).

### MT6. Thm 4.23: the dichotomy for Ric >= 0
- Location: Ch 4, Sec 4.1, Thm 4.23, first sentence, p. 74. Kind: error.
- Issue: For compact 3-dimensional M, "if Ric(x,0) >= 0, then either Ric > 0 on M x (0,T) or Ric = 0 on M x [0,T)" is false: round S^2 times a flat circle, g(t) = (1-2t) g_S2 + dtheta^2, has Ricci eigenvalues 1/(1-2t), 1/(1-2t), 0. Hamilton's trichotomy is correct (Ric > 0, flat, or locally the product of a positively curved surface flow with a static line). The roundness part is correct, and all later uses are in the Ric > 0 case.
- HOL: not formalized as stated. Used instead: preservation of positive sectional curvature on a compact component (RFA_P2_THM_4_23, src/pc_rfa_secpres.ml) and Hamilton's pinching for ancient compact flows (RFA_P2B_REQ_PINCH_ROUND3, src/pc_rfa_pinch3.ml).

### MT7. Thm 4.40: the integrated Harnack inequality
- Location: Ch 4, Sec 5.2, Thm 4.40 and its proof, p. 82. Kind: error.
- Issue: For complete flows with bounded non-negative curvature operator on [t1,t2] the theorem states log(R(x2,t2)/R(x1,t1)) >= -d^2_{t1}(x2,x1)/(2(t2 - t1)); the proof drops the term R/(t - T0) of Thm 4.37. False for an expanding gradient soliton with positive curvature operator at its fixed point (R(o,t) = R(o,1)/t, x1 = x2 = o). Hamilton's version has the factor (t1 - T0)/(t2 - T0); the printed form is the ancient case.
- HOL: not used in MT's form (its only use, Claim 9.68, is bypassed by Tao's proof of Lemma 9.65). The trace Harnack inequality keeps the 1/(t - a) term (RFA_P2B_REQ_RFA_HARNACK, src/pc_rfa_htrace.ml), and its integrated form keeps the factor ((t + Tm) R non-decreasing, P2FL_HARNACK_MONO, src/pc_p2c_c1116a.ml).
- Lean: FrenzyMath records the same correction (PoincareLib/Geometry/RicciFlow/Harnack.lean:42, FiniteHarnackPath.integrated).

### MT8. Prop 5.14 and Thm 5.15: the time endpoints and completeness
- Location: Ch 5, Sec 2, Prop 5.14 and Thm 5.15, pp. 90-92. Kind: error.
- Issue: (a) the hypotheses are imposed for "every compact interval I subset (T',T) containing 0" with T' <= 0 <= T; when T = 0 or T' = 0 (allowed, and T = 0 in most uses) there is no such I, so the hypotheses are vacuous and the conclusion is false; the uses also need the base time itself. Correct form: I ranges over compact intervals in (T',T) u {0}; at an initial endpoint 0 the slices converge smoothly only with derivative bounds there (Thm 3.29). (b) Completeness of every limit slice is false in general (Giesen-Topping's instantaneously complete flow from the flat unit disc, preceded by the static disc); the proof uses a curvature bound on M_inf x I although C(A,I) depends on A.
- HOL: Thm 5.15 (P2_THM_5_15_STATEMENT, src/pc_p3_iface.ml) takes any interval J containing 0 whose least element, if any, is 0, assumes derivative bounds there, and asserts completeness at time 0, and on [a,b] only under a curvature bound uniform in A; it is P2CO_THM_5_15 (src/pc_p2c_fl515.ml), from Thm 5.11 (P2CY_THM_5_11, src/pc_p2c_hreg.ml). Prop 5.14 is P2CR_PROP_5_14 (src/pc_p2c_fl514.ml), with a limit smooth from time 0 when 0 is the least element.
- Lean: FrenzyMath records corrected hypotheses and an interior reference time (PoincareLib/Geometry/RicciFlow/Blowup/Controlled/Theory.lean:71, RepairedControlledBlowupLimitTheory).

### MT9. Sec 5.3: the Gromov-Hausdorff distance on bounded complete spaces
- Location: Ch 5, Sec 3, after Lemma 5.18, p. 93. Kind: error.
- Issue: "the restriction of the Gromov-Hausdorff distance to complete metric spaces of bounded diameter is a metric" is false (true for compact spaces): X = {x_n} with d(x_n,x_m) = 1 + 1/max(n,m), and Y = X plus a point at distance 1 from every x_n, are not isometric but at distance 0, also in the pointed version.
- HOL: not used (geometric limits are smooth Cheeger-Gromov limits).

### MT10. Lemma 5.25: uniqueness of limits
- Location: Ch 5, Sec 3, Lemma 5.25, p. 95. Kind: error.
- Issue: Complete locally compact based metric spaces that are limits of the same sequence need not be isometric, and "by the local compactness and completeness, these closed balls are compact" is false: the spaces X and Y of MT9 are both limits of the constant sequence X. True for length spaces or proper spaces, the only case used.
- HOL: not used.

### MT11. Example 5.26: geometric versus Gromov-Hausdorff convergence
- Location: Ch 5, Sec 3, Example 5.26, p. 95. Kind: error.
- Issue: Asserted without proof, and false when incomplete manifolds are allowed, as Def 5.3 does: a flat unit disc with a thin strip can converge geometrically to the disc while the balls of radius 3 converge to the disc with a segment attached. It holds for complete manifolds, the only case compared (p. 219).
- HOL: not used.

### MT12. Props 6.13, 6.33, Lemma 6.14 and Cor 6.21: second variation with moving endpoints
- Location: Ch 6, Prop 6.13 (p. 110), Lemma 6.14 and (6.7) (pp. 110-111), Cor 6.21 (pp. 114-115), Prop 6.33 (p. 120). Kind: error.
- Issue: Cor 6.21 asserts d^2 L(gamma_u)/du^2 >= 0, with equality only for Y = 0, for every family whose variation field Y vanishes at both endpoints; but the endpoints may still move to second order: in flat static R^n, gamma_u = gamma + u^2 (tau/taubar) w has Y = 0 and d^2 L/du^2 = 4<Z,w> < 0 for w = -Z. Props 6.13, 6.33 and Lemma 6.14 have the same defect. They are correct for families with fixed endpoints (6.13, 6.21), or starting at x (6.14, 6.33), which is how the book uses them, except for one family in Claim 6.42 whose endpoint is unspecified.
- HOL: no second-variation statement is used. The absence of conjugate points before the end of a minimizing L-geodesic (Props 6.30-6.31) is proved with explicit fixed-endpoint competitors (P2AL_NO_CONJ, src/pc_p2a_lsv.ml), and injectivity of the L-exponential map on initial vectors of minimizers by corner cutting (P2A_INJ_FIX, src/pc_p2a_inj.ml).

### MT13. Claim 8.6: the constant 2
- Location: Ch 8, Claim 8.6, p. 173. Kind: error.
- Issue: With C0 = C1/r^3 and taubar = eps r^2, Lemma 6.60 gives the factor e^(2 C1 eps/r), unbounded as r -> 0, because one constant bounds both |grad R| and |Ric|. After rescaling to r = 1 only a deviation C(n) eps (1 + |Z|) follows, and the printed bound 2 eps (1 + |Z|) is false for n = 3 (shrinking round S^3 with |Z| = 2: deviation about 7.3 eps). The local repair (C(n) eps in Claim 8.7, smaller eps0) leaves Lemma 8.3 and Thm 8.1 unchanged.
- HOL: P2AZ_SMALLZ (src/pc_p2a_smz.ml) proves the claim with a dimensional constant C(n) (statement P2A_SMALLZ_STATEMENT, src/pc_p2a_defs.ml); Thm 8.1 is P2AT_THM_8_1 (src/pc_p2a_t81u.ml).

### MT14. Claims 8.5 and 8.8: ranges of the statements
- Location: Ch 8, Claim 8.8 and Claim 8.5(2), p. 174. Kind: error (misprint).
- Issue: Claim 8.8 is stated "for any 0 <= tau1 <= tau0"; for tau1 near tau0 >= r^2 the parabolic region need not exist and the metric ratio can be e^(+-n(n-1)). Only tau1 = eps r^2 is meant and used. Claim 8.5(2) is stated on B(x,T,r/2) but proved on B(x,T,r).
- HOL: P2AP_PARABOLIC (src/pc_p2a_par.ml) proves both claims in the form used, on a parabolic region with |Rm| <= r^-2.

### MT15. Lemma 9.23: the sign of D(psi)
- Location: Ch 9, Lemma 9.23, p. 191. Kind: error (misprint).
- Issue: The lemma concludes D(psi) <= 0; it should be >= 0, which is what the proof shows ((9.9), D >= 0 in the weak sense) and what Cor 9.24 states.
- HOL: proved with the sign >= 0 and Lipschitz test functions in the limit lemma of Prop 9.20 (P2BW_T1_LIMIT and P2BW_LIMIT, src/pc_p2b_w920.ml).

### MT16. Cor 9.26: two slips in the lower bound for l
- Location: Ch 9, Cor 9.26, p. 195. Kind: error (misprint).
- Issue: The term -n/(2 (tau')^2) should read -n tau'/2, and the distance is that of g_k(-tau_0), not g_k^2(-tau_0).
- HOL: used in the corrected form in the limit step of Prop 9.20 (P2B_W920_G3_ROUTE, src/pc_p2b_g3.ml).

### MT17. Cor 9.70: the radius of the ball
- Location: Ch 9, Cor 9.70, p. 229. Kind: error (misprint).
- Issue: "R(q',t) <= delta^-2 for all q' in B(p,0,delta)" does not follow: Claim 9.69 gives only R <= C1 there. Replacing delta by min(delta, C1^(-1/2)) repairs it.
- HOL: not used. Lemma 9.65 is proved on Tao's route, which bypasses Claims 9.66-9.70 (see MT72).

### MT18. Prop 9.79(3): the bound R(x) <= 2
- Location: Ch 9, Prop 9.79(3), pp. 232-233. Kind: error.
- Issue: Closeness in the C^[1/eps] topology of Def 2.16 is not scale invariant. After normalizing R(x) = 1 the l-th derivatives are multiplied by R(x)^(-l/2), so the statement fails as R(x) -> 0 under the printed hypothesis R(x) <= 2. A lower bound on R(x) is what is needed; large R is harmless, and the uses on pp. 325 and 407 are at large R.
- HOL: the slice form P2_PROP_9_79_SLICE_STATEMENT (src/pc_p3_iface.ml) measures closeness for the normalized metric R(x) g, which is scale invariant, so no bound on R(x) appears. It is proved as P2_PROP_9_79_SLICE (src/pc_p2b_capfix.ml) from the uniform cap form P2B_PROP_9_79_CAP_FIX.

### MT19. Thm 9.93(2): the lower diameter bound
- Location: Ch 9, Thm 9.93(2), p. 242. Kind: error (misprint).
- Issue: The lower bound C^(-1/2) R(x,0)^(-1) < diam(M,g(0)) is not scale invariant; read C^(-1) R(x,0)^(-1/2), which follows from Prop 9.91 and Vol <= omega_3 diam^3. Def 9.75(4) needs exactly this form (Cor 9.94).
- HOL: the C-components of the formalization (rfs_c_component, src/pc_rfs_geom.ml) carry the scale-invariant bounds C^(-1) (sup R)^(-1/2) < diam < C (inf R)^(-1/2); compact kappa-solutions are shown to be C-components in src/pc_p2c_e994a.ml (P2KC_CCOMP_SOME).

### MT20. (10.2): d for d^2 in the cone metric
- Location: Ch 10, (10.2), p. 256; proofs of Lemma 10.25 (p. 260, two displays) and Prop 10.29 (p. 262, three displays). Kind: error (misprint).
- Issue: (10.2) reads d((x,s1),(y,s2)) = s1^2 + s2^2 - 2 s1 s2 cos(min(d_X(x,y), pi)); the left side should be d^2. The same slip recurs in the proofs of Lemma 10.25 and Prop 10.29, where two displays also lack the cosine.
- HOL: the cone at the end of a tube is described by a cone function with the cosine law in squared form (P2BK_END_CONE, src/pc_p2b_cone4.ml).

### MT21. Lemma 12.6: positive curvature at t0 = 0
- Location: Ch 12, Lemma 12.6, p. 297. Kind: error (misprint).
- Issue: "for each t0 in [0,T) ... complete and of positive curvature": at t0 = 0 only sec >= 0 holds (the standard initial metric has flat directions far out); sec > 0 holds for t0 > 0, as Thm 12.5(3) says.
- HOL: the standard solution is required to have positive sectional curvature for 0 < t < 1 only (P2_THM_12_5_STATEMENT, src/pc_p3_iface.ml); sec >= 0 on the whole flow is proved by restarts (src/pc_p2c_stdres.ml).

### MT22. (12.17)-(12.18): two coefficients
- Location: Ch 12, (12.17)-(12.18), pp. 313-314. Kind: error (misprint).
- Issue: The terms -(2/r) dr/dt and -2 xi(w,t) should be -(1/r) dr/dt and -xi(w,t) (substitute rho = r e^(rho~) into (12.16); at t = t0, rho~ = 0, harmonicity of the identity gives rho~_t = -(1/r) dr/dt). The other terms of (12.17) are right. The leading term -xi ~ -C(t)/r is what breaks the decay estimate (MT24).
- HOL: not used: uniqueness of the standard solution is proved without Secs 12.6-12.8 (see MT24).

### MT23. Claim 12.23(1): the asymptotics of e^(h~)
- Location: Ch 12, Claim 12.23(1), p. 315. Kind: error (misprint).
- Issue: e^(h~(r^2,t)) is asymptotic to sqrt(2(1-t))/r, not to 1/((1-t) r) (f = r e^(h~) tends to sqrt(2(1-t)), the radius of the round S^2 of scalar curvature 1/(1-t)). Parts (2), (3) and (6) use only e^(h~) ~ c/r.
- HOL: not used (see MT24).

### MT24. Sec 12.7.5 and Prop 12.25: the decay estimate is false
- Location: Ch 12, Sec 12.7.5: the bound on G and (12.27) (p. 318), (12.28) (p. 319), Prop 12.25 (p. 320). Kind: error.
- Issue: The book asserts |G(rho~_i,x,t)| <= C8/(1+|x|)^2, |rho~|, |nabla rho~| <= lambda/(1+|x|)^2, and |nabla^i rho~| <= C14/(1+|x|)^2 for i <= 3. But along a radial geodesic dr/dt tends to C(t) = -int_0^inf Ric(d_s,d_s) ds < 0, so xi = r^(-1) dr/dt ~ C(t)/r (as Claim 12.23(4) itself says) while the other terms of G are O(r^-2): G = -C(t)/|x| + O(|x|^-2) already for i = 0, and rho~ ~ a(t)/|x| with a(t) > 0. Prop 12.26 is correct, and Cor 12.27 survives with the true asymptotics. Repairs: the iteration closes with exponent 1 instead of 2, or Prop 12.26 is proved without the asymptotic hypothesis by a barrier maximum principle. On the book's route this feeds the uniqueness of the standard solution (Thm 12.5(1)), which Lemma 16.8 and Prop 16.5 use.
- HOL: uniqueness of the standard solution follows from the uniqueness of complete flows of bounded curvature that admit an exhaustion function with bounded geometry, proved with Kotschwar's energy and a weight exp(-lambda phi) (RFU_A14, src/pc_rf_unique_a14u.ml; src/pc_rf_unique_complete.ml), applied with the bounded geometry of the standard initial metric (P2CN_STD_BOUNDED_GEOM, src/pc_p2c_stdgeom.ml): STDS_UNIQUE_ROUTE (src/pc_p2c_stdflow.ml). The harmonic map heat flow of Secs 12.6-12.8 is not used.
- Lean: FrenzyMath replaces MT's uniqueness proof by an energy argument (PoincareLib/Geometry/RicciFlow/Surgery/StandardCap/Uniqueness/Main.lean:64, repairedStandardCapUniqueness). The Qin et al. proof proves no uniqueness theorem; its results quantify over all standard solutions.

### MT25. Cor 12.36: the range of the conclusion
- Location: Ch 12, Cor 12.36, pp. 327-328. Kind: error.
- Issue: "for all n sufficiently large, and any point y_n in the image of rho_n, one of the following holds": geometric convergence based at x_n controls only compact subsets of R^3 x [0, theta). True version: points over K x [0, theta'] for n >= n(K, theta').
- HOL: not used (never cited; Ch 17 uses Thm 12.32 and Prop 9.79 directly).

### MT26. Claim 13.1: the constant eta
- Location: Ch 13, Claim 13.1 and the definition of eta, p. 332; Sec 13.3.3, pp. 340-341. Kind: error (misprint).
- Issue: The book sets eta = sqrt(1 - delta) and argues that, since R(x0) g is within delta of h0 x ds^2, R(x0) g >= eta (h0 x ds^2). Def 2.16 gives only R(x0) g >= (1 - delta)(h0 x ds^2), and 1 - delta < sqrt(1 - delta); the metric h0 + (1 - 0.99 delta) ds^2 is a counterexample. With eta = 1 - delta the argument works (only eta = 1 - O(delta) is used), and Thm 13.2(3) is true. Claim 13.1 proves Thm 13.2(3), which is the whole proof of Prop 15.12.
- HOL: the surgery metric is built with eta = 1 - delta (src/pc_p3_s13met.ml), and Thm 13.2 is P3_THM_13_2 (src/pc_p3_s13thm.ml).

### MT27. Lemma 13.15: two statements on the cap
- Location: Ch 13, Lemma 13.15, p. 341. Kind: error (misprint).
- Issue: The radius of B_g~(p, D + 5 + A0) lacks the factor R(x0)^(-1/2), and "pulls back the metric g~ to be within 2 delta of the standard initial metric" is false on the cap, where the deviation reaches 2K delta e^(q(A0+3)/(A0+4)) >> delta; a bi-Lipschitz closeness 1 + O(C0 delta) suffices for the proof.
- HOL: not used (never cited).

### MT28. Sec 14.1.1: the topology of the model chart P
- Location: Ch 14, Sec 14.1.1, p. 343. Kind: error (misprint).
- Issue: "the open subsets of P are the open subsets of the usual topology on the open square together with open subsets of (0,1) x [0,1)": this family is not closed under unions; the topology they generate is meant.
- HOL: not used. Ricci flows with surgery are histories of smooth flows on fixed manifolds joined by cut-and-cap events (the type rfs_history, src/pc_rfs_history.ml), not a space-time with charts of type P.

### MT29. Def 14.18: the scalar curvature of the shrinking cylinder
- Location: Ch 14, Def 14.18, p. 352. Kind: error (misprint).
- Issue: "-1 < t <= 0, where the scalar curvature of the h0(t) is 1 - t" should be 1/(1 - t), as in the proof of Prop 15.2 (p. 354).
- HOL: strong necks are eps-close to the shrinking cylinder flow (cylinder_flow, src/pc_rf_basic.ml), whose scalar curvature at time t is 1/(1 - t) (src/pc_rfs_geom.ml).

### MT30. Claim 15.1: R for Rm
- Location: Ch 15, Claim 15.1, p. 353. Kind: error (misprint).
- Issue: "|R(x,t)| <= 2" should be |Rm(x,t)| <= 2, as in Prop 4.11 and as used on p. 360; read literally it is false (the normalized unit round S^3 has R = 6). The normalization of Sec 15.0.6 (only r = 1) is weaker than Def 4.10 (all r <= 1); Bishop-Gromov repairs this with another kappa0.
- HOL: the existence time and curvature bound come from PDE_CURVATURE_TIME_STATEMENT (src/pc_pde_iface.ml) with dimensional constants, and the volume normalization of the initial metric is stated for all r <= 1 (src/pc_rfs_geom.ml).

### MT31. Claim 17.3: the choice of theta1
- Location: Ch 17, Claim 17.3, case s = theta1, pp. 399-400. Kind: error.
- Issue: theta1 is chosen by Prop 12.31 so that R >= 8D on the standard solution for t >= theta1, but the pulled back metric is only within a factor 2 of the standard solution (Def 16.12, Prop 16.5), and the flow line has R < 6D. The book concludes that R along the flow line "limits to at least 8D", but the factor 2 gives only R >= 4D < 6D, so the contradiction fails as written. Choosing theta1 for 16D instead of 8D repairs it; A'(theta1), A and delta'' are chosen after theta1, so nothing else moves.
- HOL: Prop 12.31 gives c/(1 - t) <= R on every standard flow (P2_PROP_12_31_STATEMENT, src/pc_p3_iface.ml), so theta1 = max 0 (1 - c/K) works for any K; Claim 17.3 is proved with K = 16D (P3H_CLAIM_17_3_CORE, src/pc_p3_c172d.ml).

### MT32. Claim 18.22: homotopy equivalence or degree one
- Location: Ch 18, Claim 18.22, p. 433. Kind: error.
- Issue: The claim asserts a (1 + eta)-Lipschitz homotopy equivalence X(t') -> X(t). This is false when X(t) is one of the split-off pieces (the map is then only of degree one, e.g. L(p,q) # Sigma -> Sigma); p. 430 itself says "either a homotopy equivalence or a degree-1 map". What the proof of Prop 18.18 uses is a (1 + eta)-Lipschitz map carrying xi(t') to xi(t). In the simply connected case every X(t) is a homotopy 3-sphere and a degree-one map between them is a homotopy equivalence.
- HOL: the jump across a surgery uses (1 + e)-pinch maps from an ancestor component (p4_pinch_ok, src/pc_p4_top.ml; p4_pinch_map, src/pc_p4_defs.ml), built in P4_PINCH_FROM_INV (src/pc_p4_pinch.ml); degree one comes from ATOP_P4_SC_DEGREE_ONE (src/pc_top_p4.ml).

### MT33. Cor 18.28: eta for zeta
- Location: Ch 18, Cor 18.28, p. 434. Kind: error (misprint).
- Issue: "any C^1-loop of length less than eta bounds a disk of area less than eta" should read "of length less than zeta"; as printed zeta is unused and the statement is false for large eta when pi_1(X) != 1.
- HOL: not used (finite extinction uses the width of Colding-Minicozzi, not the loop-space width of Sec 18.3).
- Lean: FrenzyMath records the same correction (PoincareLib/Geometry/Riemannian/LoopSpace/Area/SmallDisks.lean:61, small_loop_filling).

### MT34. Lemma A.9: a missing scale factor
- Location: Appendix, Lemma A.9, pp. 501-502. Kind: error (misprint).
- Issue: The inequalities (1 - alpha)(s(q) - s(p)) <= d(z,q) - d(z,p) <= (1 + alpha)(s(q) - s(p)) are stated "(here we are not assuming that R(x) = 1)", but s is dimensionless, so both bounds need the factor R(x)^(-1/2) (Claim 10.6 uses "the rescaled version").
- HOL: the lemma is stated with the scale factor (APX_A9_STATEMENT, src/pc_apx_defs.ml); the route uses a crude form for s-differences of at least 16/alpha (APX_A9_CRUDE_STATEMENT and APX_A9_IMP_CRUDE, src/pc_apx_csreq.ml).

### MT35. Prop A.11(5): the intersection of two necks need not be connected
- Location: Appendix, Prop A.11(5), last sentence, p. 503; proof p. 504. Kind: error.
- Issue: "Lastly, N cap N' is diffeomorphic to S^2 x (0,1) under a diffeomorphism mapping S(y) to S^2 x {1/2}", with "according to part (3), this intersection is connected" in the proof. False in general: on a round S^2 x S^1 of circumference 3.7/eps, necks centred at s = 0 and s = 1.8/eps meet in two components. True for the component containing S(y'), and the intersection is connected when the neck spheres separate, or for consecutive necks of a chain. Also "mapping S(y)" should be S(y').
- HOL: the Appendix is formalized in its separating form (apx_sphere_sep, src/pc_apx_sep.ml), where the intersection is connected; Prop A.21 is APX_A21 (src/pc_apx_a21.ml).

### MT36. Prop A.19: "do not separate" should be "separate"
- Location: Appendix, Prop A.19, p. 507. Kind: error (misprint).
- Issue: "Suppose that the central two-spheres of these necks do not separate M. Then ... The union U is diffeomorphic to S^2 x (0,1)" is false (a long round S^2 x S^1). The proof uses Lemma A.18, which assumes separation, so "separate" is meant, and precisely "separate the component of M containing X" (separating M fails for disconnected M). The two cases of the proof of Lemma A.20 are swapped to match.
- HOL: Prop A.19 with component-relative separation (APX_A19, src/pc_apx_chain.ml; apx_sphere_sep, src/pc_apx_sep.ml). On the route separation holds because every component of every stage is simply connected (SMT_SC_SPHERE_SEP, src/pc_smt_sep.ml).
- Lean: FrenzyMath records the same correction (PoincareLib/Topology/Manifold/NeckCap.lean:49, module documentation).

## 2. Morgan-Tian: gaps on the route of the formalization

Gaps in results that the formalization proves or uses, in page order. The last note is the one item whose status is unclear.

### MT37. Sec 3.4: the exponential map onto the metric ball
- Location: Ch 1, Sec 3.4, after Def 1.22, p. 14. Kind: gap.
- Issue: "By the inverse function theorem there exists r0 > 0 such that the restriction of exp_p to the ball ... is a diffeomorphism onto B_g(p,r0)": the inverse function theorem gives a diffeomorphism onto some open set; that the image is the metric ball needs the Gauss lemma and a length argument.
- HOL: on an injectivity ball the image of the tangent ball of radius r is the metric ball of radius r (MFD_EXP_BALL, src/pc_geo_dist.ml), from d(x, exp_x v) = |v| (MFD_EXP_DIST) and the Gauss lemma (MFD_GAUSS_LEMMA, src/pc_geo_gauss.ml).

### MT38. The normalization of the curvature operator
- Location: Ch 1, Def 1.7 (p. 7); proof of Prop 3.19 (p. 44); Lemma 4.13 (p. 68); Thm 4.26 and its proof (pp. 76-77); Thm 4.32 (p. 79); Def 4.34 (p. 80). Kind: gap.
- Issue: Def 1.7, Rm(phi,psi) = R_ijkl phi^ij psi^kl, fixes no inner product on 2-forms, and the book uses two normalizations. The proof of Prop 3.19 uses a basis in which the eigenvalues of T are twice the sectional curvatures (tr T = R; Lemma 4.13's T^2 + T^# is right there). The proof of Thm 4.26 sets "S(T) = tr(T), so that R = 2S", that is eigenvalues equal to the sectional curvatures, with reaction ODE lambda' = 2(lambda^2 + mu nu). Thm 4.26, Thm 4.32 and Def 4.34 are true in the sectional normalization (Hamilton's theorem applied to 2g); read in the normalization of Prop 3.19, estimate (2) of Thm 4.26 would be stronger than Hamilton's.
- HOL: the sectional normalization is fixed throughout (mfd_sec_min and mfd_rm_norm, src/pc_mfd_riem.ml). In dimension 3 the curvature operator is the 2-tensor P = (R/2) g - Ric (lpcurv, src/pc_rfa_pevol.ml), whose values on unit vectors are the sectional curvatures (RFA_LSECTIONAL_PCURV_3D), so the factor 2 sits in the reaction term 2(p1^2 + p2 p3) (RFA_BARRIER_REACTION, src/pc_rfa_tmaxp.ml). Def 4.34 is rfs_pinched_at (src/pc_rfs_geom.ml) with the book's constants, and Thm 4.32 is RFA_P2_THM_4_32 (src/pc_rfa_pinch.ml).

### MT39. |Rm| is never defined
- Location: Ch 1, Def 1.7 (p. 7; Introduction p. xvi); Def 4.10 and Prop 4.11 (pp. 67-68); Cor 4.33 (p. 80). Kind: gap.
- Issue: |Rm| is never defined, yet constants depend on the choice. Prop 4.11 (|Rm| <= 2 on [0, 2^-4]) is the doubling-time lemma of Chow-Lu-Ni (Lemma 6.1) for the full tensor norm, while Cor 4.33's |Rm(x,t)| <= R(x,t)/2 holds only for the operator norm in the sectional normalization (for the tensor norm it fails on the unit S^3). Every later curvature-scale condition depends on the same choice.
- HOL: mfd_rm_norm (src/pc_mfd_riem.ml) is the largest absolute sectional curvature. The book's constants 2^-4 and 2 become existential dimensional constants in PDE_CURVATURE_TIME_STATEMENT (src/pc_pde_iface.ml), proved as PDEF_CURVATURE_TIME (src/pc_pde_final.ml); the volume part of Prop 4.11 is PV411_PROP_4_11_VOLUME (src/pc_pv411.ml); Cor 4.33 becomes RFA_PINCH_RM (src/pc_rfa_pinchrm.ml).

### MT40. Prop 1.35: a lower volume bound from an upper comparison
- Location: Ch 1, Sec 6, proof of Prop 1.35, p. 20. Kind: gap.
- Issue: The proof cites Thm 1.31 for "the volume of B(p,eps) is at least that of the ball of radius eps in the n-sphere of radius 1", but Thm 1.31 (curvature bounded below) gives upper bounds. The lower bound is the Gunther-Bishop comparison (sec <= 1, exp_p a diffeomorphism on B(0,eps), eps <= pi), mentioned on p. 19 but never stated. Prop 1.35 is true. "Replacing g by r^2 g" should be r^-2 g.
- HOL: Gunther-Bishop is CMP_GUNTHER (src/pc_cmp_gunther.ml); it supplies the volume bound when initial metrics are normalized (P2AN_NORMALIZE, src/pc_p2a_norm.ml).

### MT41. Facts used as "elementary" or "standard"
- Location: Ch 2, Lemma 2.1 (p. 22), Cor 2.5 (p. 23); Ch 3, Prop 3.12 (p. 40), Claim 3.23 (p. 46); Ch 4, Lemma 4.5 (p. 65), Thm 4.16 (p. 70); Ch 5, the Tits cone (p. 97). Kind: gap.
- Issue: These are called elementary, standard or an easy exercise and used without proof: rays and lines (Lemma 2.1), the angle monotonicity of Cor 2.5, gluing flows in time (Prop 3.12), the reduction of the distance derivative to minimal geodesics (Claim 3.23), Lemma 4.5 (whose reference page is wrong, and which is false as printed with the book's tangent cone, see the typo list), the strong maximum principle Thm 4.16 (no proof or reference; needed with a time-dependent metric), and the independence of the Tits cone of the base point (never used). All are true in the forms needed.
- HOL: proved where used: rays and lines (CMPSO_RAY_EXISTS, src/pc_cmp_soul.ml; APXT_TWO_ENDS_LINE, src/pc_apx_twoends.ml), angle monotonicity (CMP_R1_TOPONOGOV, src/pc_cmp_tpg.ml), Prop 3.12 (PDE_GLUE, src/pc_rf_glue.ml), Claim 3.23 avoided by a backward difference quotient along one minimizing geodesic (RFA_P2B_REQ_RFA_DIST_LOCAL, src/pc_rfa_dist.ml), Thm 4.16 for a smooth time-dependent metric (RFA_STRONG_MAXP_SCALAR, src/pc_rfa_smax1.ml).

### MT42. Lemma 2.14: a submersion is not a product
- Location: Ch 2, Sec 5, end of the proof of Lemma 2.14, p. 29. Kind: gap.
- Issue: "Thus, B defines a smooth Riemannian submersion from M -> R which implies that M is isometric to a product": a function with gradient of norm 1 does not force a product (r on dr^2 + e^(2r) g_flat). Missing step: B_+ is harmonic, so Bochner's formula (Lemma 1.10) gives 0 = |Hess B_+|^2 + Ric(grad B_+, grad B_+), hence Hess B_+ = 0 and M splits.
- HOL: the route needs only the splitting under sec >= 0: a complete connected 3-manifold with sec >= 0 containing a line is locally split along a parallel unit field (CMP_R3_SPLIT, src/pc_cmp_split.ml), proved from the convexity of Busemann functions, without elliptic regularity.

### MT43. Lemma 2.20: the level spheres in a neck
- Location: Ch 2, Sec 6, Lemma 2.20 and its proof, pp. 31-32; used in Prop 9.85. Kind: gap.
- Issue: The proof applies Lemma A.10 without checking its hypothesis that the central sphere separates (true: M is R^3 by the soul theorem). Moreover A.10 needs the middle sixth, not the middle third; A.10 describes only the part of the boundary inside N, and that the whole boundary lies in N needs connected level sets, only asserted in the proof of Prop 2.19; and the conclusion S^2 x I needs Alexander's theorem or the annulus theorem.
- HOL: Lemma 2.20 is not formalized. Prop 2.19 is proved with separation of the neck spheres as a hypothesis (P2AS_PROP_2_19_SEP, src/pc_p2a_219.ml), and the use in Prop 9.85 goes through the topology of the soul (SOULT_SOUL_TOPOLOGY, src/pc_soul_topo.ml), where each neck sphere bounds a ball by the smooth Schoenflies theorem (SCH_SCHOENFLIES_REQ, src/pc_sch_main.ml).

### MT44. Lemma 2.22 and its uses
- Location: Ch 2, Sec 7, Lemma 2.22, p. 33; uses in Cor 3.26 (p. 50), Sec 18.3.2 (pp. 426, 432) and Ch 19 (pp. 439-441). Kind: gap.
- Issue: The comparison lemma (forward difference quotients of f at most psi(t,f) keep f below the solution of G' = psi(t,G)) is right for C^1 psi, but the book also applies it with psi only continuous or Lipschitz (Cor 3.26, Ch 19) and to a function that jumps at surgery times ("According to Proposition 18.18 and Lemma 2.22 we see that W_xi(t) <= w(t) for all t in [T_1,T_2]", p. 432). Needed: a version for continuous psi, locally Lipschitz in f, applied between surgery times, and an argument at each surgery time.
- HOL: comparison lemmas (RFA_DINI_GRONWALL, src/pc_rfa_maxp.ml; P4_DINI_MONO, src/pc_p4_cm.ml) are applied on each slab between surgery times in the width argument (P4_CM_SLAB_FROM_DINI, src/pc_p4_cm.ml), and surgery times are crossed separately (P4_Q_JUMP, inside P4_FINITE_EXTINCTION_FROM_WIDTH, src/pc_p4_top.ml). Cor 3.26 is proved for continuous k (P2AD_REQ_DIST_DISTORTION, src/pc_p2a_dd.ml).

### MT45. Thm 3.11: uniqueness is only cited
- Location: Ch 3, Sec 3, Thm 3.11, p. 39 (sketch pp. 39-40; cf. p. 306). Kind: gap.
- Issue: The uniqueness half ("these flows agree on I cap I'") is only cited ("Hamilton, cf. [29]"), the sketch covers only DeTurck's existence argument, and the step from short-time uniqueness to agreement on I cap I' is missing; p. 306 promises to "mimic the proof of uniqueness in the compact case", which the book never gives.
- HOL: Kotschwar's energy method: two Ricci flows on a closed manifold with the same initial metric agree on the common interval (PDE_UNIQUENESS, src/pc_rf_unique.ml); the version for complete flows of bounded curvature is RFU_A14 (src/pc_rf_unique_a14u.ml).
- Lean: FrenzyMath also uses an energy method (PoincareLib/Geometry/RicciFlow/Local/Energy/Comparison/UniquenessClosure.lean:757, ricciFlowUniqueness_of_difference_energy).

### MT46. Thm 3.11 and Prop 3.12: "standard PDE theory"
- Location: Ch 3, Sec 3, proof sketch of Thm 3.11 and Prop 3.12, p. 40. Kind: gap.
- Issue: Short-time existence rests on "a short-time solution ... by the standard PDE theory", and smooth continuation across the final time on Prop 3.12, called elementary. The companion texts do the same (Chow-Lu-Ni, Thm 2.43, pp. 114 and 118, "standard parabolic theory"), so none of them proves the parabolic theory or the smoothness at the final time of an extended flow.
- HOL: the parabolic theory is formalized: short-time existence (PDEF_STE, src/pc_pde_final.ml) from the existence of the Ricci-DeTurck flow (PDEF_RDT_UNIFORM, src/pc_pde_final.ml), built on the linear theory (PDE_MLIN_HOLDS, src/pc_pde_mexist.ml), and the gauge (PDE_GAUGE, src/pc_pde_gauge.ml); gluing in time is PDE_GLUE (src/pc_rf_glue.ml).

### MT47. Prop 3.33(3) and Thm 3.29: a bootstrap at first order
- Location: Ch 3, Sec 7, Prop 3.33(3) and the proof of Thm 3.29 at k = 1, pp. 52-54. Kind: gap.
- Issue: Even corrected (MT5), the bound |Delta_{g(t)} eta| <= C2 at t > 0 needs control of the change of the Christoffel symbols, that is a bound on |grad Rm| (Shi's Thm 3.27). The book refers to Chow-Lu-Ni, which proves that estimate only by a bootstrap (its Lemma 6.20 controls the second derivatives of the cutoff only as long as the first-order quantity stays below its barrier). So the first step (k = 1) of the proof of Thm 3.29 needs the same bootstrap and is not self-contained.
- HOL: the bootstrap is formalized: at order 1 the change of the Christoffel symbols is bounded from the barrier inequality itself, before the barrier is touched (RFA_SLOC_DG_BOOT, src/pc_rfa_slloc.ml), inside the barrier argument (RFA_LOCAL_BARRIER, src/pc_rfa_slbar.ml).

### MT48. Thms 4.7-4.9 and 4.16: maximum principles for a fixed metric
- Location: Ch 4, Sec 2, Thms 4.7, 4.8 (p. 66), 4.9 (pp. 66-67), 4.16 (p. 70); used in Secs 3-5. Kind: gap.
- Issue: The maximum principles are stated for a fixed metric, but applied along Ricci flows, where the Laplacian is that of g(t); the evolving-frame bundle has a fixed metric but a time-dependent connection, and Thm 4.18 uses the heat flow of g(t). Hamilton's time-dependent versions, and a strong principle with smooth time-dependent coefficients, are needed.
- HOL: all maximum principles are proved for time-dependent metrics: the scalar ones (RFA_MAXP_BARRIER, RFA_MINP_BARRIER, src/pc_rfa_maxp.ml), preservation of lower bounds of the least sectional curvature (RFA_SECMIN_LOWER_PRESERVED, src/pc_rfa_tmaxp.ml), the strong scalar principle (RFA_STRONG_MAXP_SCALAR, src/pc_rfa_smax1.ml), and the strong principle for the least sectional curvature through upper barriers (RFA_P2C_REQ_SMP_POS, src/pc_rfa_smppos.ml; RFA_P2B_REQ_SMP_SPLIT_PT, src/pc_rfa_splitend.ml).

### MT49. Cor 4.20: a zero eigenvalue of Rm
- Location: Ch 4, Sec 4.1, Cor 4.20, p. 73. Kind: gap.
- Issue: From a zero eigenvalue of the endomorphism Rm(x,T) the corollary concludes that a cover splits as (N,h(t)) x (R,ds^2), with the proof "see Lemma 9.1 in [30]"; but the local splitting Cor 4.19 needs a zero eigenvalue of Ric. Missing: Prop 4.17 for nu gives nu = 0 on M x [0,T]; for a parallel nu-eigenvector the evolution of <Te,e> gives lambda mu <= 0 with lambda > 0 (Thm 4.18), so mu = 0 and Ric has a zero eigenvalue; then Cor 4.19 and de Rham's theorem on the universal cover. The same gap recurs in Chs 9 and 11 (MT67, MT88, MT89).
- HOL: the formal statement is local (P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT, src/pc_p2b_splitreq.ml; proved as RFA_P2B_REQ_SMP_SPLIT_PT, src/pc_rfa_splitend.ml): on a connected, possibly incomplete flow with sec >= 0, a plane of zero curvature at (p,t1) makes every earlier slice flat or locally split along a parallel unit field.

### MT50. Lemma 5.7 and Thm 5.6: compactness of metrics
- Location: Ch 5, Sec 1, Lemma 5.7 and the proof of Thm 5.6, pp. 86-87. Kind: gap.
- Issue: Lemma 5.7 (subconvergence of the metrics pulled back by exp, from bounds on all |nabla^l Rm|) has only "the basic point in proving this lemma is to 'find the right gauge'", and the construction in Thm 5.6 (overlap maps, the limit manifold, near-isometric embeddings) is "a standard argument using partitions of unity ... compare [6]". These underlie Thm 5.9, Cor 5.10, Thm 5.11, Prop 5.14 and Thm 5.15.
- HOL: proved in full: Lemma 5.7 is P2C_GAUGE (src/pc_p2c_gauge.ml); the limit manifold is glued from a chart system (P2CL_GLUED_MANIFOLD, src/pc_p2c_cglim.ml); complete limits are P2CK_CG_COMPACT (src/pc_p2c_cg.ml) and incomplete local limits P2GH_LOCAL_COMPACT_G (src/pc_p2c_lcg.ml).

### MT51. Thm 5.9: the injectivity radius on the whole ball
- Location: Ch 5, proof of Thm 5.9 (p. 88); also Thm 5.6 (p. 86) and Cor 5.10 (p. 89). Kind: gap.
- Issue: "it also follows from the same result [Thm 1.34] that the uniform lower bound on the injectivity radius at the central point implies ... a uniform lower bound for the injectivity radius on the entire ball": the chain is Prop 1.35, Thm 1.34 at nearby points, then Thm 1.36; and Thm 1.36 is stated for complete M but applied to the incomplete U_k (p. 86) and to M_k with only relatively compact balls (p. 89). Local versions are needed; they hold by the same proofs.
- HOL: the Cheeger-Gromov-Taylor bound is proved on a ball with compact closure (CMP_T2_CGT, src/pc_cmp_cgt.ml), with the local relative volume comparison (CMP_RELVOL, src/pc_cmp_relvol.ml), and applied at every point of the balls (P2CK_CG_COMPACT_CGT, src/pc_p2c_cg.ml).

### MT52. The class of paths for "minimizing"
- Location: Ch 6, Def 6.2 (p. 106), Def 6.9 (p. 109); Lemma 7.2 (p. 150). Kind: gap.
- Issue: The class of competitors is never fixed: Def 6.2 takes C^1 paths in backward time, Lemma 7.2 uses weak H^{2,1} limits, and Prop 6.30 uses broken paths. For tau1 = 0 and Z != 0 the L-geodesic is not C^1 in tau (|X| ~ |Z|/sqrt(tau)). A class that works: paths absolutely continuous in s = sqrt(tau) with square-integrable velocity; C^1 paths are dense, so "minimizing" does not change.
- HOL: admissible curves (p2a_adm, src/pc_p2a_defs.ml) are continuous and piecewise C^1, with corners allowed, possibly singular at tau = 0, and with integrable L-integrand.

### MT53. Props 6.30-6.31: minimizers have no corners and no conjugate points
- Location: Ch 6, Props 6.30-6.31, pp. 118-119. Kind: gap.
- Issue: "since this latter path is not smooth, its L-length cannot be the minimum" and "Y^ is an L-Jacobi field, which is absurd since it is not a C^2-vector field" leave out the corner-cutting first variation (corner term 2 sqrt(tau_c) <X(tau_c-) - X(tau_c+), Y>), the competitors that are not L-geodesics, and the application of Prop 6.13 to a Lipschitz field (the first-order index form is needed). Only invertibility of the differential is proved; "at tau'" should be tau2.
- HOL: corner cutting gives injectivity (P2A_INJ_FIX, src/pc_p2a_inj.ml), and explicit competitors exclude conjugate points (P2AL_NO_CONJ, src/pc_p2a_lsv.ml).

### MT54. Prop 6.78: convergence and injectivity of the L-exponential maps
- Location: Ch 6, Prop 6.78, pp. 143-144. Kind: gap.
- Issue: Convergence of the Jacobians needs C^1 convergence (smooth dependence of the ODE (6.5)), and injectivity of Lexp on B(0,A) x (0,delta) is not argued (it follows from Z -> (Lexp(Z,tau) - x)/(2 sqrt(tau)) being C^1-close to the identity).
- HOL: the asymptotics of the reduced-volume integrand as tau -> 0 are P2AV_RVI_ASYMP (src/pc_p2a_rva.ml).

### MT55. Lemma 7.2: compactness and regularity of minimizers
- Location: Ch 7, Lemma 7.2, p. 150. Kind: gap.
- Issue: "converge weakly in H^{2,1}" and "being a minimizer of L-length, gamma satisfies the Euler-Lagrange equation and is smooth by the regularity theorem" omit Arzela-Ascoli, weak H^1 compactness of curves in a manifold, lower semicontinuity with a time-dependent metric, and the regularity of H^1 minimizers.
- HOL: minimizers are corner-free L-geodesics by local uniqueness for the boundary value problem (P2A_MIN_LGEOD_FIX, src/pc_p2a_reg.ml; P2A_LOC_BVP, src/pc_p2a_lbvp.ml); the lemma is P2AY_LEMMA_7_2 (src/pc_p2a_l72w.ml). Uniform limits of admissible curves of bounded L-length need not be C^1, so the formalized lemma concludes what the book's later uses need (compare Prop 16.21(1), which claims only a continuous limit).

### MT56. Prop 7.8 and Lemma 7.15: a local length function
- Location: Ch 7, Prop 7.8 (pp. 152-154) and Lemma 7.15 (pp. 157-158). Kind: gap.
- Issue: Lemma 6.49 and inequality (6.11) are proved for points in the injectivity domain U(tau), using minimality, but are applied to a local length function defined by geodesics near a given one. An index-lemma argument (no conjugate points on (tau1, tau], Prop 6.31) repairs this. In Prop 7.8 the coefficient 1/(2 tau^(3/2)) should be 1/(4 tau^(3/2)).
- HOL: the barrier inequality is proved at local minima of l in its slice, in a form that needs no local length function (P2A_BARRIER_FIX, src/pc_p2a_bar.ml, with the Riccati comparison of src/pc_p2a_lric.ml).

### MT57. Cor 7.12: semicontinuity of l_x
- Location: Ch 7, Cor 7.12, p. 156; used in Lemma 16.26, p. 390. Kind: gap.
- Issue: The proof of Thm 7.10 needs l_x lower semicontinuous to get continuity of l_min (Prop 2.23). Hypotheses (1)-(3) give no curvature bounds, so Prop 6.56 cannot supply it, and Lemma 16.26 cites only Prop 16.4(1), (2), (4).
- HOL: P2_COR_7_12_STATEMENT (src/pc_p3_iface.ml) adds lower semicontinuity in time of the slice minimum of l_x as hypothesis (4); it is proved as P2AY_COR_7_12 (src/pc_p2a_c712w.ml), and the formalization of Ch 16 supplies the hypothesis as in Claim 16.25.

### MT58. Thm 7.13 and Lemma 7.15 - Cor 7.24: fillable gaps in the proofs
- Location: Ch 7, pp. 156-164. Kind: gap.
- Issue: The statements are already weak (barrier or distributional) forms and are true, apart from "convex" for "concave" (see the typo list). The proofs have fillable gaps: the local length function of MT56; Claim 7.20 applies (7.2), proved for the barriers phi, to beta^eps, which needs a gradient bound, and "-|v|_h^2 = -|v|_g^2/2" should be "<="; existence of the limit in Def 7.21 (it is monotone because Delta beta is bounded above); and MT59. The equality clause of Thm 7.13 is sketched and not used later.
- HOL: the weak inequalities of Thm 7.13 integrated over space-time are P2AW_W3 (src/pc_p2a_weak.ml), for the requirement P2B_REQ_P2A_WEAK_STATEMENT (src/pc_p2b_w3iface.ml).
- Lean: FrenzyMath also records a weak form (PoincareLib/Geometry/RicciFlow/ReducedGeometry/ReducedVolume/WeakInequality/WeakInequalities.lean:35, reducedLength_weak_inequalities).

### MT59. Remark 7.14: integration by parts
- Location: Ch 7, Remark 7.14, p. 157. Kind: gap.
- Issue: "since nabla l is a smooth, locally bounded vector field on an open subset of full measure, integration by parts yields" is insufficient (a step function has such a gradient); it needs l locally Lipschitz on the whole slice (Prop 7.5(1)), hence W^{1,inf}_loc by Rademacher's theorem.
- HOL: the weak inequalities are proved for the locally Lipschitz reduced length, with the null set of non-smooth points of the flow (P2AW_FLOW_CONJ_NULL, src/pc_p2a_wk4.ml; P2AW_W3, src/pc_p2a_weak.ml).

### MT60. Prop 7.27: rigidity of the reduced volume
- Location: Ch 7, Prop 7.27, pp. 166-167. Kind: gap.
- Issue: (a) "Ric + Hess(l) = g/(2 tau); in particular l_x is smooth" is known only on the dense set U_x(tau); a continuity argument (J > 0 everywhere, Lexp a local diffeomorphism, injective and onto) gives U~(tau) = T_pM. (b) The gradient flow phi_tau needs linear growth of nabla l. (c) "|Rm| = K taubar^2/tau^2" should be K taubar/tau. (d) The last step, R^n/Gamma with Gamma nontrivial, needs one line (V~ < (4 pi)^(n/2)). Also "by Lemma 7.25" should be Thm 7.26.
- HOL: the rigidity in the form Cor 9.14 uses is P2AU_FLOW_RV_RIGID (src/pc_p2a_rigid.ml).

### MT61. Closed versus half-open parabolic neighbourhoods
- Location: Ch 8, Thm 8.1(2)-(3), p. 169; Defs 9.1 (p. 180), 14.14-14.15 (p. 351). Kind: gap.
- Issue: Thm 8.1 assumes bounds on the closed neighbourhood B(x,T,r) x [T - r^2, T], while the definitions of noncollapsing use (t - r^2, t]. Applying Thm 8.1 with r' < r and letting r' -> r bridges the two.
- HOL: Thm 8.1 is stated and proved with half-open neighbourhoods (P2_THM_8_1_STATEMENT, src/pc_p3_iface.ml; P2AT_THM_8_1, src/pc_p2a_t81u.ml).

### MT62. Standard analysis used without proof in Chapters 6-7
- Location: Ch 6-7 (Lemmas 6.8-6.18, 7.3, Prop 6.78; Lemma 7.2, Claim 6.68; Cor 6.67, Remark 7.14; Claim 7.20, Thm 7.13). Kind: gap.
- Issue: ODE existence and smooth dependence, the direct method, Arzela-Ascoli and H^1 regularity, Rademacher's and Sard's theorems, mollification and elliptic regularity are used as "usual results". They are applied correctly, apart from MT52, MT54, MT55 and MT59.
- HOL: proved where used, e.g. ODE flows (ODE_FLOW_DIFFEO, src/pc_ode_vf.ml), the boundary value problem (P2A_LOC_BVP, src/pc_p2a_lbvp.ml) and the regularity of minimizers (P2A_MIN_LGEOD_FIX).

### MT63. Prop 9.20: smoothness of the limit reduced length
- Location: Ch 9, Prop 9.20, p. 188, and its proof, p. 198. Kind: gap.
- Issue: "by parabolic regularity l_inf is a smooth function" is uncited, and the limit equations hold only weakly (Lemmas 9.21-9.31 work with W^{1,2} and distributions). Smoothness does not follow from elliptic regularity on each time slice, as the text suggests: Lemma 9.33 differentiates in time, and u(x,tau) = |tau - tau0| x_1 is Lipschitz and harmonic in x for every tau but not differentiable in tau. What is needed is interior regularity of locally Lipschitz weak solutions of the linear conjugate heat equation for U = tau^(-n/2) e^(-l_inf).
- HOL: interior regularity of weak solutions of the conjugate heat equation (WAN_CONJ_HEAT_REG, src/pc_wan_preg.ml), applied in chart boxes (P2BW_REG, src/pc_p2b_w920.ml); Prop 9.20 is P2B_PROP_9_20_ROUTE (src/pc_p2b_p920.ml) with closed form P2BZ9_PROP_9_20 (src/pc_p2b_close9.ml).

### MT64. Lemma 9.25: the curvature bound on the second ball
- Location: Ch 9, proof of Lemma 9.25, pp. 193-194. Kind: gap.
- Issue: The proof bounds R(p',tau) <= (3/tau)(tau^(-1/4) + (sqrt 3/2) tau^(1/4))^2 (l(p,1) + 1) on the first ball, but then sets K with l(q,1) + 1 and applies Prop 3.21 on both balls; since l(q,1) <= l(p,1), this K does not bound Ric on the first ball. Using l(p,1) + 1 in both r_0 and K repairs it. On p. 194, l^(1/2)(q',tau) <= l^(1/2)(q,1) + ... should have l^(1/2)(gamma_2(tau), tau).
- HOL: P2B_LEMMA_9_25_ROUTE (src/pc_p2b_l925.ml) proves the lemma at a general backward time, by integrating a Dini-derivative bound for the distance of the two minimizers.

### MT65. The tail estimate after Cor 9.26
- Location: Ch 9, p. 195. Kind: gap.
- Issue: The estimate integrates over complements of g(-tau_0)-balls with respect to dvol_g(-tau), which Bishop-Gromov does not control; using Lemma 9.25 at the same time instead works, since {d_(-tau_0) >= s} is contained in {d_(-tau) >= s}.
- HOL: the reduced volume of the limit is the limit of the reduced volumes (P2BX_G3_RVOL, src/pc_p2b_g3a.ml; route P2B_W920_G3_ROUTE, src/pc_p2b_g3.ml).

### MT66. Thm 9.11: the limit soliton is not flat
- Location: Ch 9, proof of Thm 9.11, p. 203. Kind: gap.
- Issue: "if (M_inf, g_inf(t)) is flat ..., then ... isometric to R^n. According to Proposition 7.27 this implies V~_inf(tau) = (4 pi)^(n/2)". Prop 7.27 is the converse, and both results concern the reduced length from a point, which l_inf is not known to be (Remark 9.19). Repair: on a flat slice Claim 9.36 gives l_inf = |x|^2/(4 tau) + <x,a> + b tau, (9.5) with R = 0 forces b = |a|^2, so l_inf = |x + 2 tau a|^2/(4 tau) and the Gaussian integral is (4 pi)^(n/2), contradicting Cor 9.14.
- HOL: this is the argument formalized in the soliton step (statement P2B_SOLITON_FROM_LINF_STATEMENT, src/pc_p2b_chainstmts.ml; P2BZ9_SOLITON_FROM_LINF_FIX, src/pc_p2b_close9.ml); Thm 9.11 is P2BZ9_THM_9_11.

### MT67. Prop 9.39: the splitting of the whole flow
- Location: Ch 9, Prop 9.39, last sentence, p. 205; the same in Lemma 9.84 (p. 237) and Prop 9.85 (p. 239). Kind: gap.
- Issue: "it follows from the maximum principle (Corollary 4.19) that the entire flow splits as a product with a line": Cor 4.19 is local and Cor 4.20 splits only a cover. Repair: g_inf(-1) splits globally (Thm 5.35), and the parallel null line field stays parallel for t <= -1.
- HOL: the limit with a line at time 0 and the splitting backward in time are P2BZ9_SPLIT_AT_INFINITY (src/pc_p2b_close9.ml), on the time invariance of a parallel field (P2BX0_TIME_INVARIANCE, src/pc_p2b_x0.ml).

### MT68. Cor 9.44: roundness of the compact asymptotic soliton
- Location: Ch 9, proof of Cor 9.44, p. 208. Kind: gap.
- Issue: "by Hamilton's pinching toward round result or Ivey's theorem (see Theorem 4.23), this implies that the (M,g(t)) are all exactly round". Thm 4.23 says nothing at fixed times, and Ivey's theorem is irrelevant here. Needed: Hamilton's pinching estimate with constants tending to 0 along the sequence, or preservation of the pinching set {lambda <= C nu} plus Schur's lemma.
- HOL: preservation of pinching and Schur's lemma (RFA_P2B_REQ_PINCH_ROUND3, src/pc_rfa_pinch3.ml) give Cor 9.44 (RFA_P2B_COR_9_44_ROUTE, src/pc_rfa_c944.ml; closed form P2BZ5_COR_9_44, src/pc_p2b_close95.ml).

### MT69. Cor 9.50(1): a self-reference and a missing case
- Location: Ch 9, Cor 9.50(1), p. 213. Kind: gap.
- Issue: Part (1) refers to "the hypotheses of Proposition 9.50" (meaning 9.39) and its proof cites Cor 9.40; read literally it is vacuous, and as intended Cor 9.40 does not cover non-compact M with finite asymptotic curvature. Correct proof: unbounded curvature on a slice gives points as in 9.39, contradicting 9.40; so the curvature is bounded, the flow is a 2-dimensional kappa-solution, and (3) (proved via (2), independently of (1)) gives compact and round. On p. 217 "except possibly compactness" should be non-compactness.
- HOL: the 2-dimensional case enters through Hamilton's entropy for ancient flows on S^2 (statement P2B_REQ_S2_ENTROPY_STATEMENT, src/pc_p2b_s2entreq.ml; proved as S2E_S2_ENTROPY, src/pc_s2ent_flow.ml).

### MT70. Cor 9.54: uniqueness at every time
- Location: Ch 9, proof of Cor 9.54, pp. 217-218. Kind: gap.
- Issue: "this is clear by uniqueness of the Ricci flow in the compact case": Thm 9.42 is applied only at t = -1, and earlier times would need backward uniqueness; the cylinder case also needs forward uniqueness on a non-compact manifold. Repair: (9.2) holds at every t < 0, so Thm 9.42 applies to |t_0|^(-1) g_inf(t_0) for every t_0, followed by forward uniqueness from t_0 in the compact case and Cor 9.50(3) for the S^2 factor.
- HOL: the asymptotic soliton is stated with the soliton equation at every time (P2B_THM_9_11_STATEMENT, src/pc_p2b_chainstmts.ml), and Thm 9.42 with Cor 9.54 in flow form is P2BZ9_THM_9_42F (src/pc_p2b_close9.ml).

### MT71. Prop 9.58, Thm 9.59, Thm 9.64
- Location: Ch 9, Prop 9.58 (pp. 220-221), Thm 9.59 (p. 222), Thm 9.64 (p. 229). Kind: gap.
- Issue: Prop 9.58 is sound apart from MT68 and MT70 ("at most 3/2" holds only at the centre). The proof of Thm 9.59 is terse (the compact case, the hypothesis of Prop 9.39 coming from Prop 9.56 only in a footnote, the transfer of the volume ratio to the limit). Thm 9.64 cites Cor 9.53 (p. 229), stated only for asymptotic solitons on t < 0, for the final slice t = 0 of the limit; its proof works for any complete ancient non-flat kappa-noncollapsed 3-dimensional flow with Rm >= 0 and dR/dt >= 0, but at the final slice a form for flows up to and including t = 0 is needed.
- HOL: Prop 9.58 (P2AK0_PROP_9_58_ROUTE, src/pc_p2a_kap0.ml), Thm 9.59 on Tao's route (Prop 3.18.3 of Tao's notes: P2AV9_THM_9_59_ROUTE, src/pc_p2a_asv.ml), Thm 9.64 (P2AT64_THM_9_64_ROUTE, src/pc_p2a_t964.ml) with Cor 9.53 at the final slice (P2B_COR_9_53_FINAL_ROUTE, src/pc_p2b_shrinkfin.ml); closed forms P2BZ5_PROP_9_58, P2BZ5_THM_9_59, P2BZ5_THM_9_64 (src/pc_p2b_close95.ml).
- Lean: FrenzyMath's blueprint follows Kleiner-Lott for Thms 9.59 and 9.64 (PoincareConjecture/blueprint/chapters/ancient-models.tex:638 and :924).

### MT72. Lemma 9.65: the compact case
- Location: Ch 9, Lemma 9.65, first lines, p. 225. Kind: gap.
- Issue: The proof starts from Prop 9.56, which assumes M non-compact, but Thm 9.64 must cover compact kappa-solutions (Claim 9.90, Prop 9.91, Cor 9.71). Tao's argument (Prop 3.18.7 with Cor 3.18.6 = MT Cor 9.62) works at p itself and bypasses Claims 9.66-9.70 and Prop 9.56.
- HOL: Lemma 9.65 on Tao's route (P2AL65_LEMMA_9_65_ROUTE, src/pc_p2a_l965.ml; closed form P2BZ5_LEMMA_9_65, src/pc_p2b_close95.ml).

### MT73. Prop 9.83(1): positive curvature at all times
- Location: Ch 9, Prop 9.83(1), p. 236. Kind: gap.
- Issue: The proof via Cor 4.20 propagates a zero eigenvalue at t_1 only to earlier times; positivity at later times would need uniqueness for complete non-compact flows. The only use (Prop 9.85) needs t = 0.
- HOL: stated and proved at time 0 (P2BPK_PROP_9_83K_ROUTE, src/pc_p2b_p983k.ml): a zero plane at time 0 gives, by the strong maximum principle, zero planes at all earlier times and the cylinder model.

### MT74. Prop 9.85: uniformity in kappa and the soul
- Location: Ch 9, proof of Prop 9.85, pp. 237-239. Kind: gap.
- Issue: (a) the constants D(eps), D_1(eps) are meant to be independent of kappa (Cor 9.88 "for any kappa > 0"), but Thm 9.64 needs a fixed kappa; Prop 9.58 (non-compact implies non-round, hence kappa_0-noncollapsed) supplies it. (b) "By Lemma A.10 ... the soul is not the center of a strong 2 eps-neck" is not in A.10; two sub-necks on either side of p would give two disjoint spheres in one level set of d(p,.), contradicting the connectedness of level sets.
- HOL: Prop 9.85 in the length-L form is P2A985D_PROP_9_85L_ROUTE (src/pc_p2a_985d.ml), with Prop 9.58 among its inputs.

### MT75. Remark 9.86: any non-neck base point
- Location: Ch 9, Remark 9.86, p. 237 (with Lemma 9.84 and Prop 9.85). Kind: gap.
- Issue: The remark extends Prop 9.85(1) to any point that is not the centre of a neck, without proof. The line in the limit at the closest non-neck point comes from Lemma 2.20, whose separation hypothesis (the neck separates the base point from infinity) the book proves only for a soul as base point (Prop 9.85(2), Lemma A.10).
- HOL: the statement is proved at a soul, where the soul side of a neck sphere is a ball (P2B_SOUL_TOPOLOGY_STATEMENT, src/pc_p2b_c994req.ml; SOULT_SOUL_TOPOLOGY, src/pc_soul_topo.ml), and then reduced to a general non-neck point, which lies in a bounded ball about the soul with comparable curvature (P2A985D_PROP_9_85L_ROUTE, src/pc_p2a_985d.ml).

### MT76. Prop 9.85: the two-to-one cylinder quotient
- Location: Ch 9, Lemma 9.84 and Prop 9.85, pp. 238-239. Kind: gap.
- Issue: At a non-neck base point the limit of Thm 9.64 could a priori be the quotient (S^2 x R)/Z_2 by the antipodal map times a reflection, which is orientable and has separating neck spheres. The book excludes it on p. 239 by orientability, which does not exclude this quotient; the reason given on p. 238 (M_k is R^3, so it contains no embedded RP^2) does.
- HOL: only the lower curvature bound needs a positively curved limit; the Z_2 case is excluded by moving the neck sphere of the model to M_k, which would give a two-to-one covering of a ball by a connected shell (Z2X_EXCLUSION, src/pc_z2x_excl.ml; used by P2A985D_PROP_9_85L_ROUTE).

### MT77. Claim 9.90: the negation of the claim
- Location: Ch 9, proof of Claim 9.90, p. 241. Kind: gap.
- Issue: The negation of the claim gives diam > C'_k (max R)^(-1/2), not diam > C'_k R(p_k,0)^(-1/2). Lemma 9.65 closes the gap (diam <= D at the scale R(p_k,0) = 1 gives max R <= C(D)). In the strong-neck case Prop 9.79(2) is needed.
- HOL: Claim 9.90 in a uniform form is P2KD_CLAIM_9_90_ROUTE (src/pc_p2c_c990.ml), with Lemma 9.65 among its inputs.

### MT78. Thm 9.89 and Prop A.25(1): double caps and strong tubes
- Location: Ch 9, proof of Thm 9.89, p. 241; Prop A.25(1), p. 514. Kind: gap.
- Issue: The proof concludes "a double C_0-capped eps-tube", while A.25(1) also allows a union of two (C,eps)-caps; this is excluded by the diameter (two overlapping caps give diam < 2 C_0^(3/2) (max R)^(-1/2); take C_1 >= 2 C_0^(3/2), as Ch 10 does on p. 248). Thm 9.89(3) says strong tube, but A.25 gives an eps-tube; the tube has to be chosen among the strong-neck centres of Claim 9.90. Also max_x R(x,0) should be max_x R(x,t), and "Theorem 9.42" should be Cor 9.54.
- HOL: the compact case of Cor 9.94 in the length-L form (src/pc_p2c_e994.ml; closed form P2BZ5_COR_9_94_L, src/pc_p2b_close95.ml).

### MT79. Thm 10.2: the alternatives quoted from A.21
- Location: Ch 10, Thm 10.2, pp. 247-248. Kind: gap.
- Issue: The alternatives quoted from Prop A.21 omit A.21(3) and A.21(6). Harmless on the route.
- HOL: Thm 10.2 uses the separating form of A.21 (APX_A21, src/pc_apx_a21.ml).

### MT80. Prop 10.7: evolving necks
- Location: Ch 10, Prop 10.7, pp. 253-255. Kind: gap.
- Issue: The proposition asserts that every point is the centre of an evolving 2 eps-neck defined for normalized time 1/2, but the proof gives only time-0 necks (Claim 10.8), flow lines (Claim 10.10) and Rm >= 0 (Claim 10.11). The evolving part follows as in Claim 10.8 with the evolving-neck part of Prop 9.79; its only use (p. 263) also follows from Claims 10.10-10.11.
- HOL: evolving 2 eps-necks of normalized length 1/2 in the limit are P2BTL_LIM_ENECK (src/pc_p2b_tubelim2.ml).

### MT81. Thm 10.2: local compactness
- Location: Ch 10, proof of Thm 10.2, pp. 253, 255 and 263. Kind: gap.
- Issue: (i) p. 253 invokes Thm 5.6, whose hypothesis (4) needs a volume bound with kappa independent of the scale, which the necks do not give (the proof of Thm 5.6 needs (4) only at scales chosen after the curvature bound, where Claim 10.6 gives constants); (ii) p. 255 applies Prop 5.14 to boxes covering a domain that is not a product (and "(-t_0(X), 0]" is a sign slip); (iii) p. 263 applies Thm 5.11, which needs bounds on balls of every radius and gives a complete limit, while only balls of radius < eps^(-1)/2 are controlled.
- HOL: the limits are taken in one chart around the base points (normal coordinates of the time-0 slices) on a ball of R^3 (P2CD_LOCAL_COMPACT_N, src/pc_p2c_lcn.ml); boxes under every point of the limit carry the persistence and curvature margins (P2BTL_LIM_BOXES, src/pc_p2b_tubelim.ml).

### MT82. Lemmas 10.21-10.22: Toponogov in an incomplete space
- Location: Ch 10, Lemma 10.21 (p. 259) and Lemma 10.22 (pp. 259-260). Kind: gap.
- Issue: Thm 2.4 and Cors 2.5-2.6 are for complete manifolds, but they are applied in U_inf, which is incomplete at both ends. Near the end E the minimizing geodesics stay in a compact part of U_inf (Lemma A.7, as in Claim 10.13), where the Hessian comparison gives the triangle comparison.
- HOL: Toponogov's angle comparison in a compact convex region of a possibly incomplete manifold with sec >= 0 (CMP_R8_LOCAL_TOPONOGOV, src/pc_cmp_ltpg.ml).

### MT83. Lemma 10.22: the triangle inequality for angles at E
- Location: Ch 10, Lemma 10.22, pp. 259-260. Kind: gap.
- Issue: "by Corollary 2.6 we have theta_n(x,y) + theta_n(y,z) >= theta_n(x,z)": Cor 2.6 only bounds the sum of the three comparison angles by 2 pi, and the inequality is false for each n (unit S^2, pole p, x and z antipodal on the equator, y midway: pi/3 + pi/3 < pi). The lemma is true: theta is the Alexandrov angle at E in the metric space U_inf u {E}, with rays as geodesics from E, and Alexandrov angles satisfy the triangle inequality in any metric space (Bridson-Haefliger I.1.14).
- HOL: the angle at E of two rays is the limit of comparison angles, and its triangle inequality is proved with a planar comparison triangle as in Bridson-Haefliger I.1.14 (P2BK_EANG_TRIANGLE_ASYM, src/pc_p2b_cone3.ml).

### MT84. Claim 10.31: separation in the Gromov-Hausdorff limit
- Location: Ch 10, Claim 10.31, p. 264. Kind: gap.
- Issue: "taking the Gromov-Hausdorff limit of these spaces, we see that the base point separates ..." : separation does not pass to Gromov-Hausdorff limits without argument (Prop 10.29 gives convergence of annuli only). A direct argument with a direction [mu] != [gamma] (Lemma 10.18) and Lemma 10.21 works.
- HOL: no Gromov-Hausdorff limits are used; the cone data at the end E come from neck geometry (the level-set lemma of src/pc_p2b_cone.ml and P2BK_END_CONE, src/pc_p2b_cone4.ml).

### MT85. Ch 10, Secs 5.2 and 6: metric cones versus Riemannian cones
- Location: Ch 10, pp. 264-265. Kind: gap.
- Issue: The limit is isometric to an open subset of the metric cone over the metric space X(E), but Prop 4.22 needs a cone over a Riemannian manifold (Def 1.14, Prop 1.15). Missing lemma: an open subset of a metric cone that is isometric to a smooth Riemannian 3-manifold is a smooth Riemannian cone (the dilations are smooth homotheties). The same step is missing in Prop 9.56.
- HOL: a cone function on a smooth limit is smooth with Hess(rho^2/2) = g (P2BK_CONE_REGULAR, src/pc_p2b_cone5.ml); then Prop 4.22 gives a flat limit, against R = 1 at the base point (P2BK_BLOWUP, src/pc_p2b_cone9.ml). The no-bad-tube half of Thm 10.2 is P2BK_NO_BAD_TUBE_ROUTE (src/pc_p2b_cone10.ml).

### MT86. Thm 11.1: the alternatives of hypothesis (1)
- Location: Ch 11, Thm 11.1 (p. 267), its proof (p. 269), Lemma 11.11 (p. 274), Claim 11.33. Kind: gap.
- Issue: Hypothesis (1) allows curvature pinched toward positive or non-negative curvature, but the proof uses Thm 10.2, which assumes pinching. Thm 10.2 holds with Rm >= 0 (pinching enters only through (10.1) in Claim 10.11), so it should be restated with both alternatives.
- HOL: the blow-up theorems are formalized for the sequences that the route produces (P2C_THM_11_1_VIEW_STATEMENT, src/pc_p2c_iface.ml; P2BU_THM_11_1_VIEW_ROUTE, src/pc_p2c_blowup.ml).

### MT87. Lemma 11.2 and Assumption 11.18(c): derivative bounds for every canonical neighbourhood
- Location: Ch 11, proof of Lemma 11.2 (pp. 268-269); Assumption 11.18(c) (p. 279). Kind: gap.
- Issue: The proof uses |dR/dt| <= C R^2 and |nabla R| <= C R^(3/2) at every point with a strong canonical neighbourhood. Caps carry these bounds (Def 9.72(8)) and necks and round components get them from closeness, but C-components (Def 9.75) carry none. On an eps-neck |dR/dt|/R^2 is close to 1, so C must exceed about 1 + O(eps), and the neck alternative controls the gradient only for small eps (steep funnels are counterexamples for large eps). Also the bound (11.1), R(y) <= (16/9)(R(z) + r0^-2), needs R(z) >= 0, which pinched flows need not satisfy.
- HOL: C-components carry the derivative bounds (rfs_c_component, src/pc_rfs_geom.ml), the neck case needs eps <= eps0 and C >= 2, and (11.1) uses max 0 R(z) (statement P2C_LEMMA_11_2_STATEMENT, src/pc_p2c_iface.ml; proofs P2C_LEMMA_11_2_DB, src/pc_p2c_l112.ml, and SNGL_P2_L112, src/pc_p2c_sing.ml). P2C_LEMMA_11_2_NONNEG recovers the printed form when R(z) >= 0.

### MT88. Claim 11.7: a zero eigenvalue of Rm
- Location: Ch 11, Claim 11.7, pp. 270-271. Kind: gap.
- Issue: The proof applies Cor 4.19, which needs a zero eigenvalue of Ric; a zero eigenvalue of Rm (eigenvalues lambda, mu, 0 with lambda, mu > 0) gives Ric > 0. Hamilton's strong maximum principle for Rm (so(3) has no 2-dimensional subalgebra, so a null vector forces rank Rm <= 1) is needed and is not in the book (compare Cor 4.20). "Compact surface" is not proved, but bounded curvature still follows.
- HOL: P2BU_CLAIM_11_7 (src/pc_p2c_blowup.ml), with a strong maximum principle for the curvature operator and the resulting local splitting (RFA_P2B_REQ_SMP_SPLIT_PT, src/pc_rfa_splitend.ml).

### MT89. Prop 11.10 and the end of the proof of Thm 11.8: Prop 2.19 under Rm >= 0
- Location: Ch 11, Prop 11.10 and the end of the proof of Thm 11.8, p. 278; also p. 407. Kind: gap.
- Issue: "This limit manifold satisfies the hypothesis of Proposition 2.19 and hence has bounded sectional curvature": Prop 2.19 is for complete positively curved manifolds, and these limits only have Rm >= 0. The strong maximum principle repairs it (each slice is positively curved, or its universal cover splits off a line).
- HOL: Prop 2.19 is proved for sec >= 0 with separating neck spheres, by Toponogov and without the strong maximum principle (P2_PROP_2_19_SEP_STATEMENT, src/pc_p3_iface.ml; P2AS_PROP_2_19_SEP, src/pc_p2a_219.ml).

### MT90. Prop 11.10: Harnack under per-slice curvature bounds
- Location: Ch 11, Prop 11.10, p. 278; Thm 4.37, p. 81; Def 9.2, p. 180. Kind: gap.
- Issue: Thm 4.37 states Hamilton's Harnack inequality for flows "with bounded curvature for each t", and Def 9.2 bounds the curvature of each slice of a kappa-solution separately, while Hamilton's theorem assumes curvature bounded on the time interval. Prop 11.10 then uses the inequality to bound the curvature on [-T, 0] from bounds on each slice ("We still don't know whether the entire flow is of bounded curvature. But now invoking Hamilton's Harnack inequality ..."), which is circular as written.
- HOL: the Harnack inequality is proved for complete flows with |Rm| bounded on the time interval (RFA_P2B_REQ_RFA_HARNACK, src/pc_rfa_htrace.ml); kappa-solutions have |Rm| bounded on [a, 0] for every a (p2b_kappa_solution, src/pc_p3_iface.ml); and the blow-up limit of Thm 11.8 gets this bound without Harnack, from |dR/dt| <= C R^2 at canonical neighbourhoods (P2C_CANON_DERIV, src/pc_p2c_cderiv.ml) and ODE comparison for 1/R (P2BU_THM_11_8_VIEW_ROUTE, src/pc_p2c_blowup3.ml).

### MT91. Claim 11.24: the left end of the time window
- Location: Ch 11, Claim 11.24 in the proof of Lemma 11.23, p. 282. Kind: gap.
- Issue: From necks at times t_n -> T the proof gets flow lines on (T - 1, T] (rescaled) and uses convergence uniformly on compact subsets of B x (-1, 0], which does not control the left end of the target window (T - 1/R(x,T), T]. Repair: u - 1/R(x,u) is strictly increasing at times near neck times (dR/du = Lap R + 2 |Ric|^2 and |Lap R| < R^2 on a neck C^4-close to the cylinder), so for late necks the window of the n-th neck covers the whole target window.
- HOL: Lemma 11.23 is P2C_LEMMA_11_23_ROUTE (src/pc_p2c_sing2.ml), whose core SNGL_LIMIT_CANON proves the neck case directly.

### MT92. Lemma 11.30: facts from the proof of A.21
- Location: Ch 11, Lemma 11.30, p. 286. Kind: gap.
- Issue: The proof uses facts from the proof of Prop A.21, not from its statement.
- HOL: the formal A.21 states them (APX_A21_STATEMENT, src/pc_apx_defs.ml).

### MT93. Lemma 11.30: finitely many horns
- Location: Ch 11, proof of Lemma 11.30, pp. 286-287. Kind: gap.
- Issue: "by compactness ... there can only be finitely many disjoint 2 eps-horns with non-parallel, homotopically non-trivial boundaries" is completed by volume counting: each horn contains half a strong 2 eps-neck of volume >= c (rho/C)^3 inside the compact set. Typos on p. 286: "at most 2 C^2 rho^-2 ... at least 2 C rho^-2" should be "at least 2 C^2 rho^-2 ... at least C rho^-2", "each component of Omega_(rho/2C)" should be Omega^0(rho), and "only one boundary component" should be one end.
- HOL: finiteness by volume counting (P2_LEMMA_11_30_STATEMENT, src/pc_p3_iface.ml; P2HN_LEMMA_11_30_ROUTE, src/pc_p2c_horns.ml).

### MT94. Claim 11.32: canonical neighbourhoods at the final time
- Location: Ch 11, Claim 11.32 (pp. 287-288); the same in Claim 11.33 and the proof of Claim 11.35 (p. 290). Kind: gap.
- Issue: Assumption 11.18(c) covers only times < T_n; at the final slice Thm 11.19(5) and Lemma 11.23 give only strong (2C, 2 eps)-neighbourhoods. So Thms 11.1 and 10.2 must be applied with (2C, 2 eps), which needs the Appendix and Prop 2.19 for 4 eps, as the book does in Ch 17 (p. 403).
- HOL: the blow-up theorems are stated for eps <= eps0 with constants that allow (2C, 2 eps) (P2_THM_11_8_STATEMENT, src/pc_p3_iface.ml).
- Lean: FrenzyMath records a corrected terminal accuracy factor (PoincareLib/Geometry/RicciFlow/Surgery/Singular/DeepHorn/Construction/Sequences/RegularTimes.lean:54, terminalAccuracy_pos).

### MT95. Claim 11.34: RP^2 is not excluded
- Location: Ch 11, Claim 11.34, pp. 288-289. Kind: gap.
- Issue: Gauss-Bonnet gives S^2 or RP^2 for the cross-section, and RP^2 must be excluded (every point of M_inf is the centre of a 3 eps-neck, so M_inf is a tube S^2 x R by A.21); with RP^2 x R the final neck contradiction fails.
- HOL: the splitting of Claim 11.34 is not used: a complete connected non-negatively curved 3-manifold with two ends contains no (C, eps)-cap for small eps (P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT, src/pc_p2c_iface.ml), which gives Claim 11.35 directly (P2HN_NO_CAP_NEAR, src/pc_p2c_horns2.ml).

### MT96. Thm 11.31: the ancient solution on S^2
- Location: Ch 11, proof of Thm 11.31, p. 291. Kind: gap.
- Issue: "invoking Hamilton's result (Corollary 9.50), ... must be a shrinking round S^2": Cor 9.50(3) is for 2-dimensional kappa-solutions, kappa-noncollapsing is not checked, and non-round ancient solutions on S^2 exist without it (King-Rosenau). Claim 11.35, iterated over t <= 0, makes every point a 2 eps-neck centre in the limit, so each slice is close to round after scaling, hence uniformly noncollapsed, and with R <= Q_0 a kappa-solution.
- HOL: a kappa-solution all of whose points at all times are centres of necks is the round cylinder (P2C_REQ_KAPPA_NECKS_ROUND_STATEMENT, src/pc_p2c_iface.ml; closed form P2BZ9_KAPPA_NECKS_ROUND_L_FIX, src/pc_p2b_close9.ml); Thm 11.31 is P2HN_THM_11_31_ROUTE (src/pc_p2c_horns2.ml).

### MT97. Cor 12.12: SO(3)-invariance of the standard solution
- Location: Ch 12, proof of Cor 12.12, p. 304. Kind: gap.
- Issue: Two steps are missing: a solution X(t) of (12.1) with X and nabla X bounded on non-compact R^3 (Dirichlet problems on exhausting balls, local parabolic estimates, a limit), and the decay of |h|^2 at infinity, which is not implied by the asymptotics of g(t).
- HOL: SO(3)-invariance follows from uniqueness: a rotated standard flow is a standard flow from the same initial metric (STDS_GS_SO3, src/pc_p2c_stdsym.ml).

### MT98. Thm 12.28(2): necks of rescaled time 1 + eps
- Location: Ch 12, Thm 12.28(2), p. 323. Kind: gap.
- Issue: The strong necks with rescaled time 1 + eps are not given by Cor 9.95, which the proof cites; they need canonical neighbourhoods of kappa-solutions with necks of every length.
- HOL: Cor 9.94 and 9.95 are proved in a length-L form (P2BZ5_COR_9_94_L, src/pc_p2b_close95.ml), and Thm 12.28 gives necks of length 1 + eps (STDS_THM_12_28, src/pc_p2c_stdc1.ml).

### MT99. Thm 12.29: extending the flow
- Location: Ch 12, proof of Thm 12.29, p. 324; also Prop 12.31, Step 1. Kind: gap.
- Issue: "if the limit metric g(T) exists on all of R^3, then we can extend the flow keeping the curvature bounded": g(T) is complete with bounded curvature, but extending it needs Shi's existence theorem for complete non-compact manifolds, while the book states existence only for compact manifolds (Thm 3.11).
- HOL: the flow is restarted on compact doubles of a modified metric and glued (STDS_RESTART and STDS_GLUE, src/pc_p2c_stdres.ml), so only compact existence is needed; Thm 12.29 is STDS_TM_EQ_1 (src/pc_p2c_stdc2.ml).

### MT100. Prop 12.31: three steps
- Location: Ch 12, Prop 12.31, pp. 325-326. Kind: gap.
- Issue: (a) Step 1 applies Prop 2.19 to a limit that need not be complete and has only sec >= 0; a symmetry argument (the warping function is concave with limit sqrt(2(1-t)), so the orbit areas tend to 0) shows R -> inf everywhere, which also replaces Step 2. (b) In the last paragraph the inequality is backwards, r^2 and r^-2 are swapped, and only one time is treated; integrating |dR/dt| <= C R^2 gives the contradiction at every t1 in [t0, 1), t0 = 1 - r^2/(2C), given inf R > 0 on R^3 x [0, t0]. (c) Step 2 cites Thm 11.19, which assumes compact time-slices. Typos: Q_n g(t' - t_n) should be Q_n g(Q_n^(-1) t' + t_n), and B(p0,t_n,A) should be B(p,t_n,A).
- HOL: STDS_PROP_12_31 (src/pc_p2c_stdc3.ml) needs no limit metric g(1): the warp is nondecreasing and far out close to sqrt(2(1-t)), so the tangential coefficient is at most 2(1-t)/r^2, and bounded R near a point would keep it bounded below (STDS_R_TO_INFTY); then Lemma 11.2 forward from t1 >= 1 - r^2/(32 C), and inf R > 0 on [0, t0] by continuity and positivity.

### MT101. Thm 12.32: "for any eps > 0"
- Location: Ch 12, Thm 12.32, p. 326. Kind: gap.
- Issue: The statement is for any eps > 0, but the proof covers only small eps.
- HOL: stated and proved for 0 < eps <= eps1 (STDS_P6 and STDS_PROPS, src/pc_p2c_stdc4.ml).

### MT102. Sec 13.3.2: positive curvature of the surgery cap
- Location: Ch 13, Sec 13.3.2, p. 340. Kind: gap.
- Issue: "in the preimage of the interval [4, 4 + A0 - r0] this follows from Corollary 13.12 and the fact that eta g0 has non-negative curvature": Cor 13.12 is proved only for metrics delta-close to h0 x ds^2, while on this annulus the metric is the cap of the standard initial metric and the tangential Hessian terms of f are O(1); warped-product formulas repair it, with conditions on q and c that depend on g0. The blend region s in [A0 + 4 - r0, A0 + 4 - r0/2], where the conformal factor is a blend and not e^(-2f), is not covered at all; positivity there needs r0 below the radius of the round region of g0, which the book does not require. These are the only substantive gaps in Ch 13.
- HOL: on the cap the sectional curvature of the surgery metric is given by an exact identity in terms of K_tan, K_rad of g0 and the conformal exponent, and is positive for r0 = min(1, r_round/2), q >= Q0(g0), c <= c_max(g0,q) (P3S_CAP_GS and P3S_CAP_POS, src/pc_p3_s13cap.ml); these choices are compatible with Thm 13.2 (P3_THM_13_2, src/pc_p3_s13thm.ml).

### MT103. Lemma 14.11 as used at a surgery time
- Location: Ch 14, Lemma 14.11, as used in Sec 15.4 (p. 362) and Lemma 15.11 (p. 364). Kind: gap.
- Issue: Lemma 14.11 assumes products M1 x (a,b] with a flow on all of M1, but at time T only Omega(T) exists and the earlier flow may have surgeries; a local version on a relatively compact open set containing C_T is needed.
- HOL: the lemma is stated locally, for an open set of retained points of one event (P3_LEMMA_14_11_STATEMENT; P3_LEMMA_14_11, src/pc_p3_s14glue.ml).

### MT104. Prop 15.2: beta depends on epsilon
- Location: Ch 15, Prop 15.2, pp. 353-354. Kind: gap.
- Issue: "There is 0 < beta < 1/2 such that the following holds for any epsilon < 1": the compactness proof fixes epsilon (closeness eps_n^2 in C^[1/eps_n] fails as eps_n -> 0), so it proves only beta = beta(eps). No effect: Sec 15.1.1 fixes epsilon before beta.
- HOL: stated with beta chosen after eps (P3E_PROP_15_2, src/pc_p3e_152h.ml).

### MT105. Prop 15.3: the topology of a discarded piece
- Location: Ch 15, proof of Prop 15.3, p. 357. Kind: gap.
- Issue: (a) "every point is either contained in the core of a (C,eps)-cap or is the center of an eps-neck" does not exclude C-components or eps-round components that lie only partly in D_t'. (b) "according to Proposition A.19, D_t' is an eps-tube": A.19 is applied without checking separation and gives only that D_t' lies in an eps-tube; for S^2 x I the frontier spheres must be sections, parallel in the tube. This includes a tight-shell case: Assumption (5) makes each cut sphere the central sphere of some strong delta-neck, but the disjointness of these necks comes from the construction of Sec 15.4, which the proof does not invoke, so two cut spheres may bound a thin shell inside one neck. Also the double-capped tube needs a citation (A.21 Case I), "Assumption (5)" should be (6), and "S^2 x S^1" should be an S^2-bundle over S^1.
- HOL: a component containing a small delta-neck is neither a C-component nor eps-round (APX_EXCLUDE, src/pc_apx_neck.ml); the region theorem gives the product structure of a discarded piece between its cut spheres (APX_REGION, src/pc_apx_tight.ml), with a separate tight-shell lemma for two close spheres (APX_TIGHT_SHELL, src/pc_apx_tight.ml); also the cut spheres are central spheres of K delta-necks by the backward part of strong necks (APX_STRONG_NECK_EARLIER, src/pc_apx_neck.ml).

### MT106. Prop 15.3: the frontier spheres at time t'
- Location: Ch 15, proof of Prop 15.3, p. 357. Kind: gap.
- Issue: The frontier spheres at the earlier time t' are not shown to be central spheres of eps-necks; they are central spheres of K delta-necks, with K universal, by the backward part of the strong necks.
- HOL: APX_STRONG_NECK_EARLIER (src/pc_apx_neck.ml; statement APX_STRONG_NECK_EARLIER_STATEMENT, src/pc_apx_defs.ml).

### MT107. Cor 15.4(2): from the surgery sequence to S^3
- Location: Ch 15, Cor 15.4(2), pp. 358-359. Kind: gap.
- Issue: "The last two statements are immediate from this one" leaves out van Kampen for connected sums (a free product is trivial only if every factor is), pi_1 of S^2-bundles over S^1, Killing-Hopf (a simply connected space form is S^3), X # S^3 = X (Palais-Cerf and Smale: every diffeomorphism of S^2 extends over B^3), and a precise meaning of the connected sums of Prop 15.3, including the gluing maps.
- HOL: the endgame runs by induction over the history: cut-and-cap keeps every component simply connected (RFS_CUTCAP_SC, src/pc_rfs_ccsc.ml), discarded components are of the listed types and hence S^3 (RFS_LISTED_SC_S3, src/pc_smt_listed.ml), and backward induction from the empty last stage shows that every component of every stage is S^3 (RFS_SPHERE_SYSTEM, src/pc_smt_system.ml; assembly RFS_POINCARE_SMOOTH, src/pc_rfs_assembly.ml). Smale's theorem enters through the smooth-topology layer (src/pc_smt_*.ml).

### MT108. Lemma 15.11: a uniform time T1
- Location: Ch 15, proof of Lemma 15.11, p. 364. Kind: gap.
- Issue: "Since M_t' minus psi(int C_T x {t'}) is compact for every t', there is T1 < T such that R(p(t)) > r_i^-2 for all p and all t in [T1, T)": a uniform T1 does not follow from compactness and the pointwise limits. Proof: if R(p_n(t_n)) <= r_i^-2 with t_n -> T, then |dR/dt| <= C R^2 keeps R <= 2 r_i^-2 on [t_n, T), so p_n flows into Omega_rho, which lies in int C_T, a contradiction. The same gap affects the disappearing-region clause of the surgery (R >= r^-2 on X minus Y uniformly on (t1, T)).
- HOL: the derivative bounds at canonical neighbourhoods (P2C_CANON_DERIV, src/pc_p2c_cderiv.ml) plus compactness; Lemma 15.11 is P3E_LEMMA_15_11_ROUTE (src/pc_p3e_15_11.ml).

### MT109. Prop 15.12: the extension and the Lipschitz bound
- Location: Ch 15, Prop 15.12, p. 365. Kind: gap.
- Issue: "this map extends to a map X(t') -> X(T) ... distance decreasing ... This is immediate from the third item in Theorem 13.2": the extension (identity on the continuing part, the collapse on the adjacent necks, constant beyond each neck) is well defined only because the spheres separate; and Thm 13.2(3) concerns the time-T metric, so for t < T one gets a (1 + eta)-Lipschitz map, not a distance-decreasing one.
- HOL: the pinch maps are (1 + e)-Lipschitz for t close to the event time (p4_pinch_ok, src/pc_p4_top.ml), constructed in P4_PINCH_FROM_INV (src/pc_p4_pinch.ml) from the identity on retained points, the radial collapse across each cut neck and the cap tip beyond.

### MT110. Separation of null-homotopic surgery spheres
- Location: Prop 15.12 and Remark 15.13, p. 365; pp. 428, 430; Lemma 11.30, p. 286. Kind: gap.
- Issue: That the surgery spheres separate is asserted, not argued ("since the 2-spheres along which we do surgery are homotopically trivial they separate M_t'"). A valid argument without orientability: an embedded S^2 is two-sided, and if it did not separate, a loop crossing it once would have mod-2 intersection number 1, a homotopy invariant.
- HOL: on the route every component is simply connected, and then every neck sphere separates (SMT_SC_SPHERE_SEP, src/pc_smt_sep.ml, by a lifting argument for a winding map).
- Lean: FrenzyMath records a separation repair (PoincareLib/Topology/Manifold/EmbeddedSphere/Basic.lean:40, RepairedSphereSeparationData).

### MT111. The transport of the class xi through surgery
- Location: Prop 15.12, Claim 18.22, Prop 18.18; pp. 428, 430-431, 433. Kind: gap.
- Issue: (i) a global (1 + eta)-Lipschitz bound for psi_t' is not proved; (ii) the claim that the psi_t' are homotopy equivalences (p. 428) is false for split-off homotopy-sphere pieces (MT32); (iii) "the degree-1 map constructed in Proposition 15.12" (p. 431) is never constructed; (iv) separation (MT110); (v) psi is only Lipschitz (a kink at s = A0 + 4), while Lambda M uses C^1 loops, so a smooth radial collapse is needed; (vi) the independence of psi_t'*(xi(t')) from t' is not shown. In the simply connected case (ii) is automatic.
- HOL: a smooth radial collapse (src/pc_p3_s13col.ml, src/pc_p3_s13fun.ml), the pinch maps of MT109, and degree one (ATOP_P4_SC_DEGREE_ONE, src/pc_top_p4.ml); the width argument of Colding-Minicozzi needs only these maps.
- Lean: FrenzyMath records open issues on the same transport (PoincareLib/Geometry/RicciFlow/Surgery/Ancestry/TransportTheory.lean:62, module documentation; RepairedTransportTheory at :76).

### MT112. Prop 16.1: scales other than R^(-1/2)
- Location: Ch 16, proof of Prop 16.1, pp. 367-369 and Sec 16.6. Kind: gap.
- Issue: The proof treats R(x) = r^-2 with r <= r_(i+1) at that single scale (via Prop 16.3) and r_(i+1) < r (via Prop 16.4, which needs P(x,r) with |Rm| <= r^-2 and r >= r_(i+1); Thm 8.1 then gives every scale at x). Not covered: points whose admissible scales are all < r_(i+1), and scales other than R^(-1/2) when R(x) >= r_(i+1)^-2, although Def 14.15 quantifies over every scale r <= r0.
- HOL: the small scales follow Kleiner-Lott, Sublemma 79.23 (P3N_SMALL_SCALE_STATEMENT, src/pc_p3_s16sst.ml; P3N_SMALL_SCALE, src/pc_p3_s16small.ml); the large-scale case is Sec 16.6 at a second scale (Props 16.4, 16.21); Prop 16.1 is P3L_PROP_16_1_ROUTE (src/pc_p3_s161.ml).

### MT113. Prop 16.5: persistence of the larger balls
- Location: Ch 16, proof of Prop 16.5, p. 374; Lemma 16.8 and Cor 16.9, pp. 371-373. Kind: gap.
- Issue: theta_n is chosen maximal for the persistence of the single ball B(p, t_n, A h_n), but Lemma 16.8 and Cor 16.9 assume that for every A' the ball B(p, t_n, A' h_n) persists on [t_n, t_n + h_n^2 theta_n) for n large. A later surgery could cut B(A') minus B(A) while B(A) survives, and the book never excludes this. Repair inside the proof: Claim 16.10 applied to the larger balls (beyond the neck threshold of the standard flow, a ball close to the standard solution up to an event is wholly retained or wholly discarded there), carried through the subsequence step of Lemma 16.8.
- HOL: P3N_PROP_16_5_ROUTE (src/pc_p3_s16prop5.ml).

### MT114. Def 16.20 and Prop 16.21: compactness of Y(l)
- Location: Ch 16, Def 16.20 and Prop 16.21, pp. 384-388. Kind: gap.
- Issue: "Clearly, Y(l) is a closed subset of t^(-1)([T_(i-1), T]) and hence Y(l) is a compact subset": t^(-1)([T_(i-1), T]) is not compact (the curvature blows up on the disappearing regions); Y(l) is compact because there are finitely many surgery times, the slices are compact and each slab off nu_sing is a flow image of a compact set. Also, on p. 387, Claim 16.22 controls the cap region only for times in [tbar, tbar + hbar^2/2], while nu_sing removes B_j x [tbar, tbar + h^2 Delta t_j) with Delta t_j up to theta_0; Delta t_j <= min(1/2, theta_0, (T - tbar)/h^2) in Def 16.20 repairs it.
- HOL: P3N_PROP_16_21_FIX (src/pc_p3_s1621.ml).

### MT115. Sec 16.6: Thm 4.23 for positive sectional curvature
- Location: Ch 16, Sec 16.6, p. 393. Kind: gap.
- Issue: "by Hamilton's result, Theorem 4.23, ... the component ... flows forward as a family of components of positive sectional curvature until it disappears": Thm 4.23 is about Ric. What is needed, preservation of positive sectional curvature on a compact component, already follows from the weak maximum principle (sec >= c > 0 at one time is preserved, since where the least sectional curvature equals c the reaction term is 2(c^2 + p2 p3) >= 4c^2 > 0); neither the strong principle nor the splitting of Cor 4.20 is needed. The surgeries in (t'', T] are ignored; such a closed component is never cut, but this needs an argument.
- HOL: preservation of sec >= c > 0 from the weak principle (RFA_P2_THM_4_23, src/pc_rfa_secpres.ml, with RFA_SECMIN_LOWER_PRESERVED, src/pc_rfa_tmaxp.ml); the induction of p. 393 itself is not needed, because noncollapsing is proved without the positive-curvature exemption (MT117).

### MT116. Lemma 17.2, subcase (i): closeness of the re-centred necks
- Location: Ch 17, Lemma 17.2, subcase (i), p. 397. Kind: gap.
- Issue: The book asserts that the re-centred necks at (x_n, t_n) are "clearly" within eps in C^[1/eps]; that needs eps-closeness on the whole open neck after a small backward extension, which continuity gives only on compact subsets (and nothing controls it across an event in (t' - 1/R, t']). Repair: compress the neck axially by a radial power map (closeness cost (1 - lambda^2)^2), then extend past u = -1 on the compact sub-neck and re-centre, or some point is a new cap point, which is the book's subcase (ii).
- HOL: P3_LEMMA_17_2_ROUTE (src/pc_p3_c172f.ml).

### MT117. Prop 17.1: noncollapsing without the positive-curvature exemption
- Location: Ch 17, proof of Prop 17.1, pp. 402-403; Claim 17.9, p. 406; p. 407. Kind: gap.
- Issue: "By Proposition 16.1, ... kappa-non-collapsed on scales <= eps R^(1/2)(x_a)" and "the limiting flow ... is kappa-non-collapsed on all scales ... is a kappa-solution": Prop 16.1 gives only the two-outcome notion of p. 360 and Remark 16.2 (points in a component of positive sectional curvature are exempt), while Thm 5.11, Thm 11.8 and Cor 9.95 need noncollapsing without exemption, and the exempt case is never treated.
- HOL: follows Kleiner-Lott (Def 69.1(c), Lemma 79.12): canonical neighbourhoods carry a volume clause on C-components (p3_canonv_assumption, src/pc_p3_defs.ml), and noncollapsing has no exemption (p3_noncoll_all, src/pc_p3_defs.ml), which Prop 16.1 concludes (P3L_PROP_16_1_ROUTE, src/pc_p3_s161.ml) and Prop 17.1 preserves (P3_PROP_17_1_ROUTE_2, src/pc_p3_c171e.ml).

### MT118. Claim 17.6: retained points next to a new cap
- Location: Ch 17, Claim 17.6, second case, p. 403. Kind: gap.
- Issue: "Suppose now that x~ is not an exposed point ... arguing as in the proof of Lemma 11.23 we see that x~ has a strong (2C, 2 eps)-canonical neighborhood": at a surgery time a retained point next to a new cap may have earlier neighbourhoods that meet the removed region, so the limit argument fails.
- HOL: points of the region of Thm 13.2 next to new caps are treated like exposed points, through the closeness of the cap to the standard solution, Thm 12.32 at small t > 0 and the cap transfer of Prop 9.79 (P3H_171_FRESH, src/pc_p3_c171b.ml); the worst bad point (P3H_171_WORST_BAD) supplies the canonical-neighbourhood hypotheses of Thms 10.2 and 11.8.

### MT119. Lemma 17.7: the strong neck inside the surgery neck
- Location: Ch 17, Lemma 17.7, last case, p. 406. Kind: gap.
- Issue: The strong delta-neck of the surgery is said to "contain a strong beta eps/2-neck centered at" psi(x_a, -t_a). A strong neck centred at a point x of that delta-neck needs backward time 1/R(x,T_k) = h^2 (1 + O(delta)), more than the delta-neck's h^2 when R(x) < R(y) = h^-2; the flow before the surgery need not exist or be controlled on the extra O(delta h^2) (an earlier surgery may lie there).
- HOL: the cut necks are evolving necks of rescaled backward length 2 (the invariant p3_neck2_ok, src/pc_p3_inv.ml), which Thm 11.31's own proof supplies (its limit is the round shrinking cylinder on (-inf, 0]); Lemma 17.7 is P3_LEMMA_17_7_ROUTE (src/pc_p3_c177e.ml).

### MT120. Prop 17.1: the sequence for T'
- Location: Ch 17, proof of Prop 17.1, pp. 406-408. Kind: gap.
- Issue: T' is the supremum of the rescaled times for which the backward balls persist with bounded curvature along the sequence, but the proof passes to subsequences at each such time (Thm 11.8), so the sequence for T' is not fixed; and the step past T' needs a bound R <= D Q on all A-balls of the slice at -T' with D independent of A.
- HOL: the supremum is taken over nested subsequences with a diagonal argument (P3H_SUBSEQ_SUP, src/pc_p3_c171c.ml), the uniform bound at the new time is RFA_171_UTB (src/pc_rfa_171u.ml), and T' = infinity along one subsequence is P3H_171_TINF (src/pc_p3_c171c.ml).

### MT121. Prop 17.1: the curvature bound up to -T'
- Location: Ch 17, end of the proof of Prop 17.1, p. 408. Kind: gap.
- Issue: "According to Theorem 11.8, ... this limiting flow has bounded, non-negative curvature ... Let Q be the bound for the scalar curvature of this flow": Thm 11.8 gives only curvature locally bounded in time; the step needs a bound on B(x_inf,0,A) x (-T',0] uniform up to -T', which Cor 11.16 (p. 277) provides. Typos: "If T = infinity" should be T', and P(x~_a,0,A,T) should be P(x~_a,0,A,-T).
- HOL: Cor 11.16 (P2C_COR_11_16_FLOW, src/pc_p2c_c1116u.ml) is part of the blow-up statement used here (P2C_THM_11_8_VIEW_STATEMENT, src/pc_p2c_iface.ml).

### MT122. Lemma A.4: continuity of minimal geodesics
- Location: Appendix, proof of Lemma A.4, pp. 498-499. Kind: gap.
- Issue: "minimal geodesics between a pair of points ... vary continuously in the C^1-topology as a function of the space of metrics" is false as a principle (non-uniqueness, e.g. antipodal points). A contradiction argument works: recentre at bad points, take fixed-length subarcs, and use Arzela-Ascoli and the geodesic equation to get a C^1 limit in S^2 x J that minimizes there, whose S^2-projection is too short for the angle bound to fail.
- HOL: in the neck chart a minimizer is a geodesic of the pullback metric, s'' is bounded by the C^2 closeness to the cylinder, and a window argument replaces the continuity claim (src/pc_apx_mincs.ml, constant-speed forms of A.4, A.6-A.8).

### MT123. Cor A.5 and Cor A.6: no proofs
- Location: Appendix, Cor A.5 and A.6, p. 499. Kind: gap.
- Issue: No proofs are given; A.6 is immediate from A.4, and A.5 follows from the C^0 closeness to h0 x ds^2 rather than from A.4.
- HOL: proved where used (neck distances: APX_NECK_DIST_STATEMENT, src/pc_apx_defs.ml; constant-speed forms in src/pc_apx_mincs.ml).

### MT124. Lemma A.9: the proof by continuity
- Location: Appendix, proof of Lemma A.9, pp. 501-502. Kind: gap.
- Issue: "clearly true for the product metric on an infinite cylinder, and hence by continuity" fails: z may lie outside N, M is not assumed complete (Claim 10.6 applies the lemma in an incomplete manifold), and for q near p the lower bound is a derivative estimate on a domain of size 1/eps, which C^0 closeness does not give. A repair separates z from p, q by a level sphere and estimates through it.
- HOL: the route uses only a crude form for s-differences of at least 16/alpha (APX_A9_CRUDE_STATEMENT, src/pc_apx_csreq.ml).

### MT125. Prop A.11(5), Lemma A.13, Lemma A.18: chains of necks
- Location: Appendix, Prop A.11(5) (p. 503), Lemma A.13 (p. 505), Lemma A.18. Kind: gap.
- Issue: (a) in A.11(5) the arc endpoints used for the diffeomorphism vary only semicontinuously. (b) Lemma A.13 ("by part (5) of Proposition A.11, U is the union of two manifolds each diffeomorphic to S^2 x (0,1) ... It now follows easily"): A.11(5) concerns two necks, but the overlap of the union with N_b may involve several earlier necks; it must be shown to be a connected end collar through the induction, and the proof never shows that a chain of overlapping necks has no triple overlaps. (c) Lemma A.18 invokes A.17, which needs the spheres of both N_b and N to separate M, while A.18 assumes it only for N_a.
- HOL: the corrected A.13 (APX_A13_THM, src/pc_apx_a13.ml) on the chain engine (APX_CHAIN_TUBE, src/pc_apx_engine.ml), and A.18 with separation for all its necks (APX_A18, src/pc_apx_chain.ml).

### MT126. Claim A.22: a cap inside a neck
- Location: Appendix, Claim A.22, first case, p. 510. Kind: gap.
- Issue: "the intersection of C_(i-1) and C_i would be contained in N_i. This cannot happen since C_(i-1) is contained in C_i" is not a contradiction; what is needed is that a cap cannot lie inside a neck (the core boundary of C_(i-1) is a neck sphere in N_i, essential in H_2(N_i) by A.11(4), yet bounds a compact region in N_i). Claim A.24 uses the separation of 2-spheres in R^3 or RP^3 minus a point without citation.
- HOL: the closed core of a (C,eps)-cap never lies in an eps-neck (APX_NO_CAP_IN_NECK_UNCOND, src/pc_apx_neck.ml), and Claim A.22 is APX_A22 (src/pc_apx_a22.ml).
- Lean: FrenzyMath records repairs of the cap-overlap conditions in this part of the Appendix (PoincareLib/Topology/Manifold/NeckCap.lean:56, module documentation).

### MT127. Prop A.21, Case I: the frontier sphere and Alexander's theorem
- Location: Appendix, A.21 Case I, end, p. 513. Kind: gap.
- Issue: "the frontier of C' in C~ is a two-sphere that bounds either a compact three-ball or the complement of an open three-ball in RP^3": the frontier of the open cap C' is not known to be a 2-sphere (a neck need not extend to its ends); the sphere of Claim A.24 must be used, and the gluing rests on Alexander's theorem (and its RP^3 analogue) and Smale's theorem, uncited. The case is genuine: a compact component covered by eps-necks and two caps whose cores face each other and overlap deeply satisfies all the cap clauses, and the only charts covering the ends are the core charts, so radial arguments alone do not suffice.
- HOL: the smooth Schoenflies theorem in R^3 in the collared form needed (SCH_SCHOENFLIES_REQ, src/pc_sch_main.ml, a proof of Alexander's theorem following Hatcher's notes), from which Prop A.25 follows (APX_A25, src/pc_apx_a25top.ml).

### MT128. Prop A.25: "an immediate corollary"
- Location: Appendix, Prop A.25, p. 514. Kind: gap.
- Issue: The proposition is introduced by "As an immediate corollary we have" without proof. The reduction from A.21 (X = M) is immediate, but the diffeomorphism types rest on the sketched steps of A.21 and on Alexander's theorem, Smale's theorem and the classification of free Z-quotients of S^2 x R, none cited; "(C, eps-cap" lacks a bracket. On the route only case (1) with M = S^3 occurs.
- HOL: APX_A25 (src/pc_apx_a25top.ml), on the Schoenflies theorem of MT127.

### MT129. Claim 11.35: a strict sign margin
- Location: Ch 11, Claim 11.35, pp. 289-291. Kind: unclear.
- Issue: FrenzyMath records that Claim 11.35 needs a strict positive time-derivative margin, which an absolute derivative bound alone does not give. Both margins that the book's proof uses are stated in the book and true: positivity of curvature comes from Thm 4.18 (not Cor 4.14, see the typo list), and dR/dt is controlled by C^4-closeness to the model, where (1-t)^(-2) >= 1/4. What FrenzyMath corrected cannot be decided from the public files.
- HOL: Claim 11.35 is part of the proof of Thm 11.31 (P2HN_THM_11_31_ROUTE, src/pc_p2c_horns2.ml).
- Lean: FrenzyMath, PoincareLib/Geometry/RicciFlow/Surgery/Singular/DeepHorn/Theory.lean:39 (module documentation).

## 3. Morgan-Tian: gaps in parts that the formalization does not use

Gaps in results that the formalization does not prove or use (or uses only in a weaker form), in page order; the "HOL" part says what the formalization does instead, where that is relevant.

- MT130 (gap; Ch 1, Sec 3.4, after Def 1.24, p. 15) "It follows from Corollary 1.23 that U subset T_pM is a star-shaped open neighborhood of 0": U should be U_p, and its openness does not follow from Cor 1.23; it belongs to the cut-locus theory cited for Prop 1.25. HOL: not used; ball volumes are computed over the segment domain of exp_x, whose star-shapedness is proved directly (CMPQ_SEG_STAR, src/pc_cmp_seg.ml).
- MT131 (gap; Ch 1, Sec 3.4, Def 1.26 and the next paragraph, p. 15) "Clearly, inj_M(p) is the distance in T_pM from 0 to the frontier of U_p. It is also the distance in M from p to the cut locus", and the following dichotomy (a geodesic loop or a conjugate point), need M complete and inj_M(p) finite. HOL: not used; the injectivity radius mfd_injrad (src/pc_geo_defs.ml) is a supremum of radii of injectivity balls, and the cut locus is never used.
- MT132 (gap; Ch 3, Sec 2, Claim 3.7 and Prop 3.9, p. 38) phi_t is the flow of X up to time s(t) = -log(1 - 2 lambda t)/(2 lambda) -> infinity, so X must be complete, which is never addressed; Claim 3.7 fails for incomplete M (flat open unit ball, X = x), and for Prop 3.9 completeness holds (Z.-H. Zhang, 2009) but is not argued. HOL: not used; the asymptotic soliton satisfies the shrinker equation at every time by definition (src/pc_p2b_chainstmts.ml).
- MT133 (gap; Ch 4, Sec 5.1, proof of Thm 4.35, p. 81) "according to Theorem 4.18 either all (M,g(t)) are flat or Rm(x,t) > 0": Thm 4.18 gives only R > 0; Cor 4.20 is needed, and the split case (a finite cover N x S^1 with a static circle) must be excluded; c(t) g(t) should be c(t)^(-1) g(t). HOL: not used (never cited); compact gradient shrinkers of positive curvature are round by RFA_P2B_REQ_SHRINKER_ROUND (src/pc_rfa_s2.ml).
- MT134 (gap; Ch 5, Sec 2, proof of Cor 5.16, p. 92) The flow on the incomplete V is extended "using the local existence results", but Thm 3.11 is for compact manifolds; doubling a compact domain containing V, flowing and gluing by Prop 3.12 repairs it. HOL: not used (never cited); on closed manifolds the extension criterion is PDEF_EXTENSION (src/pc_pde_final.ml).
- MT135 (gap; Ch 6, after Def 6.25, p. 117) "it is clear from the definition that U~_x is an open subset": only openness within a slice is clear. Across tau it needs Prop 6.30 (for earlier tau, proved later) and the persistence of unique minimality slightly past tau, which needs control of competitors near the edge of space-time for generalized flows. HOL: the injectivity domain is not used. It is replaced by the set of initial vectors of minimizers (p2a_Smin, src/pc_p2a_defs.ml), and Thm 8.1 is stated with an open set of end points of minimizers (P2A_THM_8_1_VIEW_STATEMENT).
- MT136 (gap; Ch 6, Cor 6.67 and Claim 6.68, pp. 139-140) The corollary needs that minimizers from x exist to every point of nu(A) and stay in a compact set (L-geodesics can run off the edge of space-time); taubar is undefined. At the use in Ch 16 (p. 394), Props 16.4 and 16.21 supply the missing hypotheses. HOL: not needed. The proof of Thm 8.1 uses no injectivity domain, Prop 6.56 or Cor 6.67 (P2AT_THM_8_1, src/pc_p2a_t81u.ml).
- MT137 (gap; Ch 6, Cor 6.79, pp. 144-145) For a flow with bounded sectional curvature the proof via Lemma 6.60 also needs a bound on |grad R| along the relevant paths and the existence of minimizers, and the bound "between sqrt(delta)|Z|^2 and 3 sqrt(delta)|Z|^2" needs additive O(delta^(3/2)) terms (it is false for Z = 0). HOL: not used. The small-time lower bound in the proof of Thm 7.26 comes from an explicit chord estimate (P2AU_CHORD_LX, src/pc_p2a_frv.ml).
- MT138 (gap; Ch 8, proof of Thm 8.10, p. 177) "according to Proposition 4.11, |Rm(p,t)| <= 2 and Vol B(p,t,r) >= kappa0 r^3" under only Vol B(p,0,1) >= omega: the volume part needs an omega-variant of Prop 4.11 (Bishop-Gromov gives kappa0(omega)). HOL: Thm 8.10 is not formalized (not on the route).
- MT139 (gap; Ch 9, proof of Prop 9.56, pp. 219-220) (a) Prop 4.22 needs a cone over a Riemannian manifold, but the Tits cone is a metric cone; missing: the cone dilations restrict to homotheties of the smooth limit, hence the cone is dr^2 + r^2 h with h smooth. (b) Thm 1.34 states only monotonicity; the rigidity case of Bishop-Gromov is needed, and the preceding display is garbled. HOL: Prop 9.56 is not used; Thm 9.59 and Lemma 9.65 follow Tao's arguments (MT71, MT72).
- MT140 (gap; Ch 12, proof of Claim 12.23, p. 315) Prop 12.7 gives no rates; part (3) needs f_r = o(1/r) and part (4) needs int_0^inf Ric(d_s,d_s) ds < inf. Both follow from concavity (sec >= 0 gives f_rr <= 0 and r f_r(r) <= 2 (f(r) - f(r/2)) -> 0). The claim is stated for fixed t but used uniformly on [t0, T]. HOL: not used. Prop 12.7 and Cor 12.8 are proved by a limit at infinity, identified with the shrinking cylinder by uniqueness (src/pc_p2c_stdasym.ml, e.g. STDS_ASYM_CLOSE).
- MT141 (gap; Ch 12, Cor 12.27, p. 322) The corollary rests on the false decay estimate (MT24), and its verification is not written; "delta-close ... as required in Proposition 12.26" refers to a hypothesis that Prop 12.26 does not have; "ghat1(t) = ghat1(t)" should read ghat2, and psi^-1 lacks subscripts. HOL: not used (see MT24).
- MT142 (gap; Ch 12, Cor 12.34, p. 327) No proof is given; it follows from Thm 12.32, but only for small eps (about eps < 0.04), not for every eps > 0. HOL: not used (never cited).
- MT143 (gap; Ch 12, Secs 12.6-12.8, pp. 300-323) The proof of Thm 12.5(1) is complete up to typos in many steps (Lemma 12.9, Cor 12.16, Claims 12.17-12.21, the derivation of (12.16), Prop 12.24, Prop 12.26 given its hypotheses, the three cases of Sec 12.8), sketched but standard in others (Lemmas 12.15, 12.18, the Schauder steps on p. 319, psi_t a diffeomorphism), and has the gaps MT97, MT140 and MT141 and the errors MT22-MT24. It is repairable; alternatives are Chen-Zhu's uniqueness theorem, Kleiner-Lott's route through compactness of standard solutions, and an energy argument. HOL: uniqueness via complete bounded-curvature flows (see MT24).
- MT144 (gap; Ch 14, Lemma 14.11, pp. 349-350) Paracompactness, required by Def 14.1, is never checked for the glued space (it is regular and second countable, hence metrizable). The Hausdorff claim of the lemma is correct. HOL: does not arise: the stages of a history are fixed manifolds and no space-time is glued (P3_LEMMA_14_11, src/pc_p3_s14glue.ml).
- MT145 (gap; Ch 18, proof of Lemma 18.5, pp. 421-422) 2V_1 + V_2 >= E + 3(1-k) is right, but "a free product decomposition of pi_1(X) with at least E + 3(1-k) non-trivial free factors" is false (RP^3 # RP^3); the correct count is >= (E + 3 - k)/2, and with Lemma 18.3 the lemma stands. HOL: not formalized (Sec 18.2 is off the route).
- MT146 (gap; Ch 18, proof of Claim 18.8, pp. 422-423) "Since Sigma is homotopically trivial, it is the boundary of a homotopy 3-ball" and the homotopy-equivalence statement after it are standard facts used without proof or reference. HOL: not formalized (off the route; in the simply connected case the facts are immediate).
- MT147 (gap; Ch 18, Lemma 18.10, pp. 424-426) "The first statement is Theorem 3.3 in [59]": [59] is about energy; the area version needs Morrey's epsilon-conformality lemma, which the conformal reparametrization of non-immersed maps also needs; s(S^2) should be s_n(S^2). HOL: not formalized (Sec 18.2 is off the route).
- MT148 (gap; Ch 18, Def 18.17, p. 430) "Notice that A(gamma) is a continuous function of gamma in Lambda M" is true but not proved (an annulus of shortest geodesics between uniformly close loops gives the bound). HOL: not needed on the Colding-Minicozzi route.
- MT149 (gap; Ch 18, proof of Claim 18.19, p. 431) The passage to every component at every time needs van Kampen at each surgery and the Kurosh theorem for free factors. HOL: not needed: only the trivial group occurs, and simple connectivity is preserved by cut-and-cap (RFS_CUTCAP_SC, src/pc_rfs_ccsc.ml).
- MT150 (gap; Appendix, proof of Lemma A.20, p. 508) The disjointness from the translates is automatic; missing are that deck transformations preserve the ends and that a lifted sphere and its translate cobound S^2 x I in S^2 x R. The two cases of the proof are swapped (see the typo list). HOL: not used (A.20 is never cited in the main text; the route is the separating case).
- MT151 (gap; Appendix, A.21 Case II, pp. 513-514; Lemma A.16, p. 506) The non-separating part ("the chain wraps around on itself like a snake eating its tail ... Clearly ...") is a sketch and uses the false general A.11(5) (MT35) exactly in the wrap-around case; Lemma A.16 ("it is an easy matter to interpolate between the projection maps") is a sketch. Typo: -(0.8) eps - 1 should be -(0.8) eps^(-1). HOL: not formalized (the route is the separating case).

## 4. Morgan-Tian: imprecisions, typos and cross-reference errors

Slips that make no numbered statement false, with the corrected reading, in page order (Chapter 19 is in Section 5). An entry may group several slips of one passage. The "HOL" part is given where the formalization states the result concerned.

- MT152 (imprecision; Ch 1, Sec 1, after Def 1.1, p. 3) "This makes M a metric space" holds only on each connected component, since the book's manifolds need not be connected, and disconnected manifolds occur after surgery. HOL: distances and balls count only joinable points (mfd_dist, mfd_ball, src/pc_grg_dist.ml); mfd_metric is the metric space of one joinability class (MFD_METRIC), and joinability classes are the connected components (MFD_JOINABLE_CONNECTED_COMPONENT, src/pc_grg_dist.ml).
- MT153 (cross-reference error; Ch 1, Thm 1.11, p. 8) Thm 1.11 is labelled "(Uniformization Theorem)"; it is the Killing-Hopf classification of complete simply connected space forms (the statement is correct). HOL: the case needed is KILLING_HOPF_S3 (src/pc_geo_kh.ml): a compact simply connected 3-manifold of constant curvature 1 is isometric to the round S^3.
- MT154 (typo; Ch 1, Def 1.14, Prop 1.15, Cor 1.16, pp. 9-10) The dimension conventions clash: Def 1.14 takes coordinates (x^1,...,x^n) on N, Prop 1.15 takes N of dimension n-1 with (x^0,...,x^n), and Cor 1.16 counts (n-1)(n-2)/2 eigenvalues; the formulas are correct with one convention. HOL: not used; Prop 4.22 is proved directly from Hess(rho^2/2) = g (RFA_P2B_REQ_CONE, src/pc_rfa_cone.ml).
- MT155 (typo; Ch 1, Prop 1.15, p. 10) The matrix of the curvature operator of the cone has its nonzero block s^2(Rm_g - wedge^2 g) printed off the diagonal (not symmetric); the block-diagonal form is meant, as Cor 1.16 uses.
- MT156 (imprecision; Ch 1, Sec 3.1, p. 10, and Sec 3.4, p. 14) The existence of minimizing curves between any two points of a complete manifold and the surjectivity of exp_p need the points in one component. HOL: MFD_COMPLETE_MINIMIZING_GEODESIC (src/pc_geo_hr.ml) assumes the points joinable, and MFD_HOPF_RINOW_POINT (src/pc_geo_hr.ml) a connected space.
- MT157 (typo; Ch 1, Def 1.30 and Thm 1.31, p. 18) (g_ij(r,theta)) <= sn_k^2(r) means sn_k^2(r) times the round metric; ct_k(r) = sn_k'(r)/(sqrt(k) sn_k(r)) is undefined for k = 0 (the bound meant is sn_k'/sn_k); theta^i should be dtheta^i. HOL: the shape-operator bound is CMPJ_SHAPE_UPPER (src/pc_cmp_jcomp.ml), with model functions defined for every real k (src/pc_cmp_defs.ml).
- MT158 (typo; Ch 2, Def 2.2, p. 22; Ch 3, before Cor 3.17, p. 43) "for all x, y in X" should be M; "F_a(t) = A_a^b F_b(t)" should be F'_a(t) = A_a^b F_b(t).
- MT159 (imprecision; Ch 2, Thm 2.4, p. 23) Toponogov's comparison assumes only "a manifold of non-negative curvature"; the section's set-up says complete, and completeness is essential (a flat cone of total angle 5 pi/2 with the apex removed contains a geodesic triangle with angle sum pi/2). HOL: CMP_R1_TOPONOGOV (src/pc_cmp_tpg.ml) assumes completeness; the incomplete case of Ch 10 is CMP_R8_LOCAL_TOPONOGOV (src/pc_cmp_ltpg.ml).
- MT160 (typo; Ch 2, proof of Lemma 2.14, p. 29) "a minimizing geodesic ray mu_- from x asymptotic at infinity to lambda_+" should end lambda_-; "B defines" should be B_+.
- MT161 (typo; Ch 3, Sec 1, p. 35) In a heuristic remark, Ric_ij = -(1/2) Delta g_ij + Q_ij gives dg/dt = Delta g - 2Q, not + 2Q.
- MT162 (typo; Ch 3, proof sketch of Thm 3.11, p. 40) "d phi_t/dt = W(t)" should be d phi_t/dt = -W(t) o phi_t, as in Chow-Lu-Ni (2.52) and in the book's own Lemma 12.15 (p. 307); the sign of W itself is right. HOL: the Ricci-DeTurck flow becomes a Ricci flow by pulling back along the flow of -W (PDE_GAUGE, src/pc_pde_gauge.ml). Lean: FrenzyMath records the same correction (PoincareLib/Geometry/RicciFlow/Local/ExistenceUniquenessContinuation.lean:70, ricciFlowLocalTheory).
- MT163 (typo; Ch 3, proof of Prop 3.19, p. 44) sum_{e,f} R_abef R_cdef = ... = 2(B_abcd - B_adbc) should end 2(B_abcd - B_abdc); as printed it fails also in dimension 3 (S^2 x R, (a,b,c,d) = (1,2,2,1)); the next page uses the correct identity. HOL: not needed (in dimension 3 the formalization uses P = (R/2) g - Ric, src/pc_rfa_pevol.ml).
- MT164 (typo; Ch 3, proof of Prop 3.21 and Cor 3.26, pp. 48-50) In (3.14), second line, "- <nabla_X nabla_Y Y, X>" should be "+" (it integrates to 0); on p. 49 the length should be int_0^d sqrt<X,X>_{g(t)} du; Cor 3.26 says [0,T) where [a,b] is meant, with K(t) continuous; "w let" should be "we let". HOL: Claim 3.24 is CMP_RICCI_INTEGRAL (src/pc_cmp_index.ml), and Cor 3.26 is P2AD_REQ_DIST_DISTORTION (src/pc_p2a_dd.ml).
- MT165 (typo; Ch 3, proof of Cor 3.25, Case (i), p. 50) "the liminf ... is at most -4(n-1) sqrt(2K/3)" should be "at least" (with r0 = sqrt(3/(2K)) the bound of Prop 3.21 equals -4(n-1) sqrt(2K/3)). HOL: P2AD_REQ_DIST_DISTORTION (src/pc_p2a_dd.ml) proves the lower bound with the sharp constant.
- MT166 (cross-reference error; Ch 3, Sec 7, pp. 51 and 53; Ch 4, proof of Prop 4.11, p. 68) The page references to Chow-Lu-Ni do not match the published book (AMS GSM 77, 2006): "Lemma 6.1 on page 207" and "Theorem 6.3 on page 208" (p. 68) are on pp. 213 and 214; "Chapter 6.2, starting on page 212" and "Theorem 6.9 on page 210" (p. 51) are pp. 218 and 216; "Lemma 6.62 on page 225" (p. 53) is the published Lemma 6.27 on p. 231. Presumably a preprint numbering. HOL: the cited results are proved (PDEF_CURVATURE_TIME and PDEF_EXTENSION, src/pc_pde_final.ml; RFA_P2_THM_3_28, src/pc_rfa_shi328.ml; RFA_P2_THM_3_29, src/pc_rfa_shi329.ml).
- MT167 (typo; Ch 3, Thm 3.28, p. 51, and Remark 3.30, p. 52) In Thm 3.28, P(x,0,r,T) should be P(p,0,r,T); Remark 3.30's "the case l = 0 of Theorem 3.29 is Shi's theorem (Theorem 3.27)" should cite Theorem 3.28. HOL: RFA_P2_THM_3_28 (src/pc_rfa_shi328.ml).
- MT168 (typo; Ch 3, proof of Thm 3.29, pp. 52-54) B(x,0,3r/4) should be B(p,0,3r/4); "C2(alpha,n) and C2'(K,alpha,r/4,n)" should be C2'(alpha,n) and C2(K,alpha,r/2,n); (F_{m-C0})^2 should be (F_m - C0)^2; and Prop 3.33 is applied at centres y although only exp_p was made a diffeomorphism (one must also pull back by exp_y). HOL: the local estimate runs in exponential coordinates at each centre (RFA_SLOC_STEP, src/pc_rfa_slloc.ml).
- MT169 (cross-reference error; Ch 4, pp. 63, 68, 72) p. 63: the tensor maximum principle "was established by Hamilton in [35]", but [35] is about four-manifolds with positive isotropic curvature (the principle is from [29], in the form of [30]); p. 68: "Equation (3.7)" should be (3.8), and "the expressions in Equation (3.19)" should be Proposition 3.19; p. 72: "by Theorem 4.17" should be Proposition 4.17.
- MT170 (typo, with a cross-reference error; Ch 4, Def 4.4 and Lemma 4.5, p. 65) T_zZ is defined as an intersection of half-spaces with z on their boundary, a cone with vertex z, but Def 4.4 tests "psi(z) in T_zZ"; z + psi(z) in T_zZ is meant (as printed Lemma 4.5 fails for Z = [1,infinity), psi = 0). "Lemma 4.1 on page 183 of [30]" cannot be right: [30] occupies pp. 153-179. HOL: not used; in dimension 3 the least sectional curvature is treated as a scalar with upper barriers (RFA_SECMIN_BARRIER, src/pc_rfa_tmaxp.ml).
- MT171 (typo; Ch 4, Def 4.10(2), p. 67, Cor 4.19, pp. 71-72; Ch 5, pp. 86, 98, 102) Def 4.10(2) quantifies "for any p in M" over the centre x; Cor 4.19 says "for some p in M" for p in U, and its proof writes T_x M and x in M for T_y U and y in U; the proof of Thm 5.6 has "if follows"; the proof of Thm 5.35 writes d_{lambda_n g_n} for d_{lambda_n g}; the proof of Prop 5.31 calls S_inf(M,p) a metric completion (harmless). HOL: Def 4.10 is rfs_normalized (src/pc_rfs_geom.ml), over every point and every r <= 1.
- MT172 (typo; Ch 4, pp. 69-72, 77; Ch 7, pp. 160-162) "convex" is written for "concave": the least eigenvalue nu_x and the sum of the two smallest eigenvalues are minima of linear functions, hence concave (Cors 4.14, 4.15, 4.19); Prop 4.17(1) requires s_x to be "a convex function" while (2) needs its superlevel set to be convex, so read literally Prop 4.17 is incoherent; in Claim 4.28, "since nu is a convex function, X is a concave function" has both words swapped (the display is right); the same slip recurs in Cor 7.19, Claim 7.20(3) and Claim 7.22. HOL: these convexity statements are not used (scalar barriers for mfd_sec_min, RFA_SECMIN_BARRIER, src/pc_rfa_tmaxp.ml; Hamilton-Ivey RFA_P2_THM_4_32, src/pc_rfa_pinch.ml). Lean: FrenzyMath records the same correction (PoincareLib/Geometry/RicciFlow/Pinching/Region.lean:49, least_eigenvalue_concave).
- MT173 (typo; Ch 4, proof of Prop 4.17, p. 71) "T(x,t) >= h(x,t)" should be s(T(x,t)) >= h(x,t).
- MT174 (cross-reference error; Ch 4, after Thm 4.23, p. 75) "Hamilton's proof in [29] uses the maximum principle and Shi's derivative estimates": [29] (1982) predates Shi (1989) and uses Hamilton's own global derivative estimates.
- MT175 (typo; Ch 5, Lemma 5.7 (p. 86), Def 5.32 (p. 99), proof of Thm 5.33 (p. 100)) The sequence index is k, but the text says "for each n", "for all n" and "as n does". HOL: Lemma 5.7 is P2C_GAUGE (src/pc_p2c_gauge.ml); Thm 5.33 is P2CP_THM_5_33 (src/pc_p2c_t533.ml).
- MT176 (typo; Ch 5, Sec 3.2, the angle at infinity, p. 96) "|ab| = |bc| = 1 and |bc| = l(gamma,mu)" should end |ac| = l(gamma,mu), so that theta_inf = 2 arcsin(l/2). HOL: not used (Thm 9.59 by Tao's argument).
- MT177 (imprecision; Ch 6, Eq. (6.6), p. 109) The L-Jacobi equation is correct only if nabla_X nabla_X Y at tau0 uses the Christoffel symbols of the fixed time tau0, a convention stated only inside the proof of Claim 6.34; read as differentiation along the flow it lacks -(dGamma/dtau)(X,Y), and Claim 6.34 loses its (nabla_X Ric)(Y,Y) term. HOL: Jacobi fields are derivatives of the L-geodesic flow in charts (src/pc_p2a_ljac.ml), so no convention is needed.
- MT178 (typo; Ch 6, Eq. (6.13), p. 126) In an intermediate line, "- d/dtau(2 sqrt(tau) Ric(Y,Y))" should be "+"; the last line and (6.11) are correct.
- MT179 (typo; Ch 6, Prop 6.56, p. 133) t^(-1)(-inf, T - tau1 + eps) should be T - tau1 - eps, as in Prop 6.59 (with "+" the eps is idle and the statement stays true).
- MT180 (typo; Ch 7, Prop 7.5(4), p. 152) U_x(tau') subset U_x(tau) should be U~_x(tau') subset U~_x(tau): the proof cites Prop 6.30, and nested spatial domains are not proved.
- MT181 (typo; Ch 8, proof of Lemma 8.9, p. 175) In the last display the second "=" should be ">=" (the square contains the disc).
- MT182 (typo; Ch 8, Thm 8.10, p. 176) "for any t0 <= T" should be t0 < T (the flow is not defined at T).
- MT183 (typo, with cross-reference errors; Ch 6-8) p. 107: the displacement, not the speed, is linear in sqrt(tau); p. 115: T_xM_{t-tau1} should be T_xM_{T-tau1}; p. 118: gamma_{Z'} should be gamma_Z; (6.21): X should be Z; p. 147: "By Theorem 6.80" should be Prop 6.81; Def 7.4: "Definition 6.26" should be 6.27; Cor 7.6: M_{T_tau} should be M_{T-tau} and "vector field" should be function; proof of Thm 7.26 (p. 165): A = M x (T - tau0, T) should be U_x cap (M x (T - tau0, T)), since Thm 6.80 needs A in U_x; p. 174: "Lemma 8.7" should be Claim 8.7, "l + x(q,tau1)" should be l_x(q,tau1), and W_sm(tau) should be W_sm(tau1).
- MT184 (typo; Ch 9, proof of Cor 9.30, p. 197) "By Corollary 9.24 each term in the sequence is non-positive" should be non-negative.
- MT185 (typo; Ch 9, Sec 9.2.6, p. 197) An overall minus sign is missing in the first display of V~(tau_1) - V~(tau_0) (harmless: the quantity is shown to vanish).
- MT186 (typo; Ch 9, set-up of Thm 9.11, pp. 183-186) The rescaling is the pure parabolic one and Claim 9.13 is right; read l_x(q_k, taubar_k) <= n/2 and l_{x_k}(q_k, 1) <= n/2, and in the proof of Cor 9.16 n/(2 tau_0^2) should be n/(2 tau^2). Lean: FrenzyMath records the same set-up (PoincareLib/Geometry/RicciFlow/AncientKappa/Rescaling/Setup.lean:40, AncientBlowupSetup).
- MT187 (cross-reference error; Ch 9) p. 220 "Corollary 9.42" should be Cor 9.54; p. 222 (footnote 3 of Thm 9.59) and p. 225 "Theorem 9.56" should be Prop 9.56; p. 242 "Corollary 9.58" should be Prop 9.58; p. 239 "Corollary 2.20" should be Lemma 2.20; p. 229 "by Lemma 9.68" should be Claim 9.68; p. 219 "Lemma 5.31" and "Theorem 5.14" should be Props 5.31 and 5.14; p. 241 "Theorem 9.42" should be Cor 9.54; p. 405 (Ch 17) "by Lemma 9.79" should be Prop 9.79; Cor 9.50(1) "Proposition 9.50" should be 9.39.
- MT188 (imprecision; Ch 9, Cors 9.94 and 9.95, p. 243) "For every 0 < eps <= eps'": eps' is never defined; it is the eps of Thm 9.93 (p. 354 says so), and "<" should be read. HOL: Cor 9.95 is stated with the constant of Thm 9.93 (P2BZ5_COR_9_95, src/pc_p2b_close95.ml).
- MT189 (typo; Ch 9, proof of Cor 9.63, p. 225) K(A) = C(nu/^n) should be C(nu/(1+A)^n).
- MT190 (typo; Ch 9, several) p. 188: in Prop 9.20, M x (-inf,0) should be M_inf x (-inf,0); p. 192: "the previous corollary" is Lemma 9.23; p. 196: Claim 9.27 means |f| <= C max(l_inf, 1); p. 187: the bounds on B(q_k,-1,A) x [-T,-tau_0] need the comparison of d_{g_k(-tau)} with d_{g_k(-1)} (Cor 9.17); p. 205: in Prop 9.39(2), R(q_i,t_i) should be R(q_i,-1); p. 222: the base points p_n and q_n are mixed up; p. 221: "rescaling by tau_k" lacks the bar.
- MT191 (typo, with cross-reference errors; Ch 10) Claim 10.4 (p. 249): R(w) < C R(z'_n) or R(w) > C^-1 R(y'_n) should have the unprimed z_n, y_n (the primes are defined later); Claim 10.5 (p. 251): 3 R(z'_n)^(-1) eps^(-1/2) should be R(z'_n)^(-1/2); Lemma 10.25 (p. 260): "proved in Lemma 10.20" should be Lemma 10.21 (its uniqueness hypothesis is unused); Lemma 10.27: d(x_i,x_j) < (delta/2) r_i should be d(x_j,x_j') < (delta/2) r; Prop 10.29: "the point p" should be the end E; p. 263: ([gamma],d_n) should be ([gamma_z],d_n).
- MT192 (imprecision; Ch 11, Thm 11.1(4) (p. 267), Thm 11.8 (p. 272), p. 288, p. 253) kappa-noncollapsing for generalized Ricci flows is used before its definition (Def 14.15, p. 351); Claim 11.5 uses exactly the pointwise meaning.
- MT193 (typo; Ch 11, proof of Thm 11.8, p. 276) "d_t(b,y)/d_t(a,y) < 4 pi eps" should read d_t(a,b)/d_t(a,y), and "contradicts d_0(x,z) = d" should be d_0(xl,z) > 3d/2. HOL: P2BU_THM_11_8_VIEW_ROUTE (src/pc_p2c_blowup3.ml).
- MT194 (typo; Ch 11) Proof of Thm 11.8 (p. 278): "kappa-non-collapsed on scales Q_n r" should be Q_n^(1/2) r; proof of Claim 11.24 (p. 282): t_n - t R(x,t_n)^(-1) and T - t should be t_n + t R(x,t_n)^(-1) and T + t; Claim 11.33 (p. 288): d(z,y) < eps^(-1) rho/2C should be eps^(-1) rho/(8C).
- MT195 (cross-reference error; Ch 11, proof of Thm 11.31, p. 289) "It now follows from Corollary 4.14 that ... the curvature of g_inf(t) on S^2 is positive" should cite Thm 4.18 (strict positivity for t in (-T, 0]; t = -T is not used).
- MT196 (typo; Ch 11, proof of Cor 11.36, p. 292) "we take the largest n such that rho >= rho_n and delta >= delta_n" should be the least n (the eligible n form a set {n >= n_0}). Lean: FrenzyMath makes the same correction (PoincareLib/Geometry/RicciFlow/Surgery/Singular/DeepHorn/Theory.lean:45, module documentation: "uses the least eligible index").
- MT197 (imprecision; Ch 12, Sec 12.2, p. 296) "Kleiner and Lott pointed out to us that this uniqueness can be easily derived from the other properties": "this uniqueness" should be "this compactness result" (the Introduction, pp. xxxvi-xxxvii, credits Kleiner with the point that only compactness is needed). The compactness result is not proved in the book, so a route that avoids uniqueness must supply it. HOL: proves uniqueness (MT24).
- MT198 (typo; Ch 12, Sec 12.3, p. 297) "The maximum principle applied to Equation (3.7), dR/dt = Delta R + |Ric|^2" should have 2 |Ric|^2 (the conclusion dRmax/dt <= Rmax^2 holds since 2 |Ric|^2 <= R^2 for sec >= 0, by Cor 4.14, cited one sentence later); "bounded by Q0 on the interval [0, max(t0, Tn))" (twice) should be min(t0, Tn).
- MT199 (typo; Ch 12) Proof of Lemma 12.2 (p. 295): "for some s0 in (1/2, 3/2)" (only (0, 3/2) follows, which is enough); proof of Lemma 12.6 (p. 298): "the smallest eigenvalue of T^2 + T^# is bounded below by 2 phi ... choosing C >= 4" should be ">= -2K phi with K = sup |Rm|, C >= 4K", and -phi(x,t1) should be -phi(x,t); (12.13) (p. 309): x^n = sin theta^1 ... sin theta^(n-1) should have the factor rhat.
- MT200 (typo; Ch 12) Lemma 12.15 (p. 307): d psi_t/dt = -ghat^(ij)(t) W(t) should be -ghat^(ij) W_j along psi_t, and Delta_{g(t),g(0)} should be Delta_{g(t),g(t0)}; (12.10) (p. 306): hhat(0) = h(0) should be ghat(t0) = g(t0); Cor 12.16 (p. 307): the target (M, g_a(0)) should be g_a(t0); proof of Lemma 12.18 (p. 310): w and r are swapped.
- MT201 (typo; Ch 12, Secs 12.7.4-12.7.5 and Prop 12.26, pp. 315-321) In (12.20) and (12.25) F(y,...,t) should be F(y,...,s); "two points in R^(n+1)" should be R^(n+2); f~ should be h~ (pp. 317, 319); "assume these estimates hold for i" should be i-1; in the "linear equation (in v)" on p. 319 the drift is nabla[(n-1) h~ - B + rho~_inf]; in Prop 12.26 the times 0 and t0 are mixed, the coefficient before the second-order term of (12.29) is 1, not 2, dOmega_b should be dOmega_(k0) in (12.30), and the boundary hypothesis must hold uniformly in t.
- MT202 (imprecision; Ch 13, p. 339) "There is a constant K' < infinity (depending on the C^[1/delta]-norm of alpha)": this is unbounded as delta -> 0; only C^2 closeness is used, so K' should depend on the C^2-norm; on s in [1,2] the eigenvalues are >= -K''(alpha) delta, so K = max(...) should be taken before C0 = 2 K e^q.
- MT203 (imprecision; Ch 13, Prop 13.14, p. 340) Conditions (1)-(2) are not scale invariant, so the proof should be run at the scale of g; the monotonicity of 2x(log x + log(1+t) - 3) that it uses is unstated but elementary; "If X_h(p) < e^3 (1+t)" should be e^3/(1+t).
- MT204 (typo; Ch 13) N^- is the image rho(S^2 x (-delta^-1, 0]), not rho((-delta^-1, 0] x S^2); beta is identically 0 on [4 + A0 - r0/2, 4 + A0], not on the empty [4 + A0 - r0/2, A0]; "[4, 4 + A0, -r0]" should be [4, 4 + A0 - r0]; "([0, delta^-1] x S^2, ...) to (B(p0, 4 + A0), eta g)" should be S^2 x [0, delta^-1) and eta g0; in Lemma 13.7(3) and Cors 13.8, 13.10 (pp. 336-338) the basis is {f1^f2, f2^f0, f0^f1} and the rotation is in span{f2^f0, f0^f1} (there is no f3); Lemma 13.4 (p. 333) says "for epsilon < 1/200", but there is no epsilon in Ch 13: the condition is delta << C0^(-1).
- MT205 (imprecision; Ch 14, Def 14.15, p. 351; p. 360; Remark 16.2) Def 14.15 has no positive-curvature exemption, while p. 360 ("for every point x not contained in a component of its time-slice with positive sectional curvature") and Ch 16 (Remark 16.2) use the two-outcome notion; Remark 14.16 speaks of "the first condition" of a one-condition definition. HOL: noncollapsing without exemption throughout (MT117).
- MT206 (typo, with cross-reference errors; Ch 15, Prop 15.3 and Cor 15.4, pp. 357-358) "By Assumption (5) every point of D_t' has a strong (C, epsilon)-canonical neighborhood" should cite (6); "Otherwise D_t' is contained in a capped or double capped epsilon-tube" should cite Prop A.21 Case I; "one of which is diffeomorphic to S^2 x S^1" should be an S^2-bundle over S^1 (possibly twisted); "a generalized Ricci flow satisfying Assumptions (1) - (7)" should be a Ricci flow with surgery.
- MT207 (typo; Ch 15, p. 360) "by Claim 15.1 there is a kappa_0 > 0 so that Vol B(x,t,r) <= kappa_0 r^3" should be ">=" (as in Claim 15.1).
- MT208 (typo; Ch 15, Def 15.7(iii), p. 360) delta0 = min(beta epsilon/3, delta0', K^-1, D^-1) versus "min(alpha epsilon/3, ...) as above" on p. 361: beta is meant (Ch 17 uses beta eps/3-necks, p. 401); K here (from Lemma 12.3) clashes with the sequence K.
- MT209 (typo; Ch 15, proof of Cor 15.10, p. 363) "defined for 0 <= t <= T2" should be T1 (Prop 4.11 and Claim 15.1 give [0, 2^-4]); a truncated flow violates Assumption (7) (maximality), so (7) should be read only for intervals ending at singular times, as Ch 17 does (p. 409). HOL: the construction starts with a history without events on [0, T_1] from a normalized metric (src/pc_p3_core.ml).
- MT210 (imprecision; Ch 11 and 15) h(rho, delta) versus h(delta, rho) (Thm 11.31, Def 15.5); the index conventions drift: r(t) = r_(i+1) on [T_i, T_(i+1)) (Def 15.7) but r_i on [T_(i-1), T_i) (Thm 15.9); Delta_i must contain delta_(i+1); the singular time lies in (T_i, T_(i+1)] (p. 361), [T_(i-1), T_i) (Lemma 15.11) or [T_i, T_(i+1)) (p. 409); a surgery at T_(i+1) uses r_(i+1) (Sec 15.4) or r_(i+2) (Cor 15.10).
- MT211 (imprecision; Ch 15, Sec 15.4, p. 361) "For each i fix a point y_i in H_i with R(y_i) = h^-2(T)": y_i must be the point given by the last statement of Thm 11.31 (its sphere cuts off an end disjoint from Omega_rho); Lemma 15.11 and Omega_rho subset C_T rely on it.
- MT212 (imprecision; Ch 15, Remark 15.13, p. 365) "we cannot extend the map even continuously over all of X(t')" is literally false (S^2 x S^1 cut along a fibre extends to S^3 through the caps); what is meant is that no extension maps X(t') minus Omega into the caps.
- MT213 (typo, with cross-reference errors; Ch 16) p. 382: "Lemma 16.13" should be Prop 16.13; p. 385: A = min(2(50 + A_0), A_0(l)) should be max; Lemma 16.19 (pp. 383-384): tau_0 and tau' should be tau_1 (Cauchy-Schwarz gives >= 100 l); Claim 16.23: J(tbar, tbar - tau_1(tbar)) should be J(tbar - tau_1(tbar), tbar); Claim 16.28 (p. 392): 2 t_0/25 should be 3 t_0/25 (the printed constant needs eps <= 1/200); p. 390: the set S should use the minimum of L_x (not l_x^min) over U_(T-tau), not M_t; A_0 is overloaded (Prop 16.13's constant should be renamed); Cor 16.24: "for any y in M_(T_(i-1))" should be any y with t(y) in [T_(i-1), t(x)) (its proof covers this); Prop 16.13(1) must allow side entry at any time in (tbar, T'] (the proof works verbatim).
- MT214 (typo; Ch 16) Claim 16.17 (p. 380): exp(2 r^-2 tau'') <= exp(2 cbrt(2)) < 2 should be exp(2 ln cbrt(2)) = 2^(2/3); Prop 16.21 (p. 385): P_0(C) uses B(p, tbar, (A + 50) hbar), which should be (A_0 + 50) hbar; Sec 16.6 (p. 394): |X_mu_z(tau)|_G(t') <= r'/Delta_1 should be sqrt(2) r'/Delta_1, "l_x is bounded by L/2" should be L_x <= L/2 (that is, l_x <= L/(4 sqrt(T - t''))), and t_(i+1) should be T_(i+1); proof of Prop 16.3 (p. 368): "Clearly, r' <= r" needs |Rm| >= R (use B(x,t,min(r,r'))).
- MT215 (typo, with cross-reference errors; Ch 17) p. 395: "the five properties given in the hypothesis of Theorem 15.9" should be the three conditions; p. 399: "delta''(A, theta_1, deltabar) ... given in Proposition 16.13" should be Prop 16.5; p. 401: the tip should be (q_(a,b), t~'_(a,b)), and "epsilon < sqrt(5D)(A_0 + 5)/2" points the wrong way (needed: eps < c/(sqrt(5D)(A_0 + 5)), which Sec 15.1.1 secures); p. 404, Claim 17.8: -t_a(2 theta_1 - 1) h_a^2 < 0 should be -t_a + (2 theta_1 - 1) h_a^2 < 0; Lemma 17.12 (p. 410): "lowers volume by at least deltabar^-1 h^2(t_0)/2" should be deltabar^-1 h^3(t_0)/2 (half a deltabar-neck of scale h has volume about 8 pi deltabar^-1 h^3; any fixed positive loss suffices), and it relies, uncited, on the monotone choice of h in Cor 11.36. Lean: FrenzyMath makes the same volume correction (PoincareLib/Geometry/RicciFlow/Surgery/Volume/LossTheory.lean:53, RepairedVolumeLossTheory).
- MT216 (typo; Ch 17, p. 409) "the surgery process at time T removes all of M_T'" should be all of M_t for t < T near T.
- MT217 (typo; Ch 18, Claim 18.13, p. 427) The area density changes by (1/2) tr(f^* dg/dt) = -tr_(TS^2) Ric, so the rate is -int_(S^2) Tr(Ric) da <= 2D Area, not "-2 int Tr ... <= 4D Area"; the stated bound e^(4D(t_1 - t_0)) remains true. Claim 18.12 and (18.1)-(18.3) are correct. Lean: FrenzyMath records a corrected factor and rank-deficient differentials (PoincareLib/Geometry/RicciFlow/Area/FixedMap/GramDerivative.lean:28, m60SphereDensity_variation).
- MT218 (typo; Ch 18, proof of Claim 18.19, p. 431) "it is true for X(T_0). But we know that pi_2(X(T_0)) = 0" should have X(T_1) (twice).
- MT219 (typo; Ch 18, Sec 18.3.2, p. 432) In w(t) = W_xi(T_1)(4t+1)^(3/4)/(4T_1+1)^(3/4) + 2 pi (4T_0+1)^(1/4)(4t+1)^(3/4) - 2 pi (4t+1), the factor (4T_0+1)^(1/4) should be (4T_1+1)^(1/4) (copied from p. 426; as printed w(T_1) != W_xi(T_1)); the conclusion is unaffected. Lean: FrenzyMath makes the same correction (PoincareLib/Geometry/RicciFlow/Extinction/Width/Profile/Data.lean:27, M68ProfileInput).
- MT220 (cross-reference error; Ch 18, pp. 435-436) "This completes the proof of Proposition 18.24 when w(t_1) >= 0" should be 18.18; "(i) w(t_1) >= 0 and w(t_1) < 0" lacks "(ii)"; "Gamma: S^2 -> X(t_0)" should be Lambda X(t_0).
- MT221 (typo; Appendix, proof of Lemma A.20, p. 508) The two cases are swapped: if the spheres do not separate, the universal cover is taken; if they separate, the previous result gives an eps-tube.
- MT222 (imprecision; Appendix, Cor A.5(1), p. 499) The distance in (1 - alpha)|s(q) - s(p)| <= d(p,q) <= (1 + alpha)|s(q) - s(p)| must be that of N (or of M when the neck spheres separate); with the distance of M and no separation the lower bound fails (round S^2 x S^1 of length 2.1/eps). Parts (2) and (3) hold for the distance of M.
- MT223 (typo, with a gap; Appendix, proof of Prop A.11, pp. 503-504) eps1(alpha1) has alpha1 undefined; "The third statement is immediate from Lemma A.4" does not cover the ends of the neck or short overlaps, but (3) follows from (2) at every point; -(0.96) eps^-1 <= s_N(x') should be s_N(y'); "though" should be "through". HOL: A.11(1) and (3) are proved for all overlapping necks (statement APX_NECK_OVERLAP_STATEMENT, src/pc_apx_defs.ml; proof in src/pc_apx_neck.ml).
- MT224 (cross-reference error; Appendix, A.21 Case I) p. 511: "by Lemma A.20 the union N_0 u ... u N_k is diffeomorphic to S^2 x (0,1)" should cite Lemma A.13; pp. 513-514: "by Lemma A.5" should be Cor A.5.
- MT225 (imprecision; Appendix, Def A.12(2), p. 505; Ch 2, Def 2.18, p. 31; Ch 9, Def 9.72 and Remark 9.73, p. 231) "the closure of its negative end meets the core of C" is impossible as written (N = C minus Ybar, Y open): the closure should meet Ybar; Remark 9.73 "r_y is bounded above by, say 2 R(x)^(-1)" has x undefined and the wrong scale (R^(-1/2)); "end" is used both for an ideal end or frontier (A.14, A.15, A.18) and for a region (A.12(2), A.21 Case II), and Def A.12(2) never defines "the negative end of N_a" as a region. HOL: chains of necks are defined with explicit quarter regions of the neck charts (src/pc_apx_defs.ml). Lean: FrenzyMath records a corrected cap definition (PoincareLib/Topology/Manifold/NeckCap.lean:44, module documentation).
- MT226 (typo; Appendix, pp. 497-513) The proofs of A.1 ("length at most 2 sqrt(2) pi (1+eps)") and A.7 ("length at most 2 pi") lack R(x)^(-1/2); in A.3 the restriction of g should be that of R(x) g; in A.10, |s(p) - s(p')| < alpha R(x)^(-1/2) eps^(-1) should be alpha eps^(-1), and "the distance from d" should be from z; in the proof of A.8, c should be the first return to S; in Claim A.22, C_(i-i) should be C_(i-1), |s_(N_i)(x')| should be s_(N'_i), S^(-1)_(N_(i-1)) should be s^(-1), and "By Lemma A.2 the ratio" should cite A.11(1); in the third subcase of A.21 the frontier of N_0 cap (M minus A) is the union of Sigma and ..., not of A (and A lies in the core of C' only if Sigma is chosen on the core side of S').

## 5. Morgan-Tian, Chapter 19 and its 2015 correction

The formalization does not formalize Chapter 19: finite extinction is proved with the width of Colding-Minicozzi (see the conventions). The notes below come from checking the chapter, the authors' 2015 correction of Section 19.2 (arXiv:1512.00699, see S9) and the two Lean proofs against each other, so they have no "HOL" part. The correction is right, and the corrected statements below follow it.

### MT227. Lemma 19.4: only in dimension 3
- Location: Ch 19, Lemma 19.4, p. 439. Kind: error.
- Issue: The lemma is stated for dim M >= 3 but holds only in dimension 3: its proof uses the identity Tr Ric^T = R/2 + K + |A|^2/2 of Lemma 19.2, which is 3-dimensional. Counterexample in dimension 4: S^2 x T^2 with g(t) = (1 - 2t) g_(S^2) + flat and a small round circle in a flat fibre. It is applied only in dimension 3 (p. 460).

### MT228. Lemma 19.7: the evolution of k^2 misses a term
- Location: Ch 19, Sec 19.2, Lemma 19.7, p. 442; proof pp. 442-443. Kind: error.
- Issue: The printed formula d/dt k^2 = (k^2)'' - 2<(nabla_X H)^perp, (nabla_S H)^perp> + 2k^4 - 2 Ric(H,H) + 4 k^2 Ric(S,S) + 2 Rm(H,S,H,S) is missing the term 2(nabla_H Ric)(S,S) - 4(nabla_S Ric)(S,H), which is linear in k: the proof commutes nabla_H and nabla_S as if the connection did not depend on t, dropping (d/dt Gamma)(S,S). The corrected identity, re-derived independently in spatial form, is Lemma 0.2 of the authors' correction (arXiv:1512.00699). The first slot should also read (nabla_S H)^perp, not (nabla_X H)^perp.
- Lean: both Lean proofs state the corrected identity: FrenzyMath PoincareLib/Geometry/CurveShortening/Evolution/CorrectedTheory.lean:26 (m62SpatialEvolutionRhs) and :153 (m62SpacetimeEvolutionRhs, Lemma 0.2 verbatim); Qin et al. DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/Evolution.lean:1188 (rfs_csf_curvature).

### MT229. (19.5) and Claim 19.8: the linear term cannot be absorbed
- Location: Ch 19, (19.5) and Claim 19.8, p. 443. Kind: error.
- Issue: (19.5) d/dt k^2 <= (k^2)'' - 2|(nabla_S H)^perp|^2 + 2k^4 + Chat k^2 and Claim 19.8 d/dt k <= k'' + k^3 + C1 k, with constants depending only on a bound for the sectional curvatures, are false: the linear term of MT228 cannot be bounded by C k^2 at small k. Corrected (correction, Cor 0.3 and (0.4)): Chat(k^2 + k), with Chat depending on bounds for Rm, Ric and nabla Ric, and d/dt h <= h'' + k^3 + C1(h + 1) for h = sqrt(k^2 + eps^2). The proof of Claim 19.8 also divides by k where k need not be differentiable; the regularization h repairs this.
- Lean: FrenzyMath, PoincareLib/Geometry/CurveShortening/Evolution/CorrectedTheory.lean:66 (M62CurveEstimates) and PoincareLib/Geometry/CurveShortening/Evolution/Flow.lean:111 (m62C0, the constant 2K0 + 6K2 + 2K2^2 + 6K1); Qin et al., DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/Basic.lean:167 (RicciBackground, C = 1 + 3B_0 + B_1 + 3B_2).

### MT230. Lemma 19.9 and Cor 19.10: the bound on total curvature
- Location: Ch 19, Lemma 19.9 (p. 444) and Cor 19.10 (p. 445), second inequalities. Kind: error.
- Issue: d/dt Theta <= C2 Theta and Theta(t'') <= Theta(t') e^(C2(t''-t')) are false: a closed geodesic (Theta = 0) generally stops being a geodesic under Ricci flow (Bahri's counterexample, arXiv:1512.02046). The length inequalities are correct. Corrected (correction, Lemma 0.4): dTheta/dt <= (C1 + C2) Theta + C1 L, hence (Theta + L)(t'') <= (Theta + L)(t') e^((C1+C2)(t''-t')): the bound on total curvature depends on the initial length too. Every use in the book is for a compact family of C^2 loops with uniform initial bounds (Lemma 19.17), so the repair is harmless.
- Lean: FrenzyMath, PoincareLib/Geometry/CurveShortening/Ramp/CurveEstimates.lean:42 (M63C2CurveEstimates); Qin et al., DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/IntegralBounds.lean:1638 (rfs_csf_integral_bounds).

### MT231. Claim 19.11: a missing sign condition
- Location: Ch 19, Claim 19.11, p. 446. Kind: error.
- Issue: du/dt = u'' + (k^2 + Ric(S,S)) u is correct (u involves no covariant derivative, so no moving-connection term), but the inequality du/dt >= u'' - C'u holds only where u >= 0. The uses (Cor 19.13, Lemma 19.14) are for ramps, u > 0, where a continuity argument makes them correct.
- Lean: FrenzyMath adds the guard 0 <= u (PoincareLib/Geometry/RicciFlow/CurveShortening/Slope/Laws.lean:28, slope_laws).

### MT232. Lemma 19.24: what the constants depend on
- Location: Ch 19, Lemma 19.24, p. 455. Kind: error.
- Issue: The constants delta and C~_i are said to depend only on t1 - t0 and a curvature bound; they must also depend on the initial bounds for total curvature and length of the family (correction, p. 9) and on bounds for derivatives of the curvature (MT229). The book is already inconsistent: its own Lemma 19.58 (p. 481) lets delta and r0 depend on Theta. The family of Lemma 19.17 has uniform bounds, so the use on pp. 455-456 stands.
- Lean: FrenzyMath, PoincareLib/Geometry/CurveShortening/Ramp/CurveEstimates.lean:165 (M63UniformDerivativeEstimates).

### MT233. Claim 19.43: false without k_geod >= 0
- Location: Ch 19, Claim 19.43 in the proof of Lemma 19.38, p. 473. Kind: error.
- Issue: dl/dt <= max_E h(psi) int k_geod ds is said to follow "immediately" from l'(t) = int k_geod h |cos theta| ds; this needs k_geod >= 0 (Gauss-Bonnet controls only the signed integral). A flat wedge with a slightly wavy base is a counterexample. Lemma 19.38 itself is true, by a different argument (polar coordinates at v, Liouville's formula, K <= 1). "t_B" should be t_xi in the last display.
- Lean: FrenzyMath records local repairs of Prop 19.35 and Lemma 19.31 (details not public) and states Prop 19.35 as M64IntrinsicAnnulusComparison (PoincareLib/Geometry/CurveShortening/Comparison/Theory.lean:35).

### MT234. Sec 19.8.1, Claims 19.59-19.62: constants and a two-sided bound
- Location: Ch 19, Sec 19.8.1, pp. 482-485. Kind: error.
- Issue: (a) the constants D0 (Claim 19.59), D1 (Claim 19.60, whose proof gives D1 = D' D0 max(D, sqrt 2)), D2, D3 (Claim 19.61) and D4 (Cor 19.62) are said to depend only on Theta or on the curvature bound; they must depend on Theta and on an initial length bound, and the constant C' of Sec 19.8.3 (Claim 19.66) on |nabla Rm|. (b) In the proof of Claim 19.61 a term int C1' phi ds must be added (from the C1 term of the corrected Claim 19.8); it is absorbed into D2. (c) Claim 19.61 asserts a two-sided bound for d/dt int phi k ds, but Claim 19.8 is one-sided and dk/dt has no lower bound in terms of k (it contains -k tau^2, tau the torsion). Only the upper bound is proved, and only it is used (Cor 19.62 integrates it).
- Lean: FrenzyMath's localized estimate is one-sided, integrated before eps -> 0, with the extra length term (blueprint PoincareConjecture/blueprint/chapters/ramps.tex:1058).

### MT235. Claim 19.1: curve shrinking in a moving Riemannian background
- Location: Ch 19, Claim 19.1, p. 437. Kind: gap.
- Issue: "For a proof of this result, see Theorem 1.13 in [2]": Altschuler-Grayson work over Euclidean space (the book says so on pp. 481 and 487). Existence, uniqueness and the blow-up alternative for C^2 immersed data in the moving metric g(t) x ds^2, and continuous dependence on the initial loop (needed for the family of p. 453), are not supplied.

### MT236. Lemmas 19.2 and 19.4: genericity, the inductive step, minimal disks
- Location: Ch 19, Lemmas 19.2 and 19.4, pp. 438-441. Kind: gap.
- Issue: (a) transversality of the double-point map ("embedded curves for all but a finite number of t") is not proved; (b) "it suffices to show that A(c(t_(i+1))) - A(c(t_i)) <= psi(t_(i+1)) - psi(t_i)" is sufficient but not what the argument proves; an induction on A(t_i) <= psi(t_i) with comparison repairs it; (c) "consider a smooth minimal disk ... It is immersed, see [37] or [27]": [27] needs real-analytic boundary and [37] is about area-minimizing currents; branch points are harmless in Gauss-Bonnet, but the branched first-variation and Gauss-Bonnet formulas are needed.

### MT237. Lemma 19.14: the computation with h/u
- Location: Ch 19, Lemma 19.14, p. 447. Kind: gap.
- Issue: The computation of d/dt(k/u) uses Claim 19.8 and must be rerun with h/u: d/dt(h/u) <= (h/u)'' + (2u'/u)(h/u)' + C'(h+1)/u, and the forcing term C1/u cannot be dropped. Since u is bounded below on finite intervals (Cor 19.13), max h/u grows at most exponentially and k stays bounded; the statement is unchanged.
- Lean: FrenzyMath's blueprint records the same ("The final forcing term cannot be dropped", blueprint PoincareConjecture/blueprint/chapters/ramps.tex:948).

### MT238. Lemma 19.15: minimal annuli
- Location: Ch 19, Lemma 19.15, pp. 447-449. Kind: gap.
- Issue: (a) existence of a minimal annulus spanning two curves in a Riemannian manifold (Douglas type) is used without reference; (b) "by shifting the boundary curves slightly within the annulus, we can assume that there are no boundary branch points": shifted curves are not flows, and the step is unnecessary; (c) in the intersecting case, "this establishes the continuity of mu(t) at t' and also ... the forward difference quotient estimate" has an order-of-limits gap: the derivative bounds for the auxiliary pairs hold at t' only and not uniformly.

### MT239. Analyticity and the minimal-surface set-up
- Location: Ch 19, p. 447; Sec 19.7, pp. 464-466. Kind: gap.
- Issue: "under the curve-shrinking flow the curves c1 and c2 immediately become analytic (see [21])": [21] (Gage-Hamilton, convex plane curves) does not apply; [40] (analyticity up to the boundary) and [71] (boundary branch points) are applied in the analytic 4-manifold M x S^1 without checking hypotheses; the passage to a smooth abstract annulus (Claims 19.33-19.34) is only sketched.

### MT240. Sec 19.5: length at the start time
- Location: Ch 19, Sec 19.5, p. 455. Kind: gap.
- Issue: The derivative bounds are claimed at times where the length is at least delta^2 B^(-1), but Lemma 19.24 needs the length bound at the start time; the length inequality of Cor 19.10 or the threshold 2 delta^2 B^(-1) repairs it.

### MT241. Claims 19.26-19.27: the error recurrence
- Location: Ch 19, Claims 19.26-19.27, pp. 457-459. Kind: gap.
- Issue: (a) the displayed recurrence in the proof of Claim 19.27 is false (counterexample with all delta_j = 0); the correct bound is f(t1) - w(t1) <= e^(C6(t1-t0))(C7 sum delta_j + k delta''), and Claim 19.27 is true. (b) Claim 19.27 needs 0 <= f(t0) <= A~ (checked at the point of use, p. 461). (c) Claim 19.26 needs |R_min| <= 2 C6, not only R_min >= -2 C6.
- Lean: FrenzyMath corrects the recurrence and the sign (PoincareLib/Geometry/CurveShortening/Deformation/GoodTimes/WeightedProfileError.lean:25, m65RestartedAreaProfile_weighted_comparison).

### MT242. Lemma 19.25: derivative inequalities from smooth convergence
- Location: Ch 19, proof of Lemma 19.25, p. 461. Kind: gap.
- Issue: Smooth convergence gives uniform convergence of the areas A_n, not the forward-difference inequalities claimed "by continuity"; Claim 19.27 needs only the integrated form, which follows from Lemma 19.4 for the limit and uniform convergence. Also B >= 3 C5 (delta')^(-1) should be 4 C5 (delta')^(-1).

### MT243. Sec 19.6: the area of the swept annulus
- Location: Ch 19, Sec 19.6, pp. 461-462. Kind: gap.
- Issue: Gamma~(c) depends on c only continuously (its polygonal vertices move continuously), so the area of the swept annulus is not controlled; a geodesic annulus between C^0-close loops, with area at most C sup d(Gamma~(c), Gamma~(c^))(L + L' + lambda), and nets chosen by C^0-closeness repair it.
- Lean: FrenzyMath's blueprint uses an explicit initial annulus joining the boundary loops (PoincareConjecture/blueprint/chapters/annular-comparison.tex:431).

### MT244. Sec 19.7: thin justifications
- Location: Ch 19, Claim 19.37 (p. 468), Claim 19.41 (pp. 471-472), Lemmas 19.46 and 19.53 (pp. 474-478). Kind: gap.
- Issue: Claim 19.37 ("a standard computation") is a Sturm comparison whose factor (1 - delta)^2 needs delta' slightly smaller than delta; the open/closed argument of Claim 19.41 is garbled but completable; the planar topology of Lemmas 19.46 and 19.53 (Schoenflies) is informal. The numbers 0.87, 0.86, 0.85 and 2 delta' < 0.2 check out.

### MT245. Sec 19.8.1: a relative length bound
- Location: Ch 19, Sec 19.8.1, p. 482. Kind: gap.
- Issue: "the length of the corresponding interval gamma'_t is at least (0.9) times the length of gamma'_t'": (19.8), k^2 <= 2/(t - t') and Claim 19.59 give only an additive loss, and a relative bound fails for very short arcs. The additive bound suffices where it is used (arcs of length >= r/2). The proof of Cor 19.63 cites a "Lemma 19.10" that does not exist.

### MT246. Secs 19.8.2 and 19.8.4: lifting to the tangent space
- Location: Ch 19, Secs 19.8.2 and 19.8.4, pp. 486, 491. Kind: gap.
- Issue: The injectivity radius of M x S^1_lambda is at most lambda/2, so the exponential map is only a local isometry on a ball independent of lambda; unique path lifting and a continuity argument that keeps the family in the ball are needed. T_(x0) M should be T_(x0) W.

### MT247. Sec 19.8.4: the same moving-connection term
- Location: Ch 19, Sec 19.8.4, p. 492; Claim 19.66(2), pp. 489-490. Kind: gap.
- Issue: The evolution of |Y|^2 is stated without derivation, and differentiating Y = nabla_Z Z/|Z|^2 - psi(Z) Z in the moving metric produces (d_t Gamma)(Z,Z) terms of size C |nabla Ric| |Y|, linear in |Y|: the same omission as in Lemma 19.7, not mentioned in the correction. The fix adds O(1 + Q) to Q_t on pp. 494-495, absorbed by enlarging C1'; Lemma 19.58 survives. On p. 494, <nabla_Z Y, Y> should be <nabla_Z Y, Z>.

### MT248. Sec 19.8.4: the barrier h
- Location: Ch 19, Sec 19.8.4, p. 495. Kind: gap.
- Issue: With g = l^2/(z^2 (l - z)^2), g_zz = (6 - 20 z(l - z)/l^2) g^2, so h = K g + ... needs K >= 6(1 - delta)^(-1); with the printed K = 4(1 - delta)^(-1) the inequality fails near z = 0 and z = l. K = 12(1 - delta)^(-1) works, with delta about 1/1200 instead of 1/400.

- MT249 (typo; Ch 19, Lemma 19.17(5), p. 450) "There is a constant C0 < infinity ... are both bounded by C3": one constant is meant (the bound comes from Claim 19.22).
- MT250 (imprecision; Ch 19, proof of Claim 19.32, p. 463) mu denotes both a constant and the minimal-annulus area function in "d mu(t)/dt = (2n-1)|Rm| mu(t) with initial condition mu(t0) <= mu".
- MT251 (typo; Ch 19, Claim 19.34, p. 466) K(h) <= C should be C''; K(h) <= C'' gives -Delta f <= 2 C'' f^2, not C'' f^2; the displayed left side is 2 K_eps, and the claimed bound 2 C'' is true.
- MT252 (typo; Ch 19, Sec 19.7.1) p. 468: "the minimum of delta and the distance along D_x" should have delta' (Claim 19.37 needs delta' < delta); p. 469: "recall that r = 1, C'' = 1" should be C'' <= 1; p. 471 (Claim 19.40): mu < 1/20 < (pi/4) - delta should be (pi/2) - delta; p. 477: "delta' < 1/20" (p. 469 fixed delta' < 1/10; any delta' < 0.4 suffices there).
- MT253 (imprecision; Ch 19, Sec 19.7.6, p. 481) "Since the length of X' is at least (0.94) l(c0)": the count on p. 480 forgets Y; with Remark 19.36 the loss is still small enough, so 0.94 is true (a cruder count gives a final ratio 0.81 > 3/4).
- MT254 (typo; Ch 19, proof of Claim 19.65, p. 489) "the Euclidean angle between (0, f_zz) and (1, f_z) is at most pi/2 - pi/5" should be "at least" (the angle is about 84 degrees).
- MT255 (typo; Ch 19, proof of Lemma 19.30, p. 462) The roles of a = A(Gamma~(c)) and a^ = A(Gamma~(c^)) are swapped (harmless: the bound holds both ways).
- MT256 (typo; Ch 19) p. 441 (proof of Lemma 19.4): A(c(t')), int_(c(x,t')) and 2 delta L_c(t) should have c^ at time t'; p. 452 (Claim 19.22): X(x) = L psi_n(x) u + (lambda/2 pi) v should be (nL/2 pi) psi_n(x) u + (lambda/2 pi) v; p. 461: W(Gamma(c)) should be A(Gamma(c)); p. 464: the net is called both X and S.

## 6. Moise

Moise's book is the source of the topological form: every compact 3-manifold has a smooth structure, through triangulations (Secs 23-35) and the PL Schoenflies theorem in R^3 (Sec 17). The formalization follows the book closely in Secs 17 and 24-35, so most notes concern proofs that it had to complete. They are in page order. The "Lean" part names the corresponding declaration of the Qin et al. proof, which also follows the book, where it treats the same passage; FrenzyMath triangulates by another route (A. J. S. Hamilton's 1976 proof), so it is not compared here.

- MO1 (gap; Sec 3, proof of Thm 3.4, Case 1, p. 28) The auxiliary vertices of Fig. 3.3 are chosen "very close" so that the figure meets Fr |K| only in v0v2; that such a choice exists needs the other polygon edges at v0 and v2 to leave at a positive angle from the free triangle, which is not argued. HOL: an explicit thin quadrilateral meets the other edges only in the shared vertices for all small widths (MOI_SA2_QUAD_CONE, MOI_SA2_EAR_REMOVE, AMB2_VERTEX, src/pc_moi_sch3_amb2.ml), giving the ambient planar Schoenflies theorem (MOI_SCD_AMB2, src/pc_moi_sch3_stmt.ml).
- MO2 (gap; Sec 17, proofs of Thms 17.2 and 17.3, p. 118) The proof of Thm 3 takes "any 2-cell of K which does not lie in D" and splits K as in the preceding proof, which needs a cell whose boundary meets Bd |K| in an arc; Thm 2's proof does not provide one, and it asserts without argument that a free cell of a piece K_i is free in K. HOL: FREE_CELL (src/pc_moi_sch3_free.ml), with MOI_SFR_BOUNDARY_CELL and MOI_SFR_FREE_LIFT (same file). Lean: Qin et al. prove Thm 2 by the book's route (DifferentialGeometry/Topology/PiecewiseLinear/FreeDiskCell.lean:127, IsPLDiskDecomposition.exists_two_free_disk_cells).
- MO3 (cross-reference error; Sec 17, Thm 17.3, p. 118) "Let K be as in Theorem 1" should cite Theorem 2 (K is a cell decomposition of a 2-cell). HOL: FREE_CELL (src/pc_moi_sch3_free.ml) is stated in the intended form.
- MO4 (gap; Sec 17, the push property, p. 118, used in Thms 17.9-17.11, pp. 121-122, and Lemma 6 of 17.12, pp. 124-125) The users need a polyhedral closed neighbourhood N of C^3 - J that misses the rest of the sphere being simplified; its existence needs that polyhedra meeting only along J meet at a positive angle, which the book never states. HOL: the property is defined in the form its users need (moi_sch3_push, src/pc_moi_sch3_stmt.ml), and the positive-angle fact is proved for the standard simplex (MOI_SPU_SEP, src/pc_moi_sch3_push.ml), used in FACE_PUSH and SIMPLEX_PUSH (same file). Lean: Qin et al. keep the book's form (DifferentialGeometry/Topology/PiecewiseLinear/PushProperty.lean:12, HasPushPropertyAt).
- MO5 (cross-reference error; Sec 17, proof of Thm 17.6, p. 120) "By Theorem 3, take a PLH f_2" should cite Theorem 4 (the push property of a 3-simplex at a 2-face). HOL: SIMPLEX_PUSH (src/pc_moi_sch3_push.ml) conjugates FACE_PUSH, as intended.
- MO6 (imprecision; Sec 17, proof of Thm 17.12, Lemma 1, p. 123) The PLH that makes D_J convex, and its extension preserving z-coordinates, must be the identity off a compact part of W cap E and supported in a thin slab about E; neither is stated, although the claim that it preserves the topology of each E' cap S depends on the second. HOL: LEVEL_CONVEXIFY (src/pc_moi_sch3_cvx.ml), used in REDUCE_FROM_COUNT (src/pc_moi_sch3_tilt.ml).
- MO7 (gap; Sec 17, proof of Thm 17.12, Lemma 1 and after Lemma 3, pp. 123-124) "By a slight alteration in the direction of the z-axis, we restore general position" and "rotate the axes slightly ... in such a way that Ind S is still = 0" presuppose that the crossing pattern at each vertex is stable under small changes of a generic direction, which is not argued. HOL: GENERIC_NEAR and CROSSINGS_STABLE (src/pc_moi_sch3_gen.ml).
- MO8 (imprecision; Sec 17, proof of Thm 17.12, Lemma 6, p. 124) From the sections E_i cap tau^3 the book concludes that |St v| cap E_i is a polyhedral 2-cell; this also needs that the section of |K| is a 2-manifold at v, otherwise the section of the star can be two disks meeting at v. HOL: MOI_SSC_STAR (src/pc_moi_sch3_slabc.ml).
- MO9 (cross-reference error; Sec 17, proof of Thm 17.12, Lemma 6, p. 125) "C^2 is free in G (Theorem 2)" should cite Theorem 3 (a free 2-cell outside a given sub-2-cell). HOL: FREE_CELL through MOI_SSL_FREE_PLANE (src/pc_moi_sch3_slab.ml).
- MO10 (gap; Sec 17, proof of Thm 17.12, Lemma 6, p. 125) "Then C^3 is convex, and is free in H" is asserted without argument: that the prism over the free 2-cell meets the rest of M_i in a 2-cell with boundary in Bd M_i is not shown. HOL: MOI_SSL_SLAB_FROM_STAR (src/pc_moi_sch3_slabb.ml), with MOI_SSB_ATTACH_IDENT, MOI_SSB_STEP and MOI_SSB_INDUCT (same file).
- MO11 (typo; Sec 17, end of the proof of Thm 17.12, p. 125) "By another n - 2 applications of Theorem 11" should be m - 3. HOL: the final gluing is an induction over the slabs (MOI_SSL_GLUE_STEP, src/pc_moi_sch3_slab.ml).
- MO12 (imprecision; Sec 24, Thm 24.7, p. 178) The theorem is stated for a connected polyhedral 3-manifold that is "not orientable", which need not be compact, while orientability is defined (p. 170) only for finite triangulated 3-manifolds; its only use (Sec 25, p. 188) is finite. HOL: not used; the loop theorem is formalized for finite orientable complexes (LOOP_THEOREM_N_STATEMENT, src/pc_moi_core_stmt.ml), and the double cover that is used comes from 24.8 with 23.19 in a Z/2 form (MOI_LTST_DOUBLE_COVER, src/pc_moi_loop_status.ml).
- MO13 (imprecision; Sec 25, Thm 25.2, p. 183; applied on pp. 193, 199, 201) The loop theorem 25.2 is stated for orientable K, although its derivation from 25.1 does not use orientability, and is then applied where orientability is unavailable or undefined (Cl(M^3 - W) on p. 193, a possibly non-orientable non-compact U on p. 199, non-compact pieces of a solid torus on p. 201); Thm 25.1 with N trivial justifies these uses. HOL: every use is for a finite complex in R^3, where the loop theorem needs no orientability hypothesis (LOOP_THEOREM_3_STATEMENT, src/pc_moi_stmt.ml; MOI_CGL_LOOP3, src/pc_moi_cglue.ml). Lean: Qin et al. prove 26.4 only in an orientable form (DifferentialGeometry/Topology/PiecewiseLinear/ExtendedLoopTheoremStatement.lean:16, Moise264Orientable).
- MO14 (gap; Sec 25, proof of Lemma 2, p. 184) "We can make slight perturbations of D, preserving the stated properties of D, so as to put |D| into general position": that local injectivity and the two-to-one property survive needs a compactness argument, not given. HOL: MOI_LGB1_STAR_STABLE and MOI_LGB1_TWO_TO_ONE (src/pc_moi_lt_gpb1a.ml), feeding GP_FROM_STEP (src/pc_moi_lt_gpb2.ml).
- MO15 (imprecision; Sec 25, proof of Lemma 2, Case 2, p. 185) After the interior of J_2 is mapped onto Delta_1 "the resulting image can be forced off a neighborhood of Delta_1"; as described J_2 itself still maps onto Gamma, so the complexity does not drop: the map must also be changed on a collar outside J_2. HOL: CLEAN_CAP (src/pc_moi_lt_cap.ml) and SWAP_FROM_CAP (src/pc_moi_lt_cuta2.ml).
- MO16 (gap; Sec 25, proof of Thm 25.1, the restricted barycentric subdivision and condition (1) of a normal system, pp. 187-188) The restricted subdivision (new vertices only off |D|) is only sketched, and the properties of the regular neighbourhood M_1 in (1) are asserted ("much the same properties as an orthodox regular neighborhood"). HOL: not used: the disk is re-simplicialized along ordinary barycentric subdivisions and the first normal system is built from the second derived neighbourhood of the image (RESIMPLICIAL and NSYS, src/pc_moi_lt_nsys.ml). Lean: Qin et al. use a retriangulated derived neighbourhood (DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/SourceNormalSystem.lean:126).
- MO17 (typo; Sec 25, proof of Thm 25.1, definition of a normal system, p. 188) "let N_1 = j*^-1(N')" should be j*^-1(N); and in condition (1), "M_2 is a 'regular neighborhood' of |D|" should be M_1 (M_2 first appears on p. 189). HOL: subgroups are replaced by maps (LOOP_NORMAL_SYSTEM_STATEMENT, src/pc_moi_core_stmt.ml).
- MO18 (gap; Sec 25, proof of Lemma 3, pp. 188-189, applying Lemmas 1-2, pp. 183-184) The lifted system is said to satisfy condition (1), which passes to the lift only if D^-1(Bd M_1) = Bd Delta, not required by (1); and Lemmas 1-2 are applied with B' = B_1, which is in general neither a regular neighbourhood of |L| nor a 2-manifold, and is never shown to be a neighbourhood of |L_3|. HOL: the descent asks for a proper disk and only a closed buffer containing the loop in its relative interior (LOOP_DESCENT_STATEMENT and LOOP_SPHERE_CASE_STATEMENT, src/pc_moi_core_stmt.ml), kept through the tower (MOI_LTD_TOWER_STEP, src/pc_moi_loop_stmt.ml; SPHERE_STEP, src/pc_moi_lt_tower.ml). Lean: Qin et al. state Lemma 2 with a buffer (DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/LemmaTwoBuffered.lean:13).
- MO19 (typo; Sec 25, proof of Lemma 3, p. 189) "(g||D|)* is surjective" and "i*((g||D|)*) is surjective" should have |D~|, the lifted image; the lift of K_1 is introduced as K'_1 but written K~_1 in the next sentence, and "B_2 forms a subcomplex of K~_2" should be K_2. HOL: the drop in complexity is proved without the group diagram (COMPLEXITY_LIFT and NO_SECTION, src/pc_moi_lt_coverb.ml).
- MO20 (gap; Sec 26, proof of Thm 26.4, Cases 1-3, p. 193) Cases 1-2 redefine D on d_1 and "force D(d_1) off of B", which destroys the general position with respect to Bd W on which the count of the polygons J_i depends; that the new map can be put back in general position with fewer polygons is not shown. Case 3 applies the loop theorem to Cl(M^3 - W) without saying that it is a triangulated 3-manifold with B as a boundary component. HOL: the singular disk is never modified: a minimal essential level circle in a bicollar and the loop theorem on one side of the cut (S26_EXT, src/pc_moi_s26_ext.ml; CUT, src/pc_moi_s26_cut.ml; MOI_CST_264, src/pc_moi_core_status.ml). Lean: Qin et al. also use a bicollar and a nontrivial level loop (DifferentialGeometry/Topology/PiecewiseLinear/ExtendedLoopTheoremOrientable.lean:20, moise264_orientable).
- MO21 (cross-reference error; Sec 26, proof of Thm 26.5, item (2), p. 194) "In the proof of Theorem 5" refers to the theorem being proved; Theorem 4 is meant. HOL: not used (26.5 is not needed).
- MO22 (gap; Sec 26, proof of Thm 26.6, p. 194) The general position conditions are numbered (1), (2), (4), (5); and (4)-(5) do not make the preimage graph a linear graph whose interior vertices lie on exactly two edges (two coplanar triangles in hexagram position meet in a hexagon): edges must also miss edges and triangles must meet transversally. HOL: the stronger condition affine_gp_3 (src/pc_moi_fnd_stmt.ml) is provided by GENERAL_POSITION_MAP_3 (src/pc_moi_fnd_gpa.ml), and 26.6 itself is proved by a parity count over a cone (SEP_266, src/pc_moi_s26_sep.ml; EVEN_CROSSING, src/pc_moi_s26_cross.ml). Lean: Qin et al. state the crossing step under an explicit transversality hypothesis (DifferentialGeometry/Topology/PiecewiseLinear/BoundaryCrossingObstruction.lean:16).
- MO23 (error; Sec 26, Thm 26.7, p. 195) The theorem assumes neither that the three surfaces are compact nor that their common boundary is nonempty, and with empty boundary it is false (three disjoint nested 2-spheres: Fr E is the outer sphere alone); the proof leaves the analysis of the three sheets to the reader. HOL: MOISE_267_STATEMENT (src/pc_moi_core_stmt.ml) adds finiteness and a nonempty common boundary, proved as THREE_267 (src/pc_moi_s26_three.ml). Lean: Qin et al. add the same two hypotheses (DifferentialGeometry/Topology/PiecewiseLinear/MoiseChain.lean:306, Moise267).
- MO24 (imprecision; Sec 26, proof of Thm 26.8, p. 195) The proof takes "another combinatorial 3-cell C_2^3" with C_1^3 cap C_2^3 = Bd C_1^3 = Bd C_2^3, which cannot exist in R^3 (it would form a 3-sphere there): it must be an abstract cell; and that S^3 - M^2 has exactly two components is left to the reader. HOL: 26.8 follows from the two sides of the surface (MOI_CST_268, src/pc_moi_core_status.ml; SURFACE_SIDES_ORIENTABLE_3, src/pc_moi_fnd_sides.ml). Lean: Qin et al. also argue by the two sides (DifferentialGeometry/Topology/PiecewiseLinear/EuclideanSurfaceOrientation.lean:82).
- MO25 (error (misprint); Sec 28, Thm 28.1 and its proof, p. 201) "Let S be a polyhedral torus in R^3. Then S is a CST" should say solid torus; and the proof's "as in Theorems 23.20 and 23.21" cites theorems that do not exist (Sec 23 ends with 23.19). HOL: solid tori are PL solid tori by definition (pl_solid_torus, src/pc_moi_core_stmt.ml); the gluing step of the proof is HANDLE_SOLID_TORUS (src/pc_moi_s30_tor_b.ml).
- MO26 (gap; Sec 28, proof of Thm 28.7, p. 204) "This follows from the preceding theorem" needs two unstated facts: the regular neighbourhood is an annulus, and its boundary curves are not ~ 0 on T. HOL: not used: 28.6, 28.8 and 28.10 are proved through PL coverings of the torus model (MOISE_286, src/pc_moi_s286.ml; MOISE_288, src/pc_moi_s288_cov.ml; MOISE_2810, src/pc_moi_s2810.ml).
- MO27 (gap; Sec 28, proof of Thm 28.10, pp. 204-205) "Therefore J u J_1 u J_2 carries a generator of H_1(S). Now apply Theorem 8": 28.8 requires every polygon to be not ~ 0, which for J is essentially the conclusion, so the step is circular as written; it is also unnecessary (J and J_1 bound an annulus, so J ~ +-J_1). HOL: MOISE_2810 (src/pc_moi_s2810.ml) does not use 28.8 (MOI_S8C_INESSENTIAL_DISK, src/pc_moi_s288_cov.ml). Lean: Qin et al. prove 28.10 in a pi_1 form (DifferentialGeometry/Topology/PiecewiseLinear/CarriesGeneratorOrIsPLCellOfDisjointCarrier.lean:13).
- MO28 (typo; Sec 28, Thm 28.19, p. 209) The hypothesis "Bd Delta = J = Delta cap J^2" should read Delta cap M^2. HOL: SPLIT_TRACE_ANNULUS (src/pc_moi_fnd_sptrace.ml).
- MO29 (error (misprint); Sec 28, definition of splitting at Delta, before 28.20, p. 209) "N(Delta) cap D_i is an annulus A_i": since Delta lies in Int D_i this set is a 2-cell; the annulus meant is N(Delta) cap Cl(D_i - Delta), as the proof of 30.3 (p. 215) states it. HOL: SPLIT_SURFACE_DISK_3 (src/pc_moi_fnd_split.ml), with the trace annulus of SPLIT_TRACE_ANNULUS.
- MO30 (gap; Sec 30, proof of Thm 30.1, pp. 214-215) The proof needs that f^-1(C) u f^-1(D) does not separate P' from Q' in the 2-cell; it proves this only when the two sets are arcs each meeting the boundary in one point, and for the general case says only "the proof is substantially the same". HOL: proved for open simply connected subsets of R^3 by unicoherence and the Phragmen-Brouwer property (MOISE_301, src/pc_moi_s30sep.ml; MOI_S30_SIMPLY_CONNECTED_UNICOHERENT), which covers every use.
- MO31 (gap; Sec 30, proof of Thm 30.3, p. 215) "Then PQ can be forced off C_1^3 into M - C" is only sketched. HOL: 30.3 in an explicit cut-and-cap form (MOISE_303_STATEMENT, src/pc_moi_core_stmt.ml; MOI_S3S5_303, src/pc_moi_s3032_stmt5.ml; CUTCAP, src/pc_moi_s30_cut_b.ml). Lean: Qin et al. use the same cut-and-cap form (DifferentialGeometry/Topology/PiecewiseLinear/MoiseChain.lean:272, Moise303).
- MO32 (gap; Sec 30, proof of Thm 30.4, p. 216) When the split surface is disconnected the bound p^1(M_2^2) <= p^1(M_1^2) - 2 is stated without argument, and the last step relies on the classification of surfaces. HOL: an extremal choice of a separating surface of largest Euler characteristic, compressed by 26.4, with Z/2 characters instead of the classification (MOI_STD_304, src/pc_moi_s3032_stmt.ml; EULER_NAT, src/pc_moi_s30_bound.ml; Z2_SC_CLOSED, src/pc_moi_s30_z2c.ml; COMPRESS and SPLIT_ESSENTIAL, src/pc_moi_s30_comp.ml). Lean: Qin et al. also use an extremal choice (DifferentialGeometry/Topology/PiecewiseLinear/SphericalShellCompression.lean:86).
- MO33 (gap; Sec 30, proof of Thm 30.5, p. 216) The four-line proof does not argue that the chosen component of R^3 - B is the bounded one, nor that C_1 lies in Int C and C in Int C_2. HOL: MOI_PROD_305_THM (src/pc_moi_p305.ml) proves 30.5 in the book's form, without a tameness hypothesis, with both steps (MOI_P35_CELL_FACTS). Lean: Qin et al. prove it only with the extra hypothesis that Bd C_2 is bicollared (DifferentialGeometry/Topology/PiecewiseLinear/TameNestedCells.lean:23, Moise305Tame).
- MO34 (gap; Sec 30, proof of Thm 30.6, pp. 216-217) Case (2) leaves to the reader that the mid-curves of the cross-caps carry a 1-cycle of order 2 and relies on the classification of surfaces; Case (1) uses "the simplest case of van Kampen's theorem", neither stated nor proved. HOL: an incompressible separating surface of largest Euler characteristic, which is a PL torus by Euler characteristic bounds and 26.8, with lifting and winding numbers instead of van Kampen (MOI_STD_306, src/pc_moi_s3032_stmt.ml; Z2_TORUS_BOUND, src/pc_moi_s30_z2c.ml; SHELL_NO_SPHERE, src/pc_moi_s30_shell.ml).
- MO35 (gap; Sec 30, proof of Thm 30.7, pp. 217-218) Case 1 needs the split torus to be connected (true, since Bd Delta is essential, but not said); Case 2 argues "exactly as in the proof of Theorem 28.1", although 28.1 starts from a solid torus, and "this is of course the bounded component" leaves S in Int S_2 unargued. HOL: MOI_STD_307 (src/pc_moi_s3032_stmt.ml), with TORUS_REGION (src/pc_moi_s30_tor_a.ml), S307_OUTSIDE and S307_INSIDE (src/pc_moi_s30_cst.ml) and HANDLE_SOLID_TORUS (src/pc_moi_s30_tor_b.ml).
- MO36 (gap; Sec 30, proof of Thm 30.8, p. 218) "Now p_J generates pi(S_2)" is stated without argument: J is a spine of S_1, and passing to S_2 needs the inclusion to induce an isomorphism, which comes from the toroidal shell Cl(S_2 - S_1). HOL: MOISE_308 (src/pc_moi_s308.ml) with MOI_S38_SHELL_LOOPS (same file). Lean: Qin et al. prove a nested form (DifferentialGeometry/Topology/PiecewiseLinear/Moise308Nested.lean:378, moise308Nested).
- MO37 (gap; Sec 31, proof of Thm 31.1, p. 221) "The theorem follows by repeated applications of Theorem 30.7", but 30.7 needs an inner solid torus with a toroidal shell, and gives nothing about the required general position of consecutive tori; both are left implicit. HOL: MOI_STD_311 (src/pc_moi_s3032_stmt.ml), with REV_SHELL (src/pc_moi_s31_rev.ml) and RECROSS (src/pc_moi_s31_cross.ml). Lean: DifferentialGeometry/Topology/PiecewiseLinear/Section31CanonicalConfiguration.lean:342 (moise311).
- MO38 (imprecision; Sec 31, canonical configurations, Fig. 31.1, p. 220, and the proof of Thm 31.4, pp. 221-222) The proof uses two properties shown only in the figure (P_j not in D_(j+1), and D_j u D_(j+1) a 2-cell); 31.4 itself holds without them. HOL: the definitions contain only the printed conditions (canonical_configuration, src/pc_moi_core_stmt.ml), and 31.4 is proved by an asymmetric argument (MOI_STD_314, src/pc_moi_s3032_stmt.ml).
- MO39 (cross-reference error; Sec 31, proof of Thm 31.4, p. 222) "by Theorem 28.9, J bounds a 2-cell ... or J carries a generator" is the content of Theorem 28.10. HOL: MOI_STD_314 uses MOISE_2810 (src/pc_moi_s2810.ml).
- MO40 (gap; Sec 32, proof of Thm 32.1, p. 224) A doubly infinite sequence of tori is chosen "as in the same definition", with all of them in general position, but 31.1 gives the tori for one triple only; each torus belongs to three triples, and a consistent choice is not argued. HOL: TOWER (src/pc_moi_s32_tower.ml) with RECROSS. Lean: DifferentialGeometry/Topology/PiecewiseLinear/CanonicalTowerExists.lean:84 (exists_canonicalTower).
- MO41 (typo; Sec 32, proof of Thm 32.1, Lemma 3, p. 225) V = UNION S''_i u {P} should have the centre P' = h(P); and in Step 2, Type 1 (p. 226), "C' and M_2 - C' are closed" should be M_3 - C'. HOL: MOI_S3I2_M1_SEP (src/pc_moi_s32_init.ml).
- MO42 (gap; Sec 32, proof of Thm 32.1, Step 4 and the final deletion, pp. 226-227) Step 4 ("The verifications are as in the preceding steps") and the final deletion of one annulus interior of each torus ("This gives a set U, with the same separation property") are asserted without argument; both remove the interior of an annulus on the barrier, which the earlier tools (30.1, 26.7) do not handle. HOL: a two-sides merge lemma (MOI_S3ST_MERGE, src/pc_moi_s32_steps.ml) in STEPS24 (same file).
- MO43 (gap; Sec 32, proof of Thm 32.1, Type 3 and Step 4, p. 227) The description of M_6 as a chain of annuli assumes that every level has at least one Type 3 component, which is not argued. HOL: MOI_S3ST_BRIDGE_EXISTS (src/pc_moi_s32_steps.ml), by 30.1.
- MO44 (gap; Sec 32, end of the proof of Thm 32.1, p. 227) U is called an open 2-cell without argument, and "it is not hard to verify, from the separation property, that Cl U = U u Bd D'" while Lemma 1 gives only one inclusion. HOL: CELL (src/pc_moi_s32_cell.ml); the separation property is needed only for Bd D' in Cl U. Lean: DifferentialGeometry/Topology/PiecewiseLinear/AnnularChainPseudoCell.lean:23 (isOpenTopologicalCell_annularChain).
- MO45 (gap; Sec 32, proof of Thm 32.3, p. 228) 32.1-32.2 are applied to two small 3-cells meeting in a disk D_e, but they are stated only for the two dual cells of an edge; the version needed is never stated ("It ought to be evident"). HOL: MOISE_322_CELLS_STATEMENT (src/pc_moi_core_stmt.ml), for any two PL 3-cells meeting in a properly embedded PL disk, proved as MOI_S3S6_322 (src/pc_moi_s3032_stmt6.ml) and used for 32.3 (MOI_S3S4_323, src/pc_moi_s3032_stmt4.ml).
- MO46 (imprecision; Sec 32, Thm 32.4, pp. 228-229) The statement says only that J bounds a 2-cell D_J in E containing P', while the proof gives D_J in N(P', delta), which the uses on pp. 233 and 238 need. HOL: MOISE_324_STATEMENT (src/pc_moi_core_stmt.ml) adds the conclusion, proved as MOI_S3S5_324 (src/pc_moi_s3032_stmt5.ml). Lean: Qin et al. state 32.4 like the book (DifferentialGeometry/Topology/PiecewiseLinear/PseudoCell.lean:422, Moise324) and derive a disk agreeing off the ball (DifferentialGeometry/Topology/PiecewiseLinear/PseudoCellDiskReplacement.lean:15).
- MO47 (gap; Sec 32, proof of Thm 32.4, p. 229) Polygons are removed "by splitting Delta u D_J apart at D_J", which needs D_J polyhedral, but the D_J are obtained only as topological 2-cells in the locally polyhedral set E - P'; that a locally polyhedral topological 2-cell is a PL 2-cell is used silently. HOL: POLY_DISK (src/pc_moi_s30_tame.ml), used in CAP_SURGERY (src/pc_moi_s32_cap_b.ml).
- MO48 (imprecision; Sec 33, Thm 33.1, pp. 230-231, as applied in Lemma 1 of 34.1, p. 240) As printed the regular neighbourhood N depends on eps, while Lemma 1 of 34.1 needs closeness of the approximation that depends on N; the proof does give the needed form (for a fixed N, f(C_v) in arbitrarily small neighbourhoods of h(C_v)). HOL: MOISE_331_STATEMENT (src/pc_moi_core_stmt.ml) in this tube form (graph_approximable, same file), derived as MOI_CST_331 (src/pc_moi_core_status.ml). Lean: Qin et al. use the same tube form (DifferentialGeometry/Topology/PiecewiseLinear/Section33TubeApproximation.lean:13, Moise331OnTube).
- MO49 (gap; Sec 33, proof of 33.1, Lemmas 3-4 (pp. 231-232), Lemma 9 (p. 234), final step (p. 238)) The disks and annuli used for splitting lie in a pseudo-cell, an open 2-cell only through a non-PL parametrization; the splitting and the PLH extensions need PL disks and annuli, and the needed recognition theorem (a polyhedral topological disk or annulus with polygonal boundary is PL) is used tacitly; the book's 2-dimensional Hauptvermutung (8.5, p. 64) covers only surfaces without boundary. HOL: DISK_RECOG and HOLED_RECOG (src/pc_moi_s33_char.ml). Lean: Qin et al. prove the disk case (DifferentialGeometry/Topology/PiecewiseLinear/PolyhedralDiskRecognition.lean:89).
- MO50 (gap; Sec 33, proof of 33.1, Lemma 5, p. 232) Adding to X all bounded components of R^3 - X keeps X in Int N' only if R^3 - N' is connected, which is true but not argued. HOL: MOI_S3FR_COMPLEMENT_CONNECTED (src/pc_moi_s33_frame.ml), by Borsuk's separation theorem, used in S33_L5 (src/pc_moi_s33_conn.ml). Lean: DifferentialGeometry/Topology/PiecewiseLinear/PolyhedralTubeHandlePieces.lean:519 (exists_hasConnectedHandlePieces).
- MO51 (gap; Sec 33, proof of 33.1, Lemma 6, p. 232) "Obviously B contains each set of the form X_v cap E_e" is not argued, and "Since Bd X is connected, it follows that A_v' is all of C_v'' cap Bd X" omits that a further component would meet no trace and so be open and closed in Bd X. HOL: S33_L6 with MOI_S3CN_CONN_ATTACH and MOI_S3CN_CONN_CLOPEN (src/pc_moi_s33_conn.ml).
- MO52 (imprecision; Sec 33, proof of 33.1, Lemma 7, pp. 232-233) "If M^2 is not connected, then M^2 - M_1^2 is a 2-sphere with at least one handle" and the bound p^1(M_1^2) <= p^1(Bd X) - 2 use the orientability of closed surfaces in R^3 and the classification, neither cited; with the Euler characteristic only "not a 2-sphere" is needed. In "Some component M_1^2 of M_2 also separates" (p. 233), M_2 should be M^2. HOL: LTD_STEP (src/pc_moi_s33_ltd7.ml), by Euler characteristic, terminating by induction (MOI_S3D_NOLTD, src/pc_moi_s33_stmt.ml).
- MO53 (error (misprint); Sec 33, proof of 33.1, Lemma 8, p. 233) The hypotheses (1) Bd Delta = Delta cap E_1 and (3) Delta meets no other set C''_v2 contradict each other, since E_1 lies in the neighbouring piece too; the intended condition, as used in Lemma 9, is that Delta misses the other pseudo-cells. HOL: S33_L8 (src/pc_moi_s33_l8.ml). Lean: Qin et al. use the same hypothesis (DifferentialGeometry/Topology/PiecewiseLinear/DiskMeetsGraph.lean:780).
- MO54 (imprecision; Sec 33, proof of 33.1, injectivity of i* (p. 234) and Lemma 10 (pp. 234-236)) Injectivity is derived from 26.4, which needs a triangulated 3-manifold with Bd X in its interior, and N' - K' is not one; the argument works in the open set Int N' - K', and the text switches between the two without noting that they have the same fundamental group. HOL: W = Int N' - K' (moi_s33_ww, src/pc_moi_s33_stmt.ml), with 26.4 for open subsets of R^3 (MOI_S3D_INJ, same file) and Lemma 10 for W (S33_SURJ, src/pc_moi_s33_l10.ml).
- MO55 (gap; Sec 33, proof of 33.1, Lemma 10, pp. 234-235) "The fact (straightforwardly demonstrable) that there is a homeomorphism phi: Bd N x (0,1) <-> Int N' - K'" is used without proof. HOL: GRAPH_TUBE_PRODUCT (src/pc_moi_fnd_tubed.ml), transported by h in TUBE_FACTS (src/pc_moi_s33_frame.ml). Lean: DifferentialGeometry/Topology/PiecewiseLinear/Section33TubeRayChart.lean:71 (IsTube.exists_rayChart).
- MO56 (typo; Sec 33, proof of 33.1, Lemma 10, pp. 235-236) X_2 = Int N' - Int X_1 should be Int N' - Int X (the printed X_2 contains K'); and on p. 236, "phi(r) is a PL closed path in Bd X ... p ~ r" should have psi(r) (psi is the square map of p. 235). HOL: MOI_S3SJ_SIDES and MOI_S3SJ_SQUARE (src/pc_moi_s33_l10.ml).
- MO57 (gap; Sec 33, proof of 33.1, Lemma 10, p. 235) "Evidently every PL closed path in Int N' - K' ... is equivalent to a finite product of PL closed paths in X_1 and PL closed paths in X_2" needs general position of the path with respect to Bd X and arcs in the connected surface Bd X joining the crossing points to P_0, neither mentioned. HOL: MOI_S3SJ_DECOMP (src/pc_moi_s33_l10.ml). Lean: DifferentialGeometry/Topology/PiecewiseLinear/SurfaceLoopDecomposition.lean:13.
- MO58 (cross-reference error; Sec 33, proof of 33.1, Lemma 11, p. 236) "Now we apply Theorem 22.9" cites the criterion by orientability and Euler characteristic, while the criterion stated with p^1 is Theorem 22.10 (harmless); the conclusion of Lemma 11 is never used (Lemma 12 needs only p^1(Bd X) = p^1(Bd N)). HOL: Lemma 11 is not formalized; the Euler characteristic of Bd X comes from the pi_1 isomorphism by counting Z/2 loop characters (MOI_S3D_CHI, src/pc_moi_s33_stmt.ml).
- MO59 (cross-reference error; Sec 33, proof of 33.1, final paragraph, p. 238) "By repeated applications of Theorem 18.2, f can be extended to all of N", but Theorem 18.2 (p. 129) concerns the Antoine construction; what is needed is 17.12 plus coning, as in the proof of 5.4 (p. 43). HOL: S33_EXT (src/pc_moi_s33_ext.ml), with MOI_SCD_COR_EXTEND_BALL (src/pc_moi_sch3_stmt.ml).
- MO60 (error (misprint); Sec 34, proof of Thm 34.1, conditions (a)-(f) of Lemma 2, p. 240) Condition (b) makes the solid torus S_1 a neighbourhood of Bd sigma and of the half-stars of the vertices of sigma, which reach the splitting disks on Bd N_sigma, so (b) cannot hold together with (f); and (d) makes Bd sigma a spine of N_sigma, while Thm 30.8 needs J to be a spine of the inner torus S_1. The evident reading is that S_1 is a thin regular neighbourhood of Bd sigma. HOL: Lemma 2 is proved without S_1, S_2 or 30.8, by a degree argument from (d) as printed (SHELL_FND, MOI_S4S_MAP_DEGREE, src/pc_moi_s34_shell.ml).
- MO61 (gap; Sec 34, proof of Thm 34.1, definition of N_sigma, p. 240; repeated in the proof of 35.2, p. 251) "Then N_sigma is a solid torus" is asserted without proof. Three 3-cells glued cyclically along disks give a solid torus or a solid Klein bottle; the second cannot occur in R^3, but the proof of 35.2 reuses the argument in an arbitrary PL 3-manifold. HOL: GRAPH_TUBE_TRIANGLE_SOLID_TORUS (src/pc_moi_fnd_tubec.ml), for complexes in R^N with no ambient orientation: a 3-simplex with face sigma gives a fixed side for every cell.
- MO62 (cross-reference error; Sec 34, proof of Lemma 4 of 34.1, p. 241) "By (4) of Lemma 1, J' carries a generator of pi(N_sigma'')": (4) of Lemma 1 says only that N_sigma'' is a neighbourhood of J'; the carrying statement is Lemma 2. HOL: LEMMA4 (src/pc_moi_s34_h1.ml).
- MO63 (gap; Sec 34, Lemma 5 of 34.1, condition (7) and the remark after it, p. 241, used on p. 245) The remark tacitly uses that h(w) lies in the unbounded component of the complement of h(Bd sigma^3 u the half-stars), a separation fact the book does not give; the use on p. 245 also needs h(w) in C_w''. HOL: MARGIN (src/pc_moi_s34_margin.ml), via the complement of a compact absolute retract. Lean: DifferentialGeometry/Topology/PiecewiseLinear/Section34ExteriorComponent.lean:705.
- MO64 (gap; Sec 34, Operation 1 and Lemma 6 of 34.1, p. 242) The check that Operation 1 preserves the conditions treats only a compressing disk inside C_sigma; if it lies outside, the new cell includes a pocket that may contain other vertex cells or most of Bd N_sigma''; condition (6) is not checked in either case. HOL: the operation is split by the side of the disk (OP1_IN, src/pc_moi_s34_op1a.ml; OP1_OUT_FROM_UNCLEAN, src/pc_moi_s34_op1b.ml; UNCLEAN, src/pc_moi_s34_op1bu.ml). Lean: Qin et al. also treat clean and unclean pockets (DifferentialGeometry/Topology/PiecewiseLinear/Section34CompressionOutsideTube.lean:159).
- MO65 (gap; Sec 34, termination count and Lemma 8 of 34.1, pp. 242-243; reused in the proof of 35.2, p. 251) Termination is argued by the total number of trace components and rim points over all of K, which is finite for 34.1 but infinite in the proof of 35.2, "virtually a repetition" of 34.1 for a possibly infinite polyhedral 3-manifold. HOL: the argument is done once in locally finite form with a rank per 2-simplex and Zorn's lemma (MOISE_34_EXT_STATEMENT, src/pc_moi_core_stmt.ml; MOI_S4D_ZORN, src/pc_moi_s34_stmt.ml). Lean: DifferentialGeometry/Topology/PiecewiseLinear/Section34TerminalFaceBalls.lean:30.
- MO66 (gap; Sec 34, proof of Lemma 11 of 34.1, Cases 1-2, p. 244) Case 1 says that a trace curve carrying a generator "crosses each set Bd D_e'' algebraically once", which presupposes meridian disks and intersection numbers that the book does not set up; in Case 2, "this easily gives a contradiction either of Lemma 9 or of Lemma 10" is not argued. HOL: a winding count instead of intersection numbers (TRACE and MOI_S4T_COMP_THREE, src/pc_moi_s34_trace.ml).
- MO67 (imprecision; Sec 34, proof of Lemma 11 of 34.1, p. 244, citing Thm 28.8, p. 204) The lemma cites 28.8 for "each such J either carries a generator ... or bounds a disk", while 28.8 assumes no J_i ~ 0 and concludes only that each carries a generator; the form used also needs 28.9 and 28.6. HOL: MOISE_288_STATEMENT (src/pc_moi_core_stmt.ml) in the used form, proved as MOISE_288 (src/pc_moi_s288_cov.ml).
- MO68 (gap; Sec 34, construction of f in stages (1)-(7), pp. 245-246) No stage extends f over the splitting disks D_e, which lie in Bd C_v, before "f is defined on the boundary of each set C_v"; and at boundary vertices of K the parts of Bd N outside K get no targets, although f is built on K u N. HOL: the cell diagram lists every cell kind, including the splitting disks and the outer patches and arcs (src/pc_moi_s34_stmt.ml; OUTER_CELLS, src/pc_moi_s34_outer.ml), and EXT (src/pc_moi_s34_ext.ml) builds f cell by cell.
- MO69 (imprecision; Sec 35, proof of Thm 35.1, condition (1), p. 248, and the last sentence, p. 251) Condition (1) puts h(C_v) and f(C_v) in a 3-cell E_v in N(h(v), e(C_v)), which gives only d(f(P), h(P)) < 2 e(C_v) <= 2 phi(P), not "f is a phi-approximation of h" (harmless: use radius e(C_v)/2). HOL: 35.1 is stated in tube form (MOISE_351_STATEMENT, src/pc_moi_core_stmt.ml), so no radius occurs.
- MO70 (imprecision; Sec 35, proof of Thm 35.1, Fig. 35.1(b), p. 248) The altered cell is described only by the figure; building it needs a collar neighbourhood of the whole splitting disk, which the book does not mention. HOL: a PL chart from a model double cube onto the two dual cells of each edge (CHARTS, src/pc_moi_s35_charts.ml), with the altered cell and tubes as fixed model polyhedra (src/pc_moi_s35_stmt.ml).
- MO71 (imprecision; Sec 35, proof of Thm 35.1, definition of C_v'' and condition (2), p. 249) "Adding each set S_e to the corresponding set C_v'" must mean the unaltered cell, and condition (2) asks E_v to contain f_w(S_e) for e = vw, defined only when w is the unaltered side, so v and w are swapped relative to the figure. HOL: each edge has a fixed unaltered side and altered side (moi_s35_csrc and moi_s35_cplus, src/pc_moi_s35_stmt.ml).
- MO72 (typo; Sec 35, proof of Thm 35.1, condition (6), p. 249) "no set S_e' intersects K" should be h(K). HOL: the corresponding clause of moi_s35_frame (src/pc_moi_s35_stmt.ml), established in APPROX (src/pc_moi_s35_approx.ml).
- MO73 (gap; Sec 35, proof of Thm 35.1, condition (8), p. 250) "As usual, we may assume (8) A_e' and B_e' are in general position" cites no general position statement that keeps (2)-(7). HOL: no general position lemma is used: the cell is cut at a height chosen after the approximations (MOI_S5A_CC_CHOICE, src/pc_moi_s35_approx.ml).
- MO74 (gap; Sec 35, proof of Thm 35.1, choice of the numbers e_v, p. 250) "The numbers e_v can be chosen for all of K" needs, for infinite K, a positive separation between the images of disjoint pieces of different vertices and a minimum over the edges at v; neither is argued. HOL: MOI_S5A_PIECES_SEP, MOI_S5A_GLOBAL_SEP and MOI_S5A_ERR_CHOICE (src/pc_moi_s35_approx.ml).
- MO75 (gap; Sec 35, proof of Thm 35.1, the Minimality condition, p. 250, used in Lemmas 2-3) The sets are chosen to minimize the total number of components of all sets A_e' cap B_e', which is infinite for infinite K; the minimization has to be done edge by edge. HOL: MOI_S5D_REMOVAL_CORE (src/pc_moi_s35_stmt.ml), an induction per edge with compact supports, applied at all edges by COMBINE (src/pc_moi_s35_comb.ml). Lean: DifferentialGeometry/Topology/PiecewiseLinear/Section34ConfinedTubeCircleRemoval.lean:454.
- MO76 (gap; Sec 35, proof of Lemma 2 of 35.1, pp. 250-251) "Move the resulting annulus slightly off of A_e' by a PLH" and "(8) is trivial" are not justified, and "It follows that (2)-(6) are preserved" hides why (4) survives (the inserted or deleted 3-cell contains no boundary curve of A_e'). HOL: DISK_SWAP (src/pc_moi_s35_minb.ml), with the slab lemma SLAB_PRODUCT (src/pc_moi_s35_slab.ml).
- MO77 (gap; Sec 35, proof of Thm 35.1, final paragraph, p. 251) "Now let f be a PLH Bd N <-> Bd UNION D_v such that f(Bd(C_v cap C_w)) = Bd(D_v cap D_w)" exists only if the gluings agree in orientation along every cycle of K, which has to come from the closeness of the f_v to h and is not argued. HOL: an injective continuous map of a connected open set of R^3 has one determinant sign, and close maps have the same sign (LOCAL_SIGN and CLOSE_SIGN, src/pc_moi_s35_deg.ml), recorded for the charts of each edge (moi_s35_same_orient, src/pc_moi_s35_stmt.ml) and used in TWO_DISK_EXT (src/pc_moi_s35_ext2.ml). Lean: DifferentialGeometry/Topology/PiecewiseLinear/Section34PositiveReferenceMaps.lean:40.

## 7. Other sources

Sources other than Morgan-Tian and Moise in which the formalization found something, by source; the last two notes concern the 2015 correction of Section 19.2 of Morgan-Tian and a note disputing it. Pages of arXiv versions are pages of the arXiv PDF named.

### S1. Chow-Lu-Ni, Thm 6.3: smoothness at the final time of an extended flow
- Location: B. Chow, P. Lu, L. Ni, Hamilton's Ricci Flow (AMS GSM 77, 2006), Ch 6, Sec 1, end of the proof of Thm 6.3 (long-time existence), p. 218. Kind: gap.
- Issue: After g(t) -> g(T) in every C^k norm, the proof concludes "using the short time existence theorem, we can extend the solution g(t) to the time interval 0 <= t < T + eps"; that the concatenated family is smooth in t at t = T is not argued. Morgan-Tian cite this theorem for their extension criterion (Prop 4.12).
- HOL: the extension criterion (PDEF_EXTENSION, src/pc_pde_final.ml, via PDE_EXTENSION_FROM, src/pc_rf_extend.ml) needs no gluing at the final time: the flow is restarted at a time before b that lies within the uniform existence time, and the two flows agree by uniqueness. Gluing in time is proved separately (PDE_GLUE, src/pc_rf_glue.ml).

### S2. Chow-Lu-Ni, (10.56): a power of t
- Location: Chow-Lu-Ni, Ch 10, Sec 5, Lemma 10.41, (10.56), p. 411. Kind: typo.
- Issue: In the evolution of the Harnack tensor M_ab, whose definition contains R_ab/(2t), (10.56) ends with -(1/(2t)) R_ab; it should be -(1/(2t^2)) R_ab, the time derivative of the coefficient 1/(2t) (the printed term does not scale like the others).
- HOL: the heat defect of the Harnack tensor with time origin s has the coefficient -1/(2(t - s)^2) (RFA_HEAT_HM3 and RFA_ORIGIN_COEFF, src/pc_rfa_htens.ml), on which the Harnack algebra (RFA_HARNACK_ALG, src/pc_rfa_halg.ml) and the trace Harnack inequality (RFA_P2B_REQ_RFA_HARNACK, src/pc_rfa_htrace.ml) build.

### S3. Colding-Minicozzi, Lemma 3.11: a circle on S^2
- Location: T. Colding and W. Minicozzi, Width and finite extinction time of Ricci flow (Geom. Topol. 12, 2008), Sec 3.3, proof of Lemma 3.11: step (3.24) in the proof of (3.12), and the same step for (3.31) in the proof of (3.13); arXiv:0707.0108v1, pp. 13-16. Kind: gap.
- Issue: For a ball B_R of B_{2,-} and a circle dB_r with R/2 < r <= R, the proof asserts that the circle "is not contained in any of the balls in B_1", so that u = H(u,B_1) somewhere on it. On S^2 a closed cap that contains the circle contains either B_r (excluded by B_{2,-}) or the whole outside of B_r; the planar picture covers only the first case. In the second case the slice has energy at most about 2 eps1/3, but Thm 2.1 fixes eps0 and Psi before the width W, so its conclusion is claimed for slices of arbitrarily small energy, where the argument gives nothing.
- HOL: Thm 2.1 is proved in the paper's order of quantifiers (CM_TIGHTEN_STATEMENT, src/pc_cm_stmts.ml; CMR_TIGHTEN_FROM_CHAIN, src/pc_cm_replacement.ml). Lemma 3.11 is proved under the hypothesis that the energy exceeds twice the family bound, which excludes the bad configuration (CMR_L312 and CMR_L313, src/pc_cmr_l312.ml; CMR_CIRCLE_MEETS_OFF, src/pc_cmr_l311.ml), and slices of low energy are first deformed to constant maps by an energy-nonincreasing homotopy of the sweepout (CMR_LOW, src/pc_cmr_low.ml), which by the energy gap for harmonic spheres (CM_SPHERE_GAP, src/pc_hm_reg_sph.ml) creates no harmonic slices (CMR_LOW_POS, src/pc_cm_replacement.ml).

### S4. Colding-Minicozzi, Thm 1.7: slices of small area
- Location: Colding-Minicozzi 2008, Sec 1.5, proof of Thm 1.7, last paragraph (slices with area at most W(g) - delta); arXiv:0707.0108v1, p. 8. Kind: imprecision.
- Issue: For these slices the proof says only that "the continuity of g(t) implies that (1.25) automatically holds after possibly shrinking h". The constant must not depend on the sweepout or the slice, so what is needed is a bound on the change of area that is uniform over all maps, such as Area_{g(tau+h)}(f) <= (1 + C h) Area_{g(tau)}(f) from a Ricci bound; this holds on a closed manifold but is not stated.
- HOL: one constant for all sweepouts, slices and times of a compact interval (P4_AREA_TAYLOR, src/pc_p4_width.ml), applied to the small slices in the proof of (1.8) (P4_SLICE_B and P4_CM_DINI_FROM_C1, src/pc_p4_cm.ml).

### S5. Kleiner-Lott, Prop 39.1: "elliptic theory gives smoothness"
- Location: B. Kleiner and J. Lott, Notes on Perelman's papers (arXiv:math/0605667v5; Geom. Topol. 12, 2008), proof of Prop 39.1, after (39.7), p. 69. Kind: gap.
- Issue: As in Morgan-Tian's Prop 9.20 (MT63), "writing (24.8) as (39.7), elliptic theory gives smoothness of l": elliptic regularity on each time slice gives smoothness in space only, while the next step (Prop 29.5) differentiates in time. Needed: interior regularity of locally Lipschitz weak solutions of the conjugate heat equation for tau^(-n/2) e^(-l).
- HOL: WAN_CONJ_HEAT_REG (src/pc_wan_preg.ml).

### S6. Kotschwar, Lemma 6: the initial value of A
- Location: B. Kotschwar, An energy approach to the problem of uniqueness for the Ricci flow (Comm. Anal. Geom. 22, 2014), Sec 2.1, proof of Lemma 6; arXiv:1206.3225v1, p. 6. Kind: imprecision.
- Issue: The proof shows |A(p,t) - A(p,eps)| <= N (sqrt t - sqrt eps) for 0 < eps < t, where A is the difference of the connections, and ends "sending eps -> 0 completes the proof". This uses A(p,eps) -> 0, that is that both solutions are smooth up to t = 0, where they agree; the theorem does not state it.
- HOL: the analogue integrates the Christoffel differences in time and assumes explicitly that the density tends to 0 at the initial time (RFU_LOCAL_DENS_BOUND, src/pc_rf_unique_a14.ml), which right-continuity at the initial time supplies (RFU_DENS_UNIFORM, RFU_SFUN_TIME_CONT, src/pc_rf_unique_a14.ml).

### S7. Sacks-Uhlenbeck, Thm 3.6: removing the singularity
- Location: J. Sacks and K. Uhlenbeck, The existence of minimal immersions of 2-spheres (Ann. of Math. 113, 1981), Sec 3, Thm 3.6, last sentence of the proof, p. 15. Kind: imprecision.
- Issue: "This now implies s in L_1^(2 alpha)(D, N) for alpha > 1, and the proof of (2.3) applied to equation (1) gives regularity": the argument of Prop 2.3 needs the equation weakly on the whole disc, but s is known to solve it only on the punctured disc; that it extends across the puncture (a point has zero capacity in dimension 2) is not mentioned.
- HOL: the Euler-Lagrange identity is extended across the point by cutoffs (HMRR_EL_ACROSS, src/pc_hm_reg_rem.ml), with W^{1,2} across it (WAN_REMOVABLE_POINT, src/pc_wan_sob2.ml), before the regularity of weakly harmonic maps is applied (CM_REG01, src/pc_hm_reg_smth.ml); the theorem is CM_REMOVABLE (src/pc_hm_reg_rem.ml).

### S8. Tao, Sec 3.18: shifted cross-references
- Location: T. Tao, Poincare's Legacies, Part II (AMS, 2009), Ch 3, Sec 3.18, pp. 588-589 (Cor 3.18.4, Remark 3.18.5, Cor 3.18.6, Prop 3.18.7); the same shift occurs elsewhere in Secs 3.14-3.19. Kind: cross-reference error.
- Issue: Results are cited with section numbers one too small: "Proposition 3.17.3" means Prop 3.18.3, "Corollary 3.17.6" (three times) Cor 3.18.6, "Proposition 3.17.7" and "Corollary 3.17.4" Prop 3.18.7 and Cor 3.18.4, "Theorem 3.15.8" Thm 3.16.8, "Exercise 3.16.1" Exercise 3.17.1, "Exercise 3.13.7" Exercise 3.14.7, "Section 3.16" Section 3.17, and in Sec 3.19 "Theorem 3.18.7" Thm 3.19.7. In the proof of Prop 3.18.7, y_n should lie in B(x_n, A R_n(x_n)^(-1/2)), and "B(x_inf,1) = omega_3/2" omits Vol.
- HOL: not affected; the formal proofs follow Prop 3.18.3 (P2AV9_THM_9_59_ROUTE, src/pc_p2a_asv.ml) and Prop 3.18.7 with Cor 3.18.6 (P2AL65_LEMMA_9_65_ROUTE, src/pc_p2a_l965.ml).

### S9. Morgan-Tian, Correction to Section 19.2 (arXiv:1512.00699): small slips
- Location: arXiv:1512.00699v1 (9 pp.): proof of Lemma 0.1 (p. 3), Lemma 0.2 (p. 4), the last display of p. 6, Lemma 0.4 and its proof (pp. 7-8). Kind: gap.
- Issue: The correction is right: its key identity (Lemma 0.2) agrees with an independent derivation of the evolution of k^2 in spatial form, and the chain (0.4), Lemma 0.4, corrected Cor 19.10, Lemma 19.14, Lemma 19.24 and Sec 19.8 checks line by line. Slips: the proof of Lemma 0.4 passes "d/dt Theta_eps <= ..." to the limit eps -> 0 as a differential inequality, although Theta need not be differentiable; integrating first and then using 0 <= Theta_eps - Theta <= eps L repairs it. In Lemma 0.2, "perp" must mean the orthogonal complement for ghat = g(t) + dt^2 (read in g(t) the formula is off by 2 Ric(S,H)^2, which is O(k^2) and does not affect Cor 0.3). The last line of the proof of Lemma 0.1 should end -2k^2 |X|^2, not -2k^2 |H|^2, and the last display of p. 6 lacks a bracket. None affects the conclusions.
- HOL: not formalized (finite extinction is proved by the width of Colding-Minicozzi).
- Lean: both Lean proofs integrate before taking the limit: FrenzyMath, PoincareLib/Geometry/RicciFlow/CurveShortening/Integral/TotalCurvature.lean:28 (total_curvature_integral_of_regularized_bound); Qin et al., DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/IntegralBounds.lean:1638 (rfs_csf_integral_bounds).

### S10. Bahri, "C_1 in [2] is zero" (arXiv:1512.02098): the claim is false
- Location: arXiv:1512.02098v1, Sec. 2 (pp. 1-3) and Sec. 4 (p. 4). Kind: error.
- Issue: The note claims that the two terms producing the linear part of the corrected evolution combine to O(k^2), so that C1 = 0 can be taken in Lemma 0.4 of the correction, and that the book's computation on p. 442 is correct apart from a division by k; it concludes that Bahri's own counterexample (arXiv:1512.02046, a correct refutation of the book's Cor 19.10 that Morgan and Tian accepted) "still stands after the correction". Both claims are false. They contradict the first note: the coefficient of the linear term is the first variation of the Levi-Civita connection evaluated at (S,S), which the first note shows can be nonzero; with C1 = 0 the maximum principle would keep every closed geodesic a geodesic. The error lies in extending H and S off the swept surface and replacing the space-time derivative of S along S by H + Ric(S,S) d_t before differentiating in t, which drops exactly the term that the book missed. The counterexample is consistent with the corrected statements (Theta(t') = 0 but L(t') > 0).
- HOL: not formalized (as above).
- Lean: both Lean developments contain the linear term and the length-dependent bound (MT228-MT230); neither repository mentions Bahri.
