(* Scratch work of Jared Yeager, for use in work with Eric Hall and Michael Norrish *)

open HolKernel Parse boolLib bossLib;
open dep_rewrite;
open pairTheory;
open arithmeticTheory;
open pred_setTheory;
open listTheory;
open rich_listTheory;
open realTheory;
open realLib;
open extrealTheory;
open sigma_algebraTheory;
open borelTheory;
open measureTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

(* open ex_machina; *)
open trivialTheory;
open pispaceTheory;
open memoryless_channelTheory;

val _ = new_theory "mc_taxonomy";

val _ = hide "W";

(* ---------------------------------------------------------------------------*)
(* Lemmas to port to Trivial                                                  *)
(* ---------------------------------------------------------------------------*)

(* --------------- General Arithmetic ----------------------------------------*)

(* Extreal sum helpers for non-negative terms, where the library versions     *)
(* need finite (Normal) constants.                                            *)

(* TODO: See if that can be made into (c * f x) and named _CMUL_POS *)

(* Proof by Claude *)
(*
Theorem EXTREAL_SUM_IMAGE_RMUL_POS:
    ∀s. FINITE s ⇒ ∀(f :α -> extreal) (c :extreal). 0 ≤ c ∧ (∀x. x ∈ s ⇒ 0 ≤ f x) ⇒
        ∑ (λx. f x * c) s = ∑ f s * c
Proof
    ho_match_mp_tac FINITE_INDUCT >> rw[EXTREAL_SUM_IMAGE_EMPTY,mul_lzero] >>
    (* Peel e off a sum of non-negative terms. *)
    ‘∀g. (∀x. x ∈ e INSERT s ⇒ 0 ≤ g x) ⇒ ∑ g (e INSERT s) = g e + ∑ g s’ by (
        rw[] >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_PROPERTY] >>
        simp[DELETE_NON_ELEMENT_RWT] >> disj1_tac >> rw[] >>
        irule pos_not_neginf >> gs[]) >>
    ‘∑ f (e INSERT s) = f e + ∑ f s’ by (first_assum irule >> metis_tac[IN_INSERT]) >>
    ‘∑ (λx. f x * c) (e INSERT s) = f e * c + ∑ (λx. f x * c) s’ by (
        first_assum (qspec_then ‘λx. f x * c’ mp_tac) >> simp[] >>
        disch_then irule >> rw[] >> irule le_mul >> metis_tac[IN_INSERT]) >>
    ‘∑ (λx. f x * c) s = ∑ f s * c’ by (first_x_assum irule >> metis_tac[IN_INSERT]) >>
    simp[] >> irule (GSYM add_rdistrib) >> disj1_tac >> gs[] >>
    irule EXTREAL_SUM_IMAGE_POS >> gs[]
QED
*)
Theorem EXTREAL_SUM_IMAGE_CMUL_POS:
    ∀s. FINITE s ⇒ ∀f c. 0x ≤ c ∧ (∀x. x ∈ s ⇒ 0 ≤ f x) ⇒
        ∑ (λx. c * f x) s = c * ∑ f s
Proof
    ho_match_mp_tac FINITE_INDUCT >> rw[EXTREAL_SUM_IMAGE_EMPTY,mul_lzero] >>
    (* Peel e off a sum of non-negative terms. *)
    ‘∀g. (∀x. x ∈ e INSERT s ⇒ 0 ≤ g x) ⇒ ∑ g (e INSERT s) = g e + ∑ g s’ by (
        rw[] >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_PROPERTY] >>
        simp[DELETE_NON_ELEMENT_RWT] >> disj1_tac >> rw[] >>
        irule pos_not_neginf >> gs[]) >>
    ‘∑ f (e INSERT s) = f e + ∑ f s’ by (first_assum irule >> metis_tac[IN_INSERT]) >>
    ‘∑ (λx. c * f x) (e INSERT s) = c * f e + ∑ (λx. c * f x) s’ by (
        first_assum (qspec_then ‘λx. c * f x’ mp_tac) >> simp[] >>
        disch_then irule >> rw[] >> irule le_mul >> metis_tac[IN_INSERT]) >>
    ‘∑ (λx. c * f x) s = c * ∑ f s’ by (first_x_assum irule >> metis_tac[IN_INSERT]) >>
    simp[] >> irule (GSYM add_ldistrib) >> disj1_tac >> gs[] >>
    irule EXTREAL_SUM_IMAGE_POS >> gs[]
QED

(* TODO: reconcile with NESTED_EXTREAL_SUM_IMAGE_REVERSE *)
(* Proof by Claude *)
Theorem EXTREAL_SUM_IMAGE_SWAP_POS:
    ∀(f :α -> β -> extreal) A B. FINITE A ∧ FINITE B ∧ (∀x y. x ∈ A ∧ y ∈ B ⇒ 0 ≤ f x y) ⇒
        ∑ (λy. ∑ (λx. f x y) A) B = ∑ (λx. ∑ (λy. f x y) B) A
Proof
    rpt strip_tac >>
    (* Both orders flatten to a sum over a product set; the two product sets  *)
    (* are related by swapping coordinates, which is injective.               *)
    ‘∑ (λy. ∑ (λx. f x y) A) B = ∑ (λp. f (SND p) (FST p)) (B × A)’ by (
        ho_match_mp_tac EXTREAL_SUM_IMAGE_SUM_IMAGE >> simp[] >> disj1_tac >> rw[] >>
        irule pos_not_neginf >> gs[]) >>
    ‘∑ (λx. ∑ (λy. f x y) B) A = ∑ (λp. f (FST p) (SND p)) (A × B)’ by (
        ho_match_mp_tac EXTREAL_SUM_IMAGE_SUM_IMAGE >> simp[] >> disj1_tac >> rw[] >>
        irule pos_not_neginf >> gs[]) >>
    ‘B × A = IMAGE (λp. (SND p,FST p)) (A × B)’ by (
        simp[EXTENSION,EXISTS_PROD,FORALL_PROD] >> metis_tac[]) >>
    simp[] >> DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_IMAGE] >>
    simp[combinTheory.o_DEF,INJ_DEF,FORALL_PROD,EXISTS_PROD] >> disj1_tac >> rw[] >>
    irule pos_not_neginf >> gs[]
QED

(* Proof by Claude *)
Theorem EXTREAL_PROD_IMAGE_COUNT_ADD:
    ∀(f :num -> extreal) m n.
        EXTREAL_PROD_IMAGE f (count (m + n)) =
        EXTREAL_PROD_IMAGE f (count m) * EXTREAL_PROD_IMAGE (λi. f (i + m)) (count n)
Proof
    rw[count_add] >>
    DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_PROD_IMAGE_DISJOINT_UNION] >>
    simp[DISJOINT_DEF,Once EXTENSION] >>
    DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_PROD_IMAGE_IMAGE] >>
    simp[INJ_DEF,combinTheory.o_DEF] >>
    AP_TERM_TAC >> irule EXTREAL_PROD_IMAGE_EQ >> simp[]
QED

(* --------------- Results in Finite Case ------------------------------------*)

(* Proof by Claude *)
Theorem finite_space_POW_pos_fn_integral_reduce:
    ∀m f. measure_space m ∧ POW (m_space m) = measurable_sets m ∧
        FINITE (m_space m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ⇒
        ∫⁺ m f = ∑ (λx. f x * measure m {x}) (m_space m)
Proof
    rpt strip_tac >>
    (* Singletons of points of the (POW) space are measurable. *)
    ‘∀x. x ∈ m_space m ⇒ {x} ∈ measurable_sets m’ by (
        rw[] >> ‘{x} ∈ POW (m_space m)’ suffices_by metis_tac[] >>
        simp[IN_POW,SUBSET_DEF]) >>
    ‘sigma_algebra (measurable_space m)’ by metis_tac[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    (* Pointwise, f is the finite sum of its atoms' contributions:            *)
    (* ∑_x f(x)·𝟙_{x}(t) = f(t), since only the x = t term survives.          *)
    ‘∀t. t ∈ m_space m ⇒
        ∑ (λx. f x * indicator_fn {x} t) (m_space m) = f t’ by (
        rpt strip_tac >>
        ‘m_space m = t INSERT (m_space m DELETE t)’ by metis_tac[INSERT_DELETE] >>
        pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_PROPERTY] >>
        conj_tac
        >- (conj_tac >- simp[] >>
            disj1_tac >> rw[] >> irule pos_not_neginf >> irule le_mul >>
            simp[INDICATOR_FN_POS] >> gs[IN_INSERT, IN_DELETE] >> gs[]) >>
        simp[DELETE_DELETE] >>
        ‘∑ (λx. f x * indicator_fn {x} t) (m_space m DELETE t) = 0’ by (
            irule EXTREAL_SUM_IMAGE_0 >> simp[] >> rw[] >>
            ‘indicator_fn {x} t = 0’ by (rw[indicator_fn_def] >> gs[IN_DELETE]) >>
            simp[]) >>
        simp[indicator_fn_def]) >>
    (* Step 1: replace f by its atomic decomposition under the integral.      *)
    ‘∫⁺ m f = ∫⁺ m (λt. ∑ (λx. f x * indicator_fn {x} t) (m_space m))’ by (
        irule pos_fn_integral_cong >> rpt conj_tac
        >- (rw[] >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >> irule le_mul >>
            simp[INDICATOR_FN_POS] >> gs[])
        >- simp[] >- (rw[] >> metis_tac[]) >- simp[]) >>
    pop_assum SUBST1_TAC >>
    (* Step 2: push the integral through the finite sum (linearity for        *)
    (* non-negative functions; needs no finiteness of f).                     *)
    ‘∫⁺ m (λt. ∑ (λx. f x * indicator_fn {x} t) (m_space m)) =
     ∑ (λx. ∫⁺ m (λt. f x * indicator_fn {x} t)) (m_space m)’ by (
        ho_match_mp_tac pos_fn_integral_sum >> rpt conj_tac
        >- gs[] >- gs[]
        >- (rw[] >> irule le_mul >> simp[INDICATOR_FN_POS] >> gs[])
        >- (rw[] >> ho_match_mp_tac IN_MEASURABLE_BOREL_MUL_INDICATOR >>
            gs[subsets_def] >> irule IN_MEASURABLE_BOREL_CONST' >> gs[])) >>
    pop_assum SUBST1_TAC >>
    (* Step 3: each atom's integral collapses to f x · measure {x} (extreal   *)
    (* coefficient, so the PosInf case is handled uniformly).                 *)
    irule EXTREAL_SUM_IMAGE_EQ >> rpt conj_tac
    >- (rw[] >> irule pos_fn_integral_cmul_indicator' >> gs[])
    >- gs[]
    >- (disj1_tac >> rw[]
        >- (irule pos_not_neginf >> irule pos_fn_integral_pos >> rw[] >>
            irule le_mul >> simp[INDICATOR_FN_POS] >> gs[])
        >- (irule pos_not_neginf >> irule le_mul >> gs[MEASURE_POSITIVE]))
QED

(* Product measures of finite spaces with POW sigma-algebras.                 *)
(* Generic in the pairing operation cons; channels use cons = $++.            *)

(* Proof by Claude *)
Theorem POW_measure_singleton_pos:
    ∀A u x. measure_space (A,POW A,u) ∧ x ∈ A ⇒ 0 ≤ u {x}
Proof
    rpt strip_tac >> qspecl_then [‘(A,POW A,u)’,‘{x}’] mp_tac MEASURE_POSITIVE >>
    simp[measure_def,measurable_sets_def,IN_POW]
QED

(* Proof by Claude *)
Theorem FINITE_general_cross:
    ∀cons A B. FINITE A ∧ FINITE B ⇒ FINITE (general_cross cons A B)
Proof
    rpt strip_tac >>
    ‘general_cross cons A B = IMAGE (UNCURRY cons) (A × B)’ by (
        simp[Once EXTENSION,IN_general_cross,EXISTS_PROD] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >> simp[FINITE_CROSS]
QED

(* Proof by Claude *)
Theorem finite_space_POW_general_sigma:
    ∀cons A B. FINITE A ∧ FINITE B ⇒
        general_sigma cons (A,POW A) (B,POW B) =
            (general_cross cons A B,POW (general_cross cons A B))
Proof
    rw[general_sigma_def,space_def,subsets_def] >>
    qabbrev_tac ‘C = general_cross cons A B’ >>
    qabbrev_tac ‘G = general_prod cons (POW A) (POW B)’ >>
    ‘FINITE C’ by simp[Abbr ‘C’,FINITE_general_cross] >>
    (* Every rectangle lies inside C. *)
    ‘G ⊆ POW C’ by (
        simp[Abbr ‘G’,Abbr ‘C’,SUBSET_DEF,IN_general_prod,IN_POW,PULL_EXISTS,
             IN_general_cross] >>
        rw[] >> metis_tac[]) >>
    ‘subsets (sigma C G) = POW C’ suffices_by metis_tac[SPACE,SPACE_SIGMA] >>
    irule SUBSET_ANTISYM >> conj_tac
    >- (qspecl_then [‘G’,‘(C,POW C)’] mp_tac SIGMA_SUBSET >>
        simp[POW_SIGMA_ALGEBRA,space_def,subsets_def]) >>
    (* Each subset of C is a finite union of singletons {cons a b}, and each  *)
    (* such singleton is the rectangle of {a} and {b}.                        *)
    rw[Once SUBSET_DEF,IN_POW] >> rename1 ‘s ⊆ C’ >>
    ‘sigma_algebra (sigma C G)’ by (
        irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_def] >>
        metis_tac[SUBSET_DEF,IN_POW]) >>
    ‘FINITE s’ by metis_tac[SUBSET_FINITE] >>
    ‘s = BIGUNION (IMAGE (λz. {z}) s)’ by simp[Once EXTENSION,PULL_EXISTS] >>
    pop_assum SUBST1_TAC >>
    irule SIGMA_ALGEBRA_FINITE_UNION >> simp[SUBSET_DEF,PULL_EXISTS] >>
    qx_gen_tac ‘z’ >> strip_tac >> irule IN_SIGMA >>
    ‘z ∈ C’ by gs[SUBSET_DEF] >>
    qpat_x_assum ‘z ∈ C’ mp_tac >>
    simp[Abbr ‘C’,Abbr ‘G’,IN_general_cross,IN_general_prod,PULL_EXISTS] >>
    rw[] >> qexistsl [‘{a}’,‘{b}’] >>
    simp[Once EXTENSION,IN_general_cross,IN_POW]
QED

(* The product measure of s is the total weight of the pairs landing in s.   *)
(* Proof by Claude, tweaked *)
Theorem finite_space_POW_general_prod_measure_sum:
    ∀cons A B u v s. FINITE A ∧ FINITE B ∧
        measure_space (A,POW A,u) ∧ measure_space (B,POW B,v) ⇒
        general_prod_measure cons (A,POW A,u) (B,POW B,v) s =
            ∑ (λ(x,y). u {x} * v {y}) {(x,y) | x ∈ A ∧ y ∈ B ∧ cons x y ∈ s}
Proof
    rpt strip_tac >>
    ‘∀x. x ∈ A ⇒ 0 ≤ u {x}’ by metis_tac[POW_measure_singleton_pos] >>
    ‘∀y. y ∈ B ⇒ 0 ≤ v {y}’ by metis_tac[POW_measure_singleton_pos] >>
    ‘∀x y. x ∈ A ∧ y ∈ B ⇒ 0 ≤ 𝟙 s (cons x y) * u {x} * v {y}’ by
        metis_tac[le_mul,INDICATOR_FN_POS] >>
    (* Both integrals collapse to sums over the atoms (y outer, x inner).     *)
    ‘∀y. ∫⁺ (A,POW A,u) (λx. 𝟙 s (cons x y)) = ∑ (λx. 𝟙 s (cons x y) * u {x}) A’ by (
        rw[] >> qspecl_then [‘(A,POW A,u)’,‘λx. 𝟙 s (cons x y)’] mp_tac
            finite_space_POW_pos_fn_integral_reduce >>
        simp[m_space_def,measurable_sets_def,measure_def,INDICATOR_FN_POS]) >>
    ‘general_prod_measure cons (A,POW A,u) (B,POW B,v) s =
     ∑ (λy. ∑ (λx. 𝟙 s (cons x y) * u {x}) A * v {y}) B’ by (
        simp[general_prod_measure_def] >>
        qspecl_then [‘(B,POW B,v)’,‘λy. ∑ (λx. 𝟙 s (cons x y) * u {x}) A’] mp_tac
            finite_space_POW_pos_fn_integral_reduce >>
        simp[m_space_def,measurable_sets_def,measure_def] >> disch_then irule >>
        rw[] >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >>
        metis_tac[le_mul,INDICATOR_FN_POS]) >>
    pop_assum SUBST1_TAC >>
    (* Push v {y} into the inner sum, swap the order of summation, and        *)
    (* flatten into one sum over A × B.                                       *)
    ‘∑ (λy. ∑ (λx. 𝟙 s (cons x y) * u {x}) A * v {y}) B =
     ∑ (λy. ∑ (λx. 𝟙 s (cons x y) * u {x} * v {y}) A) B’ by (
        irule EXTREAL_SUM_IMAGE_EQ' >> rw[] >>
        qmatch_goalsub_abbrev_tac ‘∑ f A’ >> simp[] >>
        irule $ SRULE [Once mul_comm] $ GSYM $ SRULE [Once mul_comm] EXTREAL_SUM_IMAGE_CMUL_POS >>
        simp[Abbr ‘f’,le_mul,INDICATOR_FN_POS]) >>
    pop_assum SUBST1_TAC >>
    ‘∑ (λy. ∑ (λx. 𝟙 s (cons x y) * u {x} * v {y}) A) B =
     ∑ (λx. ∑ (λy. 𝟙 s (cons x y) * u {x} * v {y}) B) A’ by (
        ho_match_mp_tac EXTREAL_SUM_IMAGE_SWAP_POS >> simp[]) >>
    pop_assum SUBST1_TAC >>
    ‘∑ (λx. ∑ (λy. 𝟙 s (cons x y) * u {x} * v {y}) B) A =
     ∑ (λp. 𝟙 s (cons (FST p) (SND p)) * u {FST p} * v {SND p}) (A × B)’ by (
        ho_match_mp_tac EXTREAL_SUM_IMAGE_SUM_IMAGE >> simp[] >> disj1_tac >> rw[] >>
        irule pos_not_neginf >> gs[]) >>
    pop_assum SUBST1_TAC >>
    (* Drop the pairs missing s (indicator 0); on the rest the indicator is 1. *)
    ‘{(x,y) | x ∈ A ∧ y ∈ B ∧ cons x y ∈ s} =
     (A × B) ∩ {p | cons (FST p) (SND p) ∈ s}’ by
        simp[EXTENSION,FORALL_PROD,CONJ_ASSOC] >>
    pop_assum SUBST1_TAC >>
    ‘∑ (λp. 𝟙 s (cons (FST p) (SND p)) * u {FST p} * v {SND p}) (A × B) =
     ∑ (λp. 𝟙 s (cons (FST p) (SND p)) * u {FST p} * v {SND p})
       ((A × B) ∩ {p | cons (FST p) (SND p) ∈ s})’ by (
        irule (GSYM EXTREAL_SUM_IMAGE_INTER_ELIM) >> simp[] >> conj_tac
        >- simp[indicator_fn_def] >>
        disj1_tac >> rw[] >> irule pos_not_neginf >> gs[]) >>
    pop_assum SUBST1_TAC >>
    irule EXTREAL_SUM_IMAGE_EQ' >>
    simp[FORALL_PROD,indicator_fn_def,INTER_FINITE,FINITE_CROSS]
QED

(* When cons can be undone on A × B, the sum can range over s itself.        *)
(* Proof by Claude *)
Theorem finite_space_POW_general_prod_measure_split_sum:
    ∀cons car cdr A B u v s. FINITE A ∧ FINITE B ∧
        measure_space (A,POW A,u) ∧ measure_space (B,POW B,v) ∧
        (∀x y. x ∈ A ∧ y ∈ B ⇒ car (cons x y) = x ∧ cdr (cons x y) = y) ∧
        s ⊆ general_cross cons A B ⇒
        general_prod_measure cons (A,POW A,u) (B,POW B,v) s =
            ∑ (λz. u {car z} * v {cdr z}) s
Proof
    rpt strip_tac >>
    ‘∀x. x ∈ A ⇒ 0 ≤ u {x}’ by metis_tac[POW_measure_singleton_pos] >>
    ‘∀y. y ∈ B ⇒ 0 ≤ v {y}’ by metis_tac[POW_measure_singleton_pos] >>
    simp[finite_space_POW_general_prod_measure_sum] >>
    (* s is the image of the index set under cons, injective by car/cdr.      *)
    qabbrev_tac ‘P = {(x,y) | x ∈ A ∧ y ∈ B ∧ cons x y ∈ s}’ >>
    ‘FINITE P’ by (
        irule SUBSET_FINITE >> qexists_tac ‘A × B’ >>
        simp[FINITE_CROSS,Abbr ‘P’,SUBSET_DEF,FORALL_PROD]) >>
    ‘s = IMAGE (λp. cons (FST p) (SND p)) P’ by (
        simp[Abbr ‘P’,EXTENSION,EXISTS_PROD] >>
        gs[SUBSET_DEF,general_cross_def] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >>
    DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_IMAGE] >> rpt conj_tac
    >- simp[]
    >- (simp[INJ_DEF,Abbr ‘P’,FORALL_PROD,EXISTS_PROD] >> metis_tac[])
    >- (disj1_tac >> simp[Abbr ‘P’,PULL_EXISTS] >> rw[] >>
        irule pos_not_neginf >> irule le_mul >> simp[]) >>
    irule EXTREAL_SUM_IMAGE_EQ' >> simp[Abbr ‘P’,FORALL_PROD,combinTheory.o_DEF]
QED

(* Proof by Claude *)
Theorem finite_space_POW_general_prod_measure_APPEND_sum:
    ∀k A B u v s. FINITE A ∧ FINITE B ∧
        measure_space (A,POW A,u) ∧ measure_space (B,POW B,v) ∧
        (∀x. x ∈ A ⇒ LENGTH x = k) ∧
        s ⊆ general_cross $++ A B ⇒
        general_prod_measure $++ (A,POW A,u) (B,POW B,v) s =
            ∑ (λz. u {TAKE k z} * v {DROP k z}) s
Proof
    rpt strip_tac >>
    irule finite_space_POW_general_prod_measure_split_sum >> simp[] >>
    rw[] >> res_tac >> gvs[TAKE_APPEND1,DROP_APPEND1]
QED

(* No injectivity needed: the product measure is the image of u ⊗ v under    *)
(* cons, and finite additivity suffices on a finite space.                    *)
(* Proof by Claude *)
Theorem finite_space_POW_measure_space_general_prod_measure:
    ∀cons A B u v. FINITE A ∧ FINITE B ∧
        measure_space (A,POW A,u) ∧ measure_space (B,POW B,v) ⇒
        measure_space (general_prod_measure_space cons (A,POW A,u) (B,POW B,v))
Proof
    rpt strip_tac >>
    simp[general_prod_measure_space,finite_space_POW_general_sigma] >>
    irule finite_additivity_sufficient_for_finite_spaces2 >>
    simp[POW_SIGMA_ALGEBRA,FINITE_general_cross,positive_def,additive_def] >>
    ‘∀x. x ∈ A ⇒ 0 ≤ u {x}’ by metis_tac[POW_measure_singleton_pos] >>
    ‘∀y. y ∈ B ⇒ 0 ≤ v {y}’ by metis_tac[POW_measure_singleton_pos] >>
    simp[finite_space_POW_general_prod_measure_sum] >>
    (* The measure of s is a sum of non-negative terms over the pairs that   *)
    (* cons into s, so it is non-negative and adds over disjoint s and t.    *)
    qabbrev_tac ‘f = λ(x,y). u {x} * v {y}’ >>
    ‘∀x y. x ∈ A ∧ y ∈ B ⇒ 0 ≤ f (x,y)’ by (
        rw[Abbr ‘f’] >> irule le_mul >> simp[]) >>
    ‘∀s. FINITE {(x,y) | x ∈ A ∧ y ∈ B ∧ cons x y ∈ s}’ by (
        rw[] >> irule SUBSET_FINITE >> qexists_tac ‘A × B’ >>
        simp[FINITE_CROSS,SUBSET_DEF,FORALL_PROD]) >>
    conj_tac >> rpt strip_tac
    >- (‘{(x,y) | x ∈ A ∧ y ∈ B ∧ (cons x y ∈ s ∨ cons x y ∈ t)} =
         {(x,y) | x ∈ A ∧ y ∈ B ∧ cons x y ∈ s} ∪
         {(x,y) | x ∈ A ∧ y ∈ B ∧ cons x y ∈ t}’ by (
            simp[EXTENSION,FORALL_PROD] >> metis_tac[]) >>
        pop_assum SUBST1_TAC >>
        irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp[] >> conj_tac
        >- (gs[DISJOINT_DEF,EXTENSION,FORALL_PROD] >> metis_tac[]) >>
        disj1_tac >> simp[FORALL_PROD] >> rw[] >> irule pos_not_neginf >> simp[]) >>
    irule EXTREAL_SUM_IMAGE_POS >> simp[FORALL_PROD]
QED

(* Proof by Claude *)
Theorem finite_space_POW_prob_space_general_prod_measure:
    ∀cons A B u v. FINITE A ∧ FINITE B ∧
        prob_space (A,POW A,u) ∧ prob_space (B,POW B,v) ⇒
        prob_space (general_prod_measure_space cons (A,POW A,u) (B,POW B,v))
Proof
    rw[prob_space_def]
    >- (irule finite_space_POW_measure_space_general_prod_measure >> simp[]) >>
    gs[] >>
    ‘∀x. x ∈ A ⇒ 0 ≤ u {x}’ by metis_tac[POW_measure_singleton_pos] >>
    ‘∀y. y ∈ B ⇒ 0 ≤ v {y}’ by metis_tac[POW_measure_singleton_pos] >>
    simp[general_prod_measure_space,finite_space_POW_general_prod_measure_sum] >>
    (* Total mass: ∑ over A × B of u {x} * v {y} factors as u A * v B = 1.   *)
    ‘{(x,y) | x ∈ A ∧ y ∈ B ∧ cons x y ∈ general_cross cons A B} = A × B’ by (
        simp[EXTENSION,FORALL_PROD,IN_general_cross] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >>
    ‘∑ (λ(x,y). u {x} * v {y}) (A × B) = ∑ (λp. u {FST p} * v {SND p}) (A × B)’ by (
        irule EXTREAL_SUM_IMAGE_EQ' >> simp[FORALL_PROD,FINITE_CROSS]) >>
    pop_assum SUBST1_TAC >>
    ‘∑ (λx. ∑ (λy. u {x} * v {y}) B) A = ∑ (λp. u {FST p} * v {SND p}) (A × B)’ by (
        ho_match_mp_tac EXTREAL_SUM_IMAGE_SUM_IMAGE >> simp[] >> disj1_tac >> rw[] >>
        irule pos_not_neginf >> irule le_mul >> simp[]) >>
    pop_assum (SUBST1_TAC o SYM) >>
    ‘∑ (λy. ∑ (λx. u {x} * v {y}) A) B = ∑ (λx. ∑ (λy. u {x} * v {y}) B) A’ by (
        ho_match_mp_tac EXTREAL_SUM_IMAGE_SWAP_POS >> rw[] >> irule le_mul >> simp[]) >>
    pop_assum (SUBST1_TAC o SYM) >>
    ‘∑ (λx. u {x}) A = 1 ∧ ∑ (λy. v {y}) B = 1’ by (
        conj_tac
        >- (qspecl_then [‘(A,POW A,u)’,‘A’] mp_tac MEASURE_EXTREAL_SUM_IMAGE >>
            simp[measure_def,measurable_sets_def,IN_POW]) >>
        qspecl_then [‘(B,POW B,v)’,‘B’] mp_tac MEASURE_EXTREAL_SUM_IMAGE >>
        simp[measure_def,measurable_sets_def,IN_POW]) >>
    ‘∑ (λy. ∑ (λx. u {x} * v {y}) A) B = ∑ (λy. v {y}) B’ suffices_by simp[] >>
    irule EXTREAL_SUM_IMAGE_EQ' >> rw[] >>
    simp[Once mul_comm] >> 
    DEP_PURE_ONCE_REWRITE_TAC[EXTREAL_SUM_IMAGE_CMUL_POS] >> simp[]
QED

(* --------------- Loosening pair_operation_def ------------------------------*)

(*
Note to self:
trivialTheory.pos_fn_integral_cmult_clean depricated ->
lebesgueTheory.pos_fn_integral_cmul_general
*)

Definition pair_operation_weak_def:
    pair_operation_weak cons A D car cdr ⇔
    (∀a b. a ∈ A ∧ b ∈ D ⇒ car (cons a b) = a ∧ cdr (cons a b) = b) ∧
    ∀a b c d. a ∈ A ∧ c ∈ A ∧ b ∈ D ∧ d ∈ D ⇒ (cons a b = cons c d ⇔ a = c ∧ b = d)
End

Theorem general_prod_measure_general_cross:
    ∀cons car cdr m1 m2 A B. pair_operation_weak cons (m_space m1) (m_space m2) car cdr ∧
        measure_space m1 ∧ measure_space m2 ∧
        A ∈ measurable_sets m1 ∧ B ∈ measurable_sets m2 ⇒
        general_prod_measure cons m1 m2 (general_cross cons A B) =
        measure m1 A * measure m2 B
Proof
    rw[general_prod_measure_def] >> simp[GSYM pos_fn_integral_indicator] >>
    irule EQ_TRANS >> irule_at Any pos_fn_integral_cmul_general >>
    irule_at Any pos_fn_integral_pos >> simp[INDICATOR_FN_POS] >>
    irule_at Any IN_MEASURABLE_BOREL_INDICATOR >> qexists ‘B’ >> simp[] >>
    irule pos_fn_integral_cong >> simp[GSYM IMP_CONJ_THM,GSYM FORALL_AND_THM] >>
    qx_gen_tac ‘y’ >> strip_tac >> irule_at Any le_mul >>
    ntac 2 $ irule_at Any pos_fn_integral_pos >> simp[INDICATOR_FN_POS] >>
    simp[Once mul_comm] >> irule EQ_TRANS >>
    irule_at Any pos_fn_integral_cmul_general >> simp[INDICATOR_FN_POS] >>
    irule_at Any IN_MEASURABLE_BOREL_INDICATOR >> qexists ‘A’ >> simp[] >>
    irule pos_fn_integral_cong >> simp[GSYM IMP_CONJ_THM,GSYM FORALL_AND_THM] >>
    simp[le_mul,INDICATOR_FN_POS] >> qx_gen_tac ‘x’ >> strip_tac >>
    simp[indicator_fn_def,general_cross_def] >>
    gs[pair_operation_weak_def] >> first_x_assum $ qspecl_then [‘x’,‘y’] mp_tac >>
    ‘∀z. z ∈ A ⇒ z ∈ m_space m1’ by metis_tac[MEASURE_SPACE_IN_MSPACE] >>
    ‘∀z. z ∈ B ⇒ z ∈ m_space m2’ by metis_tac[MEASURE_SPACE_IN_MSPACE] >> rw[]
    >- (qexistsl [‘a’,‘b’] >> simp[] >> rw[] >> gs[])
    >- (qexistsl [‘a’,‘b’] >> simp[] >> Cases_on ‘y = b’ >> gs[])
    >- (qexistsl [‘a’,‘b’] >> simp[] >> rw[] >> gs[])
    >- metis_tac[]
QED

Theorem measure_space_general_prod_measure':
    ∀cons car cdr m1 m2. pair_operation_weak cons (m_space m1) (m_space m2) car cdr ∧
        sigma_finite_measure_space m1 ∧
        sigma_finite_measure_space m2 ⇒
        measure_space (general_prod_measure_space cons m1 m2)
Proof
    rw[] >> irule $ INST_TYPE [“:α” |-> “:(α # β)”,“:β” |-> “:γ”] measure_space_isomorphic >>
    irule_at Any measure_space_prod_measure >> ntac 2 $ first_assum $ irule_at Any >>
    simp[isomorphic_def,measure_preserving_def,in_measurability_preserving_alt] >>
    qexists ‘λ(a,b). cons a b’ >> simp[PULL_EXISTS,GSYM CONJ_ASSOC] >>
    qexistsl [‘prod_sets (measurable_sets m1) (measurable_sets m2)’,
        ‘general_prod cons (measurable_sets m1) (measurable_sets m2)’] >>
    gs[sigma_finite_measure_space_def] >> rpt conj_asm1_tac
    >- (simp[prod_measure_space_def,prod_sigma_def,SIGMA_REDUCE])
    >- (simp[general_prod_measure_space_def,general_sigma_def,SIGMA_REDUCE])
    >- (rw[subset_class_def,m_space_prod_measure_space] >>
        irule SUBSET_CROSS >> simp[MEASURABLE_SETS_SUBSET_SPACE])
    >- (rw[subset_class_def,general_prod_measure_space_def,general_cross_def,general_prod_def,SUBSET_DEF] >>
        gs[] >> irule_at Any EQ_REFL >> simp[MEASURE_SPACE_IN_MSPACE,SF SFY_ss])
    >- (simp[BIJ_IFF_INV] >>
        simp[FORALL_PROD,prod_measure_space_def,general_prod_measure_space_def,general_cross_def] >>
        rw[] >- (irule_at Any EQ_REFL >> simp[]) >>
        qexists ‘λc. (car c,cdr c)’ >> gs[pair_operation_weak_def,PULL_EXISTS])
    >- (simp[PULL_EXISTS] >> qx_genl_tac [‘s1’,‘s2’] >> rw[] >>
        simp[general_prod_def] >> qexistsl [‘s1’,‘s2’] >> simp[EXTENSION,general_cross_def] >>
        qx_gen_tac ‘c’ >> rw[EQ_IMP_THM]
        >- (rename [‘FST z’] >> Cases_on ‘z’ >> rename [‘(a,b)’] >>
            gs[] >> irule_at Any EQ_REFL >> simp[])
        >- (qexists ‘(a,b)’ >> simp[]))
    >- (simp[general_prod_def,PULL_EXISTS] >> qx_genl_tac [‘s1’,‘s2’] >> rw[] >>
        qexistsl [‘s1’,‘s2’] >> simp[EXTENSION,FORALL_PROD] >>
        qx_genl_tac [‘x’,‘y’] >> simp[general_cross_def,m_space_prod_measure_space] >>
        simp[EQ_IMP_THM] >> conj_tac >> strip_tac
        >- (gs[BIJ_DEF,INJ_DEF] >> first_x_assum $ qspecl_then [‘(x,y)’,‘(a,b)’] mp_tac >>
            simp[m_space_prod_measure_space,MEASURE_SPACE_IN_MSPACE,SF SFY_ss])
        >- (simp[MEASURE_SPACE_IN_MSPACE,SF SFY_ss] >> irule_at Any EQ_REFL >> simp[]))
    >- (rw[prod_measure_space_def,prod_measure_def,general_prod_measure_space_def] >>
        irule pos_fn_integral_cong >> simp[GSYM IMP_CONJ_THM,GSYM FORALL_AND_THM] >>
        qx_gen_tac ‘y’ >> strip_tac >> irule_at Any pos_fn_integral_cong >>
        ntac 2 $ irule_at Any pos_fn_integral_pos >> simp[INDICATOR_FN_POS] >>
        qx_gen_tac ‘x’ >> rw[indicator_fn_def] >- gs[] >>
        rename [‘c ∈ s’] >> Cases_on ‘c’ >> rename [‘(a,b) ∈ s’] >>
        gs[BIJ_DEF,INJ_DEF] >> CCONTR_TAC >>
        first_x_assum $ qspecl_then [‘(x,y)’,‘(a,b)’] mp_tac >> gs[m_space_prod_measure_space] >>
        ntac 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >>
        gs[GSYM measurable_sets_prod_measure_space] >>
        ntac 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SUBSET_CLASS >>
        gs[] >> pop_assum kall_tac >> gs[subset_class_def] >>
        pop_assum $ dxrule >> simp[SUBSET_DEF,FORALL_PROD] >>
        disch_then drule >> simp[] >> rw[] >> CCONTR_TAC >> gs[])
QED

Theorem prob_space_general_prod_measure:
    ∀cons car cdr m1 m2. pair_operation_weak cons (m_space m1) (m_space m2) car cdr ∧
        prob_space m1 ∧ prob_space m2 ⇒
        prob_space (general_prod_measure_space cons m1 m2)
Proof
    rw[] >> simp[prob_space_def] >>
    irule_at Any measure_space_general_prod_measure' >> last_assum $ irule_at Any >>
    simp[prob_space_sigma_finite_measure_space] >>
    gs[prob_space_def,general_prod_measure_space_def,GSYM general_prod_measure_def] >>
    irule EQ_TRANS >> irule_at Any general_prod_measure_general_cross >>
    last_assum $ irule_at Any >> simp[MEASURE_SPACE_MSPACE_MEASURABLE]
QED

(* -------------------------------------------------------------------------- *)
(* Memoryless channel probability                                             *)
(*                                                                            *)
(* Takes a channel c, input a, and output b, and returns the probability      *)
(* of returning output b given input a.                                       *)
(* -------------------------------------------------------------------------- *)
Definition mcp_def:
  mcp c a b = mcchannel c a {b}
End

(* -------------------------------------------------------------------------- *)
(* Checks if a memoryless channel is a binary memoryless channel, i.e. it     *)
(* has two possible inputs                                                    *)
(* -------------------------------------------------------------------------- *)
Definition binary_mc_def:
    binary_mc c ⇔ CARD (mcdomain c) = 2
End

(* -------------------------------------------------------------------------- *)
(* Checks if a memoryless channel is a discrete memoryless channel.           *)
(*                                                                            *)
(* It should have a finite set of inputs and a finite set of outputs.         *)
(*                                                                            *)
(* We want to be able to specify the probability of each individual output    *)
(* given each individual input, so we reqruire that each singleton is an      *)
(* event.                                                                     *)
(* -------------------------------------------------------------------------- *)
Definition discrete_mc_def:
  discrete_mc c ⇔ FINITE (mcdomain c) ∧
                  FINITE (mccodomain c) ∧
                  ∀y. y ∈ mccodomain c ⇒ {y} ∈ mcevents c
End

Theorem discrete_mc_POW_sigma_algebra:
    ∀c. discrete_mc c ⇒ mcsigma c = (mccodomain c,POW (mccodomain c))
Proof
    rw[discrete_mc_def] >>
    qspec_then ‘c’ assume_tac memoryless_channel_wf_sigma_algebra_property >>
    gs[mcsigma_alt] >> irule SUBSET_ANTISYM >> conj_tac
    >- (simp[SUBSET_DEF] >> simp[IN_POW] >>
        dxrule SIGMA_ALGEBRA_SUBSET_CLASS >> simp[subset_class_def]) >>
    simp[SUBSET_DEF] >> simp[IN_POW] >>
    qx_gen_tac ‘s’ >> strip_tac >>
    dxrule SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[subsets_def] >>
    disch_then $ qspec_then ‘IMAGE (λx. {x}) s’ mp_tac >>
    ‘BIGUNION (IMAGE (λx. {x}) s) = s’ by simp[Once EXTENSION,PULL_EXISTS] >>
    pop_assum SUBST1_TAC >> disch_then irule >>
    simp[SUBSET_DEF,PULL_EXISTS] >> reverse $ conj_tac
    >- (rw[] >> first_x_assum irule >> gs[SUBSET_DEF]) >>
    irule cardinalTheory.COUNTABLE_IMAGE >> irule finite_countable >>
    simp[SUBSET_FINITE,SF SFY_ss]
QED

(* Reading the components back out of a channel built from a wf rep.          *)
(* Proof by Claude *)
Theorem memoryless_channel_ABS_components:
    ∀r. wf_memoryless_channel r ⇒
        mcdomain (memoryless_channel_ABS r) = mcdomain0 r ∧
        mcsigma (memoryless_channel_ABS r) = mcsigma0 r ∧
        mccodomain (memoryless_channel_ABS r) = mccodomain0 r ∧
        mcevents (memoryless_channel_ABS r) = mcevents0 r ∧
        mcchannel (memoryless_channel_ABS r) = mcchannel0 r
Proof
    rw[memoryless_channel_ABSREP] >>
    simp[mcdomain_def,mcsigma_def,mccodomain_def,mcevents_def,mcchannel_def,
         quotientTheory.FUN_MAP_THM]
QED

(* A discrete channel is determined by its single-output probabilities.      *)
(* Proof by Claude *)
Theorem discrete_mc_mcchannel_sum:
    ∀W x ys. discrete_mc W ∧ x ∈ mcdomain W ∧ ys ∈ mcevents W ⇒
        mcchannel W x ys = ∑ (λy. mcp W x y) ys
Proof
    rpt strip_tac >>
    ‘mcevents W = POW (mccodomain W)’ by (
        imp_res_tac discrete_mc_POW_sigma_algebra >> gs[mcsigma_alt]) >>
    ‘prob_space (mccodomain W,POW (mccodomain W),mcchannel W x)’ by
        metis_tac[memoryless_channel_wf_prob_space_property,mcprob_space_alt] >>
    gs[discrete_mc_def,prob_space_def,IN_POW,mcp_def] >>
    qspecl_then [‘(mccodomain W,POW (mccodomain W),mcchannel W x)’,‘ys’] mp_tac
        MEASURE_EXTREAL_SUM_IMAGE >>
    simp[measure_def,measurable_sets_def,IN_POW] >> disch_then irule >>
    metis_tac[SUBSET_FINITE,SUBSET_DEF]
QED

(*** Boolean reskins ***)

Datatype:
    BIT = ZERO | ONE
End

Definition BIT_XOR_DEF:
    BIT_XOR ZERO ZERO = ZERO ∧
    BIT_XOR ZERO ONE = ONE ∧
    BIT_XOR ONE ZERO = ONE ∧
    BIT_XOR ONE ONE = ZERO
End

Definition BIT_NOT_DEF:
    BIT_NOT ZERO = ONE ∧
    BIT_NOT ONE = ZERO
End

Datatype:
    POLE = POS | NEG
End

(*** Meta Lifting Definition ***)

(* prove above wf under some conditions *)
Definition meta_lift_channel_rep_def:
    meta_lift_channel_rep (upa:α->γ) (downa:γ->α) (upb:β->δ) (downb:δ->β) W = (
        IMAGE upa (mcdomain W),
        (IMAGE upb (mccodomain W), IMAGE (IMAGE upb) (mcevents W)),
        (λal bls. mcchannel W (downa al) (IMAGE downb bls)))
End

Definition meta_lift_channel_def:
    meta_lift_channel (upa:α->γ) (downa:γ->α) (upb:β->δ) (downb:δ->β) W =
        memoryless_channel_ABS (meta_lift_channel_rep upa downa upb downb W)
End

(* The lifted output space is an isomorphic copy of W's, transported by upb. *)
(* Proof by Claude *)
Theorem wf_memoryless_channel_meta_lift_channel:
    ∀upa downa upb downb W.
        (∀a. a ∈ mcdomain W ⇒ downa (upa a) = a) ∧
        (∀b. b ∈ mccodomain W ⇒ downb (upb b) = b) ⇒
        wf_memoryless_channel (meta_lift_channel_rep upa downa upb downb W)
Proof
    rpt gen_tac >> strip_tac >>
    ‘sigma_algebra (mccodomain W,mcevents W)’ by
        metis_tac[memoryless_channel_wf_sigma_algebra_property,mcsigma_alt] >>
    ‘BIJ upb (mccodomain W) (IMAGE upb (mccodomain W))’ by (
        simp[BIJ_DEF,INJ_DEF,SURJ_DEF] >> metis_tac[]) >>
    ‘∀s. s ∈ mcevents W ⇒ s ⊆ mccodomain W’ by (
        rw[] >> drule_then (qspec_then ‘s’ mp_tac) SIGMA_ALGEBRA_SUBSET_SPACE >>
        simp[space_def,subsets_def]) >>
    ‘∀s. s ⊆ mccodomain W ⇒ IMAGE downb (IMAGE upb s) = s’ by (
        rw[Once EXTENSION] >> metis_tac[SUBSET_DEF]) >>
    ‘∀s. s ⊆ mccodomain W ⇒ PREIMAGE upb (IMAGE upb s) ∩ mccodomain W = s’ by (
        rw[Once EXTENSION,PREIMAGE_def] >> metis_tac[SUBSET_DEF]) >>
    ‘sigma_algebra (IMAGE upb (mccodomain W),IMAGE (IMAGE upb) (mcevents W))’ by (
        qspecl_then [‘(mccodomain W,mcevents W)’,‘IMAGE upb (mccodomain W)’,‘upb’] mp_tac
            IMAGE_SIGMA_ALGEBRA >> simp[space_def,subsets_def]) >>
    simp[wf_memoryless_channel_def,meta_lift_channel_rep_def,mcsigma0_def,mcdomain0_def,
         mcprob_space0_def,mccodomain0_def,mcevents0_def,mcchannel0_def,PULL_EXISTS] >>
    qx_gen_tac ‘a’ >> strip_tac >>
    ‘prob_space (mccodomain W,mcevents W,mcchannel W a)’ by
        metis_tac[memoryless_channel_wf_prob_space_property,mcprob_space_alt] >>
    simp[prob_space_def] >> reverse conj_tac >- gs[prob_space_def] >>
    (* drule rather than irule: the theorem's type variables clash with ours. *)
    ‘measure_space (mccodomain W,mcevents W,mcchannel W a)’ by gs[prob_space_def] >>
    drule_then irule measure_space_isomorphic >>
    simp[isomorphic_def] >> qexists_tac ‘upb’ >>
    simp[in_measure_preserving,in_measurability_preserving,PULL_EXISTS]
QED

(* Proof by Claude *)
Theorem meta_lift_channel_components:
    ∀upa downa upb downb W.
        (∀a. a ∈ mcdomain W ⇒ downa (upa a) = a) ∧
        (∀b. b ∈ mccodomain W ⇒ downb (upb b) = b) ⇒
        mcdomain (meta_lift_channel upa downa upb downb W) = IMAGE upa (mcdomain W) ∧
        mccodomain (meta_lift_channel upa downa upb downb W) = IMAGE upb (mccodomain W) ∧
        mcevents (meta_lift_channel upa downa upb downb W) =
            IMAGE (IMAGE upb) (mcevents W) ∧
        ∀al bls. mcchannel (meta_lift_channel upa downa upb downb W) al bls =
            mcchannel W (downa al) (IMAGE downb bls)
Proof
    rpt gen_tac >> strip_tac >>
    drule_all wf_memoryless_channel_meta_lift_channel >> strip_tac >>
    simp[meta_lift_channel_def,memoryless_channel_ABS_components] >>
    simp[meta_lift_channel_rep_def,mcdomain0_def,mccodomain0_def,mcevents0_def,
         mcsigma0_def,mcchannel0_def]
QED

Definition list_lift_channel_def:
    list_lift_channel = meta_lift_channel (λa:α. [a]) HD (λb:β. [b]) HD
End

Definition list_lift_range_channel_def:
    list_lift_range_channel = meta_lift_channel I I (λb:β. [b]) HD
End

Definition INL_lift_channel_def:
    INL_lift_channel = meta_lift_channel I I INL OUTL
End

Definition INR_lift_channel_def:
    INR_lift_channel = meta_lift_channel I I INR OUTR
End

(*** Compound Channels ***)

(* Prove wf *)
Definition basic_fusion_channel_rep_def:
    basic_fusion_channel_rep splitn W0 W1 = (
        general_cross $++ (mcdomain W0) (mcdomain W1),
        general_sigma $++ (mcsigma W0) (mcsigma W1),
        (λa01.
            let
                a0 = TAKE splitn a01;
                a1 = DROP splitn a01
            in
                general_prod_measure $++
                (mccodomain W0, mcevents W0, mcchannel W0 a0)
                (mccodomain W1, mcevents W1, mcchannel W1 a1)))
End

Theorem wf_memoryless_channel_basic_fusion_channel:
    ∀W0 W1 splitin splitout. (∀x0. x0 ∈ mcdomain W0 ⇒ LENGTH x0 = splitin) ∧
        (∀y0. y0 ∈ mccodomain W0 ⇒ LENGTH y0 = splitout) ⇒
        wf_memoryless_channel (basic_fusion_channel_rep splitin W0 W1)
Proof
    rw[] >> simp[wf_memoryless_channel_def] >> conj_asm1_tac
    >- (rw[basic_fusion_channel_rep_def,mcsigma0_def] >>
        irule sigma_algebra_general_sigma >>
        simp[memoryless_channel_wf_sigma_algebra_property,SIGMA_ALGEBRA_SUBSET_CLASS]) >>
    qx_gen_tac ‘a’ >>
    rw[basic_fusion_channel_rep_def,mcdomain0_def,mcprob_space0_def,
        mccodomain0_def,mcevents0_def,mcchannel0_def,mcsigma0_def] >>
    simp[general_sigma_def] >> ntac 2 $ simp[Once $ GSYM SIGMA_REDUCE] >>
    qspecl_then [‘$++’,‘mcprob_space W0 (TAKE splitin a)’,‘mcprob_space W1 (DROP splitin a)’] mp_tac $
        SRULE [GSYM general_prod_measure_def] $ GSYM general_prod_measure_space >>
    simp[mcprob_space_alt,GSYM general_sigma_def,mcsigma_alt] >> disch_then kall_tac >>
    irule prob_space_general_prod_measure >> simp[GSYM mcprob_space_alt] >>
    ntac 2 $ irule_at Any memoryless_channel_wf_prob_space_property >>
    qexistsl [‘DROP splitout’,‘TAKE splitout’] >>
    gvs[general_cross_def,pair_operation_weak_def] >>
    rename [‘a ⧺ b’] >> ‘splitin = LENGTH a’ by simp[] >> pop_assum SUBST1_TAC >>
    simp[FIRSTN_LENGTH_APPEND,DROP_LENGTH_APPEND] >> ntac 3 $ pop_assum kall_tac >>
    conj_tac
    >- (qx_genl_tac [‘a’,‘b’] >> strip_tac >> ‘splitout = LENGTH a’ by simp[] >>
        pop_assum SUBST1_TAC >> simp[FIRSTN_LENGTH_APPEND,DROP_LENGTH_APPEND]) >>
    rw[] >> qspecl_then [‘a’,‘b’,‘c’,‘d’] mp_tac $ cj 1 APPEND_11_LENGTH >> simp[]
QED

Theorem wf_memoryless_channel_basic_fusion_channel_discrete:
    ∀W0 W1 n0. discrete_mc W0 ∧ discrete_mc W1 ∧
        (∀a0. a0 ∈ mcdomain W0 ⇒ LENGTH a0 = n0) ⇒
        wf_memoryless_channel (basic_fusion_channel_rep n0 W0 W1)
Proof
    rpt strip_tac >>
    ‘mcevents W0 = POW (mccodomain W0) ∧ mcevents W1 = POW (mccodomain W1)’ by (
        imp_res_tac discrete_mc_POW_sigma_algebra >> gs[mcsigma_alt]) >>
    gs[discrete_mc_def] >>
    simp[wf_memoryless_channel_def,basic_fusion_channel_rep_def,mcsigma0_def,mcdomain0_def,
         mcprob_space0_def,mccodomain0_def,mcevents0_def,mcchannel0_def,mcsigma_alt,
         finite_space_POW_general_sigma,POW_SIGMA_ALGEBRA,IN_general_cross,PULL_EXISTS] >>
    rpt strip_tac >>
    ‘TAKE n0 (a ++ b) = a ∧ DROP n0 (a ++ b) = b’ by (
        res_tac >> gvs[TAKE_APPEND1,DROP_APPEND1]) >>
    simp[] >>
    qmatch_goalsub_abbrev_tac ‘general_prod_measure _ m0 m1’ >>
    ‘prob_space (general_prod_measure_space $++ m0 m1)’ suffices_by
        simp[Abbr ‘m0’,Abbr ‘m1’,general_prod_measure_space,finite_space_POW_general_sigma] >>
    simp[Abbr ‘m0’,Abbr ‘m1’] >>
    irule finite_space_POW_prob_space_general_prod_measure >> simp[] >>
    metis_tac[memoryless_channel_wf_prob_space_property,mcprob_space_alt]
QED

Definition basic_fusion_channel_def:
    basic_fusion_channel splitn W0 W1 = memoryless_channel_ABS
        (basic_fusion_channel_rep splitn W0 W1)
End

(* Proof by Claude *)
Theorem basic_fusion_channel_discrete:
    ∀W0 W1 splitin. discrete_mc W0 ∧ discrete_mc W1 ∧
        (∀x0. x0 ∈ mcdomain W0 ⇒ LENGTH x0 = splitin) ⇒
        discrete_mc (basic_fusion_channel splitin W0 W1) ∧
        mcdomain (basic_fusion_channel splitin W0 W1) =
            general_cross $++ (mcdomain W0) (mcdomain W1) ∧
        mccodomain (basic_fusion_channel splitin W0 W1) =
            general_cross $++ (mccodomain W0) (mccodomain W1) ∧
        mcevents (basic_fusion_channel splitin W0 W1) =
            POW (general_cross $++ (mccodomain W0) (mccodomain W1))
Proof
    rpt gen_tac >> strip_tac >>
    drule_all wf_memoryless_channel_basic_fusion_channel_discrete >> strip_tac >>
    ‘mcevents W0 = POW (mccodomain W0) ∧ mcevents W1 = POW (mccodomain W1)’ by (
        imp_res_tac discrete_mc_POW_sigma_algebra >> gs[mcsigma_alt]) >>
    (* Unfold discrete_mc first, so ABS is read back before the rep unfolds. *)
    PURE_ONCE_REWRITE_TAC[discrete_mc_def] >>
    simp[basic_fusion_channel_def,memoryless_channel_ABS_components] >>
    gs[discrete_mc_def] >>
    simp[basic_fusion_channel_rep_def,mcdomain0_def,mccodomain0_def,
         mcevents0_def,mcsigma0_def,mcsigma_alt,finite_space_POW_general_sigma,
         FINITE_general_cross,IN_POW]
QED

(* Proof by Claude *)
Theorem basic_fusion_channel_discrete_mcchannel:
    ∀W0 W1 splitin splitout. discrete_mc W0 ∧ discrete_mc W1 ∧
        (∀x0. x0 ∈ mcdomain W0 ⇒ LENGTH x0 = splitin) ∧
        (∀y0. y0 ∈ mccodomain W0 ⇒ LENGTH y0 = splitout) ⇒
        ∀xl yls. xl ∈ mcdomain (basic_fusion_channel splitin W0 W1) ∧
            yls ∈ mcevents (basic_fusion_channel splitin W0 W1) ⇒
            mcchannel (basic_fusion_channel splitin W0 W1) xl yls =
                ∑ (λyl. mcp W0 (TAKE splitin xl) (TAKE splitout yl) *
                        mcp W1 (DROP splitin xl) (DROP splitout yl)) yls
Proof
    rpt gen_tac >> strip_tac >>
    drule_all wf_memoryless_channel_basic_fusion_channel_discrete >> strip_tac >>
    drule_all basic_fusion_channel_discrete >> strip_tac >>
    ‘mcevents W0 = POW (mccodomain W0) ∧ mcevents W1 = POW (mccodomain W1)’ by (
        imp_res_tac discrete_mc_POW_sigma_algebra >> gs[mcsigma_alt]) >>
    simp[IN_general_cross,IN_POW,PULL_EXISTS] >>
    simp[basic_fusion_channel_def,memoryless_channel_ABS_components] >>
    simp[basic_fusion_channel_rep_def,mcchannel0_def] >> rpt strip_tac >>
    ‘TAKE splitin (a ++ b) = a ∧ DROP splitin (a ++ b) = b’ by (
        res_tac >> gvs[TAKE_APPEND1,DROP_APPEND1]) >>
    ‘prob_space (mccodomain W0,POW (mccodomain W0),mcchannel W0 a) ∧
     prob_space (mccodomain W1,POW (mccodomain W1),mcchannel W1 b)’ by
        metis_tac[memoryless_channel_wf_prob_space_property,mcprob_space_alt] >>
    gs[discrete_mc_def,prob_space_def,mcp_def] >>
    irule finite_space_POW_general_prod_measure_APPEND_sum >> simp[]
QED

Definition basic_power_channel_def:
    basic_power_channel W 0 = list_lift_channel W ∧
    basic_power_channel W (SUC n) =
        basic_fusion_channel (2 ** n) (basic_power_channel W n) (basic_power_channel W n)
End

(* Prove wf *)
Definition XOR_fusion_channel_rep_def:
    XOR_fusion_channel_rep W0 W1 = (
        general_cross $++ (mcdomain W0) (mcdomain W1),
        general_sigma $++ (mcsigma W0) (mcsigma W1),
        (λa01.
            let
                a0 = TAKE ((LENGTH a01) DIV 2) a01;
                a1 = DROP ((LENGTH a01) DIV 2) a01
            in
                general_prod_measure $++
                (mccodomain W0, mcevents W0, mcchannel W0 (MAP2 BIT_XOR a0 a1))
                (mccodomain W1, mcevents W1, mcchannel W1 a1)))
End

Definition XOR_fusion_channel_def:
    XOR_fusion_channel W0 W1 = memoryless_channel_ABS
        (XOR_fusion_channel_rep W0 W1)
End

Definition XOR_power_channel_def:
    XOR_power_channel W 0 = list_lift_channel W ∧
    XOR_power_channel W (SUC n) =
        XOR_fusion_channel (XOR_power_channel W n) (XOR_power_channel W n)
End

(*** Split Channels ***)

Definition discrete_uniform_measure_space_def:
    discrete_uniform_measure_space (S:α set) = (S, POW S,
        (λs:α set. extreal_of_num (CARD s) / extreal_of_num (CARD S)))
End

Definition BIT_msp_def:
    BIT_msp = discrete_uniform_measure_space (𝕌(:BIT))
End

(* Prove wf *)
Definition negative_pole_channel_rep_def:
    negative_pole_channel_rep W = (
        mcdomain W,
        general_sigma $++ (mcsigma W) (mcsigma W),
        (λx0 ys.
            ((general_prod_measure $++
                (mccodomain W, mcevents W, mcchannel W x0)
                (mccodomain W, mcevents W, mcchannel W ZERO) ys) +
            (general_prod_measure $++
                (mccodomain W, mcevents W, mcchannel W (BIT_NOT x0))
                (mccodomain W, mcevents W, mcchannel W ONE) ys)) / 2))
End

Definition negative_pole_channel_def:
    negative_pole_channel W = memoryless_channel_ABS (negative_pole_channel_rep W)
End

(* Prove wf *)
Definition positive_pole_channel_rep_def:
    positive_pole_channel_rep W = (
        mcdomain W,
        general_sigma (CONS ∘ INL) (measurable_space BIT_msp) (general_sigma $++ (mcsigma W) (mcsigma W)),
        (λx1 x0ys. ∫⁺ BIT_msp (λx0.
            ∫⁺ (general_prod_measure_space $++
                (mccodomain W, mcevents W, mcchannel W (BIT_XOR x0 x1))
                (mccodomain W, mcevents W, mcchannel W x1))
                (λys. 𝟙 x0ys ((INL x0)::ys)))))
End

Definition positive_pole_channel_def:
    positive_pole_channel W = memoryless_channel_ABS (positive_pole_channel_rep W)
End

(*
  Note that this leads to a "backwards" polarisation list, e.g.,
  W--+, which is ((W-)-)+ has polarisation list POS::(NEG::(NEG::[]))
*)
Definition pole_channel_def:
    pole_channel [] W = list_lift_range_channel (INR_lift_channel W) ∧
    pole_channel (NEG::polet) W = negative_pole_channel (pole_channel polet W) ∧
    pole_channel (POS::polet) W = positive_pole_channel (pole_channel polet W)
End

(** dip out of msp land **)

Definition GEN_LIST_SET_DEF:
    GEN_LIST_SET s n = {l | LENGTH l = n ∧ ∀i. i < n ⇒ EL i l ∈ s}
End

(*
val _ = reveal "C";
Definition GEN_LIST_SET_DEF:
    GEN_LIST_SET s n = {l | LENGTH l = n ∧ C EL l ∈ ((count n) → s)}
End
*)

(* Proof by Claude *)
Theorem GEN_LIST_SET_1:
    ∀s. GEN_LIST_SET s 1 = IMAGE (λx. [x]) s
Proof
    simp[GEN_LIST_SET_DEF,EXTENSION] >> Cases_on ‘x’ >> simp[] >> Cases_on ‘t’ >> simp[]
QED

(* Proof by Claude *)
Theorem general_cross_APPEND_GEN_LIST_SET:
    ∀s m n. general_cross $++ (GEN_LIST_SET s m) (GEN_LIST_SET s n) = GEN_LIST_SET s (m + n)
Proof
    rw[Once EXTENSION,IN_general_cross,GEN_LIST_SET_DEF] >> eq_tac >> rw[]
    >- simp[]
    >- (rw[EL_APPEND_EQN] >> first_x_assum irule >> simp[])
    >- (qexistsl [‘TAKE m x’,‘DROP m x’] >> simp[EL_TAKE,EL_DROP])
QED

(* Proof by Claude *)
Theorem TAKE_DROP_GEN_LIST_SET:
    ∀s m n l. l ∈ GEN_LIST_SET s (m + n) ⇒
        TAKE m l ∈ GEN_LIST_SET s m ∧ DROP m l ∈ GEN_LIST_SET s n
Proof
    rw[GEN_LIST_SET_DEF,EL_TAKE,EL_DROP]
QED

(* Proof by Claude *)
Theorem FINITE_GEN_LIST_SET:
    ∀s n. FINITE s ⇒ FINITE (GEN_LIST_SET s n)
Proof
    rpt strip_tac >> Induct_on ‘n’
    >- (‘GEN_LIST_SET s 0 = {[]}’ by simp[GEN_LIST_SET_DEF,EXTENSION] >> simp[]) >>
    ‘GEN_LIST_SET s (SUC n) = general_cross $++ (GEN_LIST_SET s 1) (GEN_LIST_SET s n)’ by
        simp[general_cross_APPEND_GEN_LIST_SET,ADD1] >>
    simp[FINITE_general_cross,GEN_LIST_SET_1]
QED



(* Base case of the power channel.                                           *)
(* Proof by Claude *)
Theorem list_lift_channel_discrete:
    ∀W. discrete_mc W ⇒
        discrete_mc (list_lift_channel W) ∧
        mcdomain (list_lift_channel W) = GEN_LIST_SET (mcdomain W) 1 ∧
        mccodomain (list_lift_channel W) = GEN_LIST_SET (mccodomain W) 1 ∧
        mcevents (list_lift_channel W) = POW (GEN_LIST_SET (mccodomain W) 1) ∧
        ∀xl yl. mcp (list_lift_channel W) xl yl = mcp W (HD xl) (HD yl)
Proof
    gen_tac >> strip_tac >>
    ‘mcevents W = POW (mccodomain W)’ by (
        imp_res_tac discrete_mc_POW_sigma_algebra >> gs[mcsigma_alt]) >>
    ‘mcdomain (list_lift_channel W) = IMAGE (λa. [a]) (mcdomain W) ∧
     mccodomain (list_lift_channel W) = IMAGE (λb. [b]) (mccodomain W) ∧
     mcevents (list_lift_channel W) = IMAGE (IMAGE (λb. [b])) (POW (mccodomain W)) ∧
     ∀al bls. mcchannel (list_lift_channel W) al bls = mcchannel W (HD al) (IMAGE HD bls)’ by
        simp[list_lift_channel_def,meta_lift_channel_components] >>
    ‘discrete_mc (list_lift_channel W)’ by (
        gs[discrete_mc_def,PULL_EXISTS,IN_POW] >> rw[] >> qexists_tac ‘{b}’ >> simp[]) >>
    ‘mcevents (list_lift_channel W) = POW (mccodomain (list_lift_channel W))’ by (
        imp_res_tac discrete_mc_POW_sigma_algebra >> gs[mcsigma_alt]) >>
    simp[GEN_LIST_SET_1,mcp_def]
QED

(* The induction is carried on single-output probabilities; the event-level *)
(* statement then follows from discrete_mc_mcchannel_sum.                     *)
(* Proof by Claude *)
Theorem basic_power_channel_discrete_mcp:
    ∀W. discrete_mc W ⇒ ∀n.
        discrete_mc (basic_power_channel W n) ∧
        mcdomain (basic_power_channel W n) = GEN_LIST_SET (mcdomain W) (2 ** n) ∧
        mccodomain (basic_power_channel W n) = GEN_LIST_SET (mccodomain W) (2 ** n) ∧
        mcevents (basic_power_channel W n) = POW (GEN_LIST_SET (mccodomain W) (2 ** n)) ∧
        ∀xl yl. xl ∈ GEN_LIST_SET (mcdomain W) (2 ** n) ∧
            yl ∈ GEN_LIST_SET (mccodomain W) (2 ** n) ⇒
            mcp (basic_power_channel W n) xl yl =
                EXTREAL_PROD_IMAGE (λi. mcp W (EL i xl) (EL i yl)) (count (2 ** n))
Proof
    gen_tac >> strip_tac >> Induct
    >- simp[basic_power_channel_def,list_lift_channel_discrete] >>
    (* P (SUC n) fuses two copies of P n, splitting inputs and outputs at N.  *)
    (* Numerals are overloaded, so the arithmetic needs :num annotations.     *)
    strip_tac >> simp[basic_power_channel_def] >>
    ‘(2:num) ** SUC n = 2 ** n + 2 ** n’ by simp[EXP] >> pop_assum SUBST1_TAC >>
    qabbrev_tac ‘N = (2:num) ** n’ >> qabbrev_tac ‘P = basic_power_channel W n’ >>
    ‘∀x0. x0 ∈ mcdomain P ⇒ LENGTH x0 = N’ by simp[GEN_LIST_SET_DEF] >>
    ‘∀y0. y0 ∈ mccodomain P ⇒ LENGTH y0 = N’ by simp[GEN_LIST_SET_DEF] >>
    qspecl_then [‘P’,‘P’,‘N’] mp_tac basic_fusion_channel_discrete >> simp[] >> strip_tac >>
    qspecl_then [‘P’,‘P’,‘N’,‘N’] mp_tac basic_fusion_channel_discrete_mcchannel >>
    simp[] >> strip_tac >>
    simp[general_cross_APPEND_GEN_LIST_SET] >> rpt strip_tac >>
    gs[general_cross_APPEND_GEN_LIST_SET] >>
    qspecl_then [‘mcdomain W’,‘N’,‘N’,‘xl’] mp_tac TAKE_DROP_GEN_LIST_SET >>
    qspecl_then [‘mccodomain W’,‘N’,‘N’,‘yl’] mp_tac TAKE_DROP_GEN_LIST_SET >>
    simp[] >> rpt strip_tac >>
    ‘mcp (basic_fusion_channel N P P) xl yl =
     mcp P (TAKE N xl) (TAKE N yl) * mcp P (DROP N xl) (DROP N yl)’ by
        simp[mcp_def,EXTREAL_SUM_IMAGE_SING,IN_POW] >>
    pop_assum SUBST1_TAC >> simp[] >>
    (* Split the product over count (N + N) into its two halves. *)
    REWRITE_TAC[TIMES2,EXTREAL_PROD_IMAGE_COUNT_ADD] >> BETA_TAC >> MK_COMB_TAC
    >- (AP_TERM_TAC >> irule EXTREAL_PROD_IMAGE_EQ >> gs[GEN_LIST_SET_DEF,EL_TAKE]) >>
    irule EXTREAL_PROD_IMAGE_EQ >> gs[GEN_LIST_SET_DEF,EL_DROP]
QED

(* Proof by Claude *)
Theorem basic_power_channel_discrete:
    ∀W. discrete_mc W ⇒ ∀n.
        mcdomain (basic_power_channel W n) = GEN_LIST_SET (mcdomain W) (2 ** n) ∧
        mccodomain (basic_power_channel W n) = GEN_LIST_SET (mccodomain W) (2 ** n) ∧
        mcevents (basic_power_channel W n) = POW (GEN_LIST_SET (mccodomain W) (2 ** n)) ∧
        ∀xl yls. xl ∈ mcdomain (basic_power_channel W n) ∧
            yls ∈ mcevents (basic_power_channel W n) ⇒
            mcchannel (basic_power_channel W n) xl yls =
                EXTREAL_SUM_IMAGE (λyl. EXTREAL_PROD_IMAGE (λi. mcp W (EL i xl) (EL i yl)) (count (2 ** n))) yls
Proof
    gen_tac >> strip_tac >> gen_tac >>
    drule_then (qspec_then ‘n’ strip_assume_tac) basic_power_channel_discrete_mcp >>
    simp[] >> rpt strip_tac >>
    DEP_PURE_ONCE_REWRITE_TAC[discrete_mc_mcchannel_sum] >> simp[] >>
    irule EXTREAL_SUM_IMAGE_EQ' >> gs[IN_POW,SUBSET_DEF] >>
    metis_tac[SUBSET_FINITE,SUBSET_DEF,FINITE_GEN_LIST_SET,discrete_mc_def]
QED

(*
For XOR power channel down the line

  Definition polar_transform_def:
      polar_transform 0 l = l ∧
      polar_transform (SUC n) l =
          polar_transform n (MAP2 BIT_XOR (TAKE (2 ** n) l) (DROP (2 ** n) l)) ++
          polar_transform n (DROP (2 ** n) l)
  End

mcp W (EL i (polar_transform n xl)) (EL i yl)
*)

(* conecting to encoding *)

val _ = export_theory();
