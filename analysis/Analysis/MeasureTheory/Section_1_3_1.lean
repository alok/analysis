import Analysis.MeasureTheory.Section_1_2_3

/-!
# Introduction to Measure Theory, Section 1.3.1: Integration of simple functions

A companion to (the introduction to) Section 1.3.1 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.3.2 -/
def UnsignedSimpleFunction {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := ∃ (k:ℕ) (c: Fin k → EReal) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0) ∧ f = ∑ i, (c i) • (Real.toEReal ∘ (E i).indicator')

def RealSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := ∃ (k:ℕ) (c: Fin k → ℝ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (E i).indicator'

def ComplexSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ∃ (k:ℕ) (c: Fin k → ℝ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (Complex.ofReal ∘ (E i).indicator')

-- TODO: coercions between these concepts, and vector space structure on real and complex simple functions (and cone structure on unsigned simple functions).


@[coe]
abbrev RealSimpleFunction.toComplex {d:ℕ} (f: EuclideanSpace' d → ℝ) (df: RealSimpleFunction f) : ComplexSimpleFunction (Complex.ofReal ∘ f) := by sorry

instance RealSimpleFunction.coe_complex {d:ℕ} (f: EuclideanSpace' d → ℝ) : Coe (RealSimpleFunction f) (ComplexSimpleFunction (Complex.ofReal ∘ f)) := {
  coe := RealSimpleFunction.toComplex f
}


lemma UnsignedSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) : UnsignedSimpleFunction (f + g) := by
  sorry

lemma UnsignedSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {a: EReal} (ha: a ≥ 0) : UnsignedSimpleFunction (a • f) := by
  sorry

lemma ComplexSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hg: ComplexSimpleFunction g) : ComplexSimpleFunction (f + g) := by
  sorry

lemma ComplexSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (a: ℂ)  : ComplexSimpleFunction (a • f) := by
  sorry

lemma ComplexSimpleFunction.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ComplexSimpleFunction (fun x ↦ (starRingEnd ℂ) (f x)) := by
  sorry

noncomputable def UnsignedSimpleFunction.integral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : EReal := ∑ i, (hf.choose_spec.choose i) * Lebesgue_measure (hf.choose_spec.choose_spec.choose i)

/-- Lemma 1.3.4 (Well-definedness of simple integral) -/
lemma UnsignedSimpleFunction.integral_eq {d:ℕ} {f: EuclideanSpace' d → EReal} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {k:ℕ} {c: Fin k → EReal}
{E: Fin k → Set (EuclideanSpace' d)} (hmes: ∀ i, LebesgueMeasurable (E i)) (hnonneg: ∀ i, c i ≥ 0) (heq: f = ∑ i, (c i) • (Real.toEReal ∘ (E i).indicator')) :
 hf.integral =  ∑ i, (hf.choose_spec.choose i) * Lebesgue_measure (hf.choose_spec.choose_spec.choose i) := by sorry

/-- Definition 1.3.5 -/
def AlmostAlways {d:ℕ} (P: EuclideanSpace' d → Prop) : Prop :=
  IsNull { x | ¬ P x }

/-- Definition 1.3.5 -/
def AlmostEverywhereEqual {d:ℕ} {X: Type*} (f g: EuclideanSpace' d → X) : Prop :=
  AlmostAlways (fun x ↦ f x = g x)

/-- Definition 1.3.5 -/
def Support {X Y: Type*} [Zero Y] (f: X → Y) : Set X := { x | f x ≠ 0 }

lemma UnsignedSimpleFunction.support_measurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : LebesgueMeasurable (Support f) := by
  sorry

lemma AlmostAlways.ofAlways {d:ℕ} {P: EuclideanSpace' d → Prop} (h: ∀ x, P x) : AlmostAlways P := by
  sorry

lemma AlmostAlways.mp {d:ℕ} {P Q: EuclideanSpace' d → Prop} (hP: AlmostAlways P) (himp: ∀ x, P x → Q x) : AlmostAlways Q := by
  sorry

lemma AlmostAlways.countable {d:ℕ} {I: Type*} [Countable I] {P: I → EuclideanSpace' d → Prop} (hP: ∀ i, AlmostAlways (P i)) : AlmostAlways (fun x ↦ ∀ i, P i x) := by
  sorry

-- TODO: AlmostEverywhereEqual is an Equiv

/-- Exercise 1.3.1 (i) (Unsigned linearity) -/
lemma UnsignedSimpleFunction.integral_add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) :
  (hf.add hg).integral = hf.integral + hg.integral := by
  sorry

/-- Exercise 1.3.1 (i) (Unsigned linearity) -/
lemma UnsignedSimpleFunction.integral_smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {c:EReal} (hc: c ≥ 0) :
  (hf.smul hc).integral = c * hf.integral := by
  sorry

/-- Exercise 1.3.1 (ii) (Finiteness) -/
lemma UnsignedSimpleFunction.integral_finite_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integral < ⊤) ↔ (AlmostAlways (fun x ↦ f x < ⊤)) ∧ (Lebesgue_measure (Support f)) < ⊤ := by
  sorry

/-- Exercise 1.3.1 (iii) (Vanishing) -/
lemma UnsignedSimpleFunction.integral_eq_zero_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integral = 0) ↔ AlmostAlways (fun x ↦ f x = 0) := by
  sorry

/-- Exercise 1.3.1 (iv) (Equivalence) -/
lemma UnsignedSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostEverywhereEqual f g) :
  hf.integral = hg.integral := by
  sorry

/-- Exercise 1.3.1 (v) (Monotonicity) -/
lemma UnsignedSimpleFunction.integral_le_integral_of_aeLe {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostAlways (fun x ↦ f x ≤ g x)) :
  hf.integral ≤ hg.integral := by
  sorry

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure) -/
lemma UnsignedSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  UnsignedSimpleFunction (Real.toEReal ∘ E.indicator') := by
  sorry

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure) -/
lemma UnsignedSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  (UnsignedSimpleFunction.indicator hE).integral = Lebesgue_measure E := by
  sorry

lemma ComplexSimpleFunction.abs {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : UnsignedSimpleFunction (fun x ↦ ‖f x‖) := by
  sorry

/-- Definition 1.3.6 (Absolutely convergent simple integral) -/
def ComplexSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : Prop :=
  (hf.abs).integral < ⊤

def RealSimpleFunction.pos_part {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (Real.toEReal ∘ (max f 0)) := by sorry

def RealSimpleFunction.neg_part {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (Real.toEReal ∘ (max (-f) 0)) := by sorry

noncomputable def RealSimpleFunction.integral {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : ℝ := (hf.pos_part).integral.toReal - (hf.neg_part).integral.toReal

def ComplexSimpleFunction.re_part {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (fun x ↦ (f x).re) := by sorry

def ComplexSimpleFunction.im_part {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (fun x ↦ (f x).im) := by sorry

noncomputable def ComplexSimpleFunction.integral {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ℂ :=
  Complex.ofReal (hf.re_part).integral + Complex.I * Complex.ofReal (hf.im_part).integral

lemma ComplexSimpleFunction.absolutelyIntegrable_iff {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) :
  (hf.add hg).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) :
  (hf.smul a).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) :
  (hf.conj).AbsolutelyIntegrable := by sorry

/-- Exercise 1.3.2 (i) ({lit}``*-linearity``) -/
lemma ComplexSimpleFunction.integral_add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integral = hf.integral + hg.integral := by
  sorry

/-- Exercise 1.3.2 (i) ({lit}``*-linearity``) -/
lemma ComplexSimpleFunction.integral_smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) : (hf.smul a).integral = a * hf.integral := by
  sorry

/-- Exercise 1.3.2 (i) ({lit}``*-linearity``) -/
lemma ComplexSimpleFunction.integral_conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) : (hf.conj).integral = (starRingEnd ℂ) (hf.integral) := by
  sorry

/-- Exercise 1.3.2 (ii) (equivalence) -/
lemma ComplexSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integral = (hg.integral) := by
  sorry

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure) -/
lemma ComplexSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  ComplexSimpleFunction (Complex.ofReal ∘ E.indicator') := by
  sorry

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure) -/
lemma ComplexSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hfin: Lebesgue_measure E < ⊤): (ComplexSimpleFunction.indicator hE).integral = (Lebesgue_measure E).toReal := by
  sorry

-- TODO: analogues for the real simple integral
