import Analysis.MeasureTheory.Section_1_1_3

/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.1 -/
example : ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
  (∀ n, JordanMeasurable (EuclideanSpace'.equiv_Real.symm '' (E n)))
  ∧ ¬ JordanMeasurable (⋃ n, EuclideanSpace'.equiv_Real.symm '' (E n)) := by
  sorry

/-- Exercise 1.2.1 -/
example : ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
  (∀ n, JordanMeasurable (EuclideanSpace'.equiv_Real.symm '' (E n)))
  ∧ ¬ JordanMeasurable (⋂ n, EuclideanSpace'.equiv_Real.symm '' (E n)) := by
  sorry

/-- Exercise 1.2.2 -/
example : ∃ f: ℕ → ℝ → ℝ, ∃ F: ℝ → ℝ, ∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M ∧
    (∀ x ∈ Set.Icc 0 1, Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (F x))) ∧
    (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) ∧
    ¬ RiemannIntegrableOn F (Icc 0 1) := by
  sorry

/-- Exercise 1.2.2 -/
def Ex_1_2_2b : Decidable ( ∀ f: ℕ → ℝ → ℝ, ∀ F: ℝ → ℝ, (∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M) → (∀ x ∈ Set.Icc 0 1, TendstoUniformly f F Filter.atTop) → (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) → RiemannIntegrableOn F (Icc 0 1) ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  sorry

theorem Jordan_inner_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_inner_measure E = sInf (((fun S: Finset (Box d) ↦ S.sum Box.volume)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) := by
  sorry

noncomputable def Lebesgue_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal :=
  sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })

theorem Lebesgue_outer_measure_le_Jordan {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Lebesgue_outer_measure E ≤ Jordan_outer_measure E := by
  sorry

/-- Example 1.2.1. With the junk value conventions of this companion, the Jordan outer measure of the rationals is zero rather than infinite (I think). -/
example {R:ℝ} (hR: 0 < R) : Jordan_outer_measure (EuclideanSpace'.equiv_Real.symm '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 2*R := by
  sorry

theorem Countable.Lebesgue_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: E.Countable) : Lebesgue_outer_measure E = 0 := by
  sorry

example {R:ℝ} (hR: 0 < R) : Lebesgue_outer_measure (EuclideanSpace'.equiv_Real.symm '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  sorry

example {R:ℝ} (hR: 0 < R) : Lebesgue_outer_measure (EuclideanSpace'.equiv_Real.symm '' (Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  sorry

def LebesgueMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  ∀ ε > 0, ∃ U: Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε

noncomputable def Lebesgue_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal := Lebesgue_outer_measure E
