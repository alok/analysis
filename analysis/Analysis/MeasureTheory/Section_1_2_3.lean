import Analysis.MeasureTheory.Section_1_2_2

/-!
# Introduction to Measure Theory, Section 1.2.3: Non-measurable sets

A companion to (the introduction to) Section 1.2.3 of the book "An introduction to Measure Theory".

-/

/-- Proposition 1.2.18 -/
theorem LebesgueMeasurable.nonmeasurable : ∃ E : Set (EuclideanSpace' 1), E ⊆ EuclideanSpace'.equiv_Real.symm '' (Set.Icc 0 1) ∧ ¬ LebesgueMeasurable E := by
  sorry

/-- Exercise 1.2.26 (Outer measure is not finitely additive)-/
example : ∃ E F : Set (EuclideanSpace' 1), E ∩ F = ∅ ∧ Bornology.IsBounded E ∧ Bornology.IsBounded F ∧ Lebesgue_outer_measure (E ∪ F) ≠ Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
  sorry

/-- Exercise 1.2.27 (Projections of measurable sets need not be measurable) -/
example : ∃ E : Set (EuclideanSpace' 2), LebesgueMeasurable E ∧ ¬ LebesgueMeasurable ((fun x ↦ EuclideanSpace'.equiv_Real.symm (x 0)) '' E) := by sorry
