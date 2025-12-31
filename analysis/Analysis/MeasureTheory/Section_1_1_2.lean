import Analysis.MeasureTheory.Section_1_1_1
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Introduction to Measure Theory, Section 1.1.2: Jordan measure

A companion to Section 1.1.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.1.4. We intend these concepts to only be applied for bounded sets `E`, but
it is convenient to permit `E` to be unbounded for the purposes of making the definitions.
-/
noncomputable abbrev Jordan_inner_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sSup { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, A ⊆ E ∧ m = hA.measure }

noncomputable abbrev Jordan_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sInf { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure }

noncomputable abbrev JordanMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  Bornology.IsBounded E ∧ Jordan_inner_measure E = Jordan_outer_measure E

noncomputable abbrev JordanMeasurable.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (_: JordanMeasurable E) : ℝ :=
  Jordan_inner_measure E

theorem JordanMeasurable.eq_inner {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_inner_measure E := rfl

theorem JordanMeasurable.eq_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_outer_measure E := by grind


/-- Various preparatory lemmas for the exercises. -/
theorem IsElementary.contains_bounded {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ A: Set (EuclideanSpace' d), IsElementary A ∧ E ⊆ A := by
  sorry

theorem Jordan_inner_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_inner_measure E := by
  sorry

theorem Jordan_outer_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_outer_measure E := by
  sorry

theorem Jordan_inner_le_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_inner_measure E ≤ Jordan_outer_measure E := by
  sorry

theorem le_Jordan_inner {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (hAE: A ⊆ E) : hA.measure ≤ Jordan_inner_measure A := by
  sorry

theorem Jordan_outer_le {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (hAE: E ⊆ A) : Jordan_outer_measure A ≤ hA.measure := by
  sorry

theorem Jordan_inner_le {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: m < Jordan_inner_measure E) : ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, A ⊆ E ∧ m < hA.measure := by
    sorry

theorem le_Jordan_outer {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: Jordan_outer_measure E < m) (hbound: Bornology.IsBounded E) :
  ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, E ⊆ A ∧ hA.measure < m := by
    sorry

/-- Exercise 1.1.5 -/
theorem JordanMeasurable.equiv {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
 [JordanMeasurable E,
  ∀ ε>0, ∃ A, ∃ B, ∃ hA: IsElementary A, ∃ hB: IsElementary B,
    A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε,
  ∀ ε>0, ∃ A, ∃ hA: IsElementary A, Jordan_outer_measure (symmDiff E A) ≤ ε].TFAE := by
  sorry

theorem IsElementary.jordanMeasurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : JordanMeasurable E := by
  sorry

theorem JordanMeasurable.mes_of_elementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : hE.jordanMeasurable.measure = hE.measure := by
  sorry

theorem JordanMeasurable.empty (d:ℕ) : JordanMeasurable (∅: Set (EuclideanSpace' d)) := by
  sorry

@[simp]
theorem JordanMeasurable.mes_of_empty (d:ℕ) : (JordanMeasurable.empty d).measure = 0 := by
  sorry


/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∪ F) := by
  sorry

lemma JordanMeasurable.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) : JordanMeasurable (⋃ E ∈ S, E) := by sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.inter {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∩ F) := by
  sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.sdiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E \ F) := by
  sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.symmDiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (symmDiff E F) := by
  sorry

/-- Exercise 1.1.6 (ii) (non-negativity) -/
theorem JordanMeasurable.nonneg {d:ℕ} {E : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) : 0 ≤ hE.measure := by
  sorry

/-- Exercise 1.1.6 (iii) (finite additivity) -/
theorem JordanMeasurable.mes_of_disjUnion {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: Disjoint E F)
  : (hE.union hF).measure = hE.measure + hF.measure := by
  sorry

/-- Exercise 1.1.6 (iii) (finite additivity) -/
lemma JordanMeasurable.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E)
(hdisj: (S : Set (Set (EuclideanSpace' d))).PairwiseDisjoint id):
  (JordanMeasurable.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  sorry

/-- Exercise 1.1.6 (iv) (monotonicity) -/
theorem JordanMeasurable.mono {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: E ⊆ F)
  : hE.measure ≤ hF.measure := by
  sorry

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
theorem JordanMeasurable.mes_of_union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  : (hE.union hF).measure ≤ hE.measure + hF.measure := by
  sorry

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
lemma JordanMeasurable.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) :
  (JordanMeasurable.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  sorry

open Pointwise

/-- Exercise 1.1.6 (vi) (translation invariance) -/
theorem JordanMeasurable.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (x: EuclideanSpace' d) : JordanMeasurable (E + {x}) := by
  sorry

/-- Exercise 1.1.6 (vi) (translation invariance) -/
lemma JordanMeasurable.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: JordanMeasurable E) (x: EuclideanSpace' d):
  (hE.translate x).measure ≤ hE.measure := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : JordanMeasurable { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.measure_of_graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : (JordanMeasurable.graph hf).measure = 0 := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.undergraph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : JordanMeasurable { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by
  sorry

/-- Exercise 1.1.8 -/
lemma JordanMeasurable.triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : JordanMeasurable T.closedInterior := by
  sorry

abbrev EuclideanSpace'.plane_wedge (x y: EuclideanSpace' 2) := x 1 * y 0 - x 0 * y 1

/-- Exercise 1.1.8 -/
lemma JordanMeasurable.measure_triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : (JordanMeasurable.triangle T).measure = |(T.points 1 - T.points 0).plane_wedge (T.points 2 - T.points 0)| / 2 := by
  sorry

/-- Exercise 1.1.9 -/

abbrev IsPolytope {d:ℕ} (P: Set (EuclideanSpace' d)) : Prop :=
  ∃ (V: Finset (EuclideanSpace' d)), P = convexHull ℝ (V : Set (EuclideanSpace' d))

lemma JordanMeasurable.polytope {d:ℕ} {P: Set (EuclideanSpace' d)} (hP: IsPolytope P) : JordanMeasurable P := by
  sorry

/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.ball {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.ball x₀ r) := by
  sorry

/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.closedBall x₀ r) := by
  sorry


/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.measure_ball (d:ℕ) : ∃ c, ∀ (x₀: EuclideanSpace' d) (r: ℝ) (hr: 0 < r), (ball x₀ hr).measure = c * r^d := by sorry

lemma JordanMeasurable.measure_closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r): (closedBall x₀ hr).measure = (ball x₀ hr).measure := by sorry

/-- Exercise 1.1.10 (2) -/
lemma JordanMeasurable.measure_ball_le (d:ℕ) : (measure_ball d).choose ≤ 2^d := by sorry

/-- Exercise 1.1.10 (2) -/
lemma JordanMeasurable.le_measure_ball (d:ℕ) : 2^d/d.factorial ≤ (measure_ball d).choose := by sorry

/-- Exercise 1.1.11 (1) -/
lemma JordanMeasurable.linear_of_elem {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: IsElementary E): JordanMeasurable (T '' E) := by
  sorry

/-- Exercise 1.1.11 (1) -/
lemma JordanMeasurable.measure_linear_of_elem {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d) : ∃ D > 0, ∀ (E: Set (EuclideanSpace' d)) (hE: IsElementary E), (linear_of_elem T hE).measure = D * hE.measure := by sorry

/-- Exercise 1.1.11 (2) -/
lemma JordanMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E): JordanMeasurable (T '' E) := by
  sorry

/-- Exercise 1.1.11 (2) -/
lemma JordanMeasurable.measure_linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d) :
∃ D > 0, ∀ (E: Set (EuclideanSpace' d)) (hE: JordanMeasurable E), (linear T hE).measure = hE.measure := by sorry

-- TODO: Fix after mathlib 4.26 upgrade - toLin' type changed for EuclideanSpace
noncomputable def Matrix.linear_equiv {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A] :
EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d := by
  sorry

/-- Exercise 1.1.11 (3) -/
lemma JordanMeasurable.measure_linear_det {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A] :
(measure_linear A.linear_equiv).choose = |A.det| := by sorry

abbrev JordanMeasurable.null {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ hE: JordanMeasurable E, hE.measure = 0

lemma JordanMeasurable.null_iff {d:ℕ} {E: Set (EuclideanSpace' d)} : null E ↔ Bornology.IsBounded E ∧ Jordan_outer_measure E = 0 := by
  sorry

/-- Exercise 1.1.12 -/
lemma JordanMeasurable.null_mono {d:ℕ} {E F: Set (EuclideanSpace' d)} (h: null E) (hEF: E ⊆ F) : null F := by
  sorry

/-- Exercise 1.1.13 -/
-- TODO: Fix type mismatch - E is Set (EuclideanSpace' d) but Set.range gives Set (Fin d → ℝ)
axiom JordanMeasure.measure_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E):
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥((fun x : EuclideanSpace' d => (x : Fin d → ℝ)) '' E ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds hE.measure)

noncomputable abbrev Box.dyadic {d:ℕ} (n:ℤ) (i:Fin d → ℤ) : Box d where
  side j := BoundedInterval.Ico ((i j)/2^n) ((i j + 1)/2^n)

noncomputable abbrev metric_entropy_lower {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ⊆ E }

noncomputable abbrev metric_entropy_upper {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ∩ E ≠ ∅ }

/-- Exercise 1.1.14 -/
theorem JordanMeasure.iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  JordanMeasurable E ↔ Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * ((metric_entropy_upper E n - metric_entropy_lower E n))) (nhds 0) := by sorry

theorem JordanMeasure.eq_lim_lower {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower E n)) (nhds hE.measure) := by sorry

theorem JordanMeasure.eq_lim_upper {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n)) (nhds hE.measure) := by sorry

/-- Exercise 1.1.15 (Uniqueness of Jordan measure) -/
theorem JordanMeasure.measure_uniq {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = c * hE.measure := by
    sorry

theorem JordanMeasure.measure_uniq' {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _).jordanMeasurable = 1) :
  ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = hE.measure := by
    sorry


/-- Exercise 1.1.16 -/
theorem JordanMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂) : JordanMeasurable (EuclideanSpace'.prod E₁ E₂) := by sorry

theorem JordanMeasurable.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by sorry

-- TODO: Fix after mathlib 4.26 upgrade - toLin' type changed for EuclideanSpace
abbrev Isometric {d:ℕ} (E F: Set (EuclideanSpace' d)) : Prop :=
 ∃ A ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∃ x₀, F = (EuclideanSpace.equiv (Fin d) ℝ).symm '' ((Matrix.toLin' A) '' ((EuclideanSpace.equiv (Fin d) ℝ) '' E)) + {x₀}

/-- Exercise 1.1.17 -/
theorem JordanMeasurable.measure_of_equidecomposable {d n:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  {P Q: Fin n → Set (EuclideanSpace' d)} (hPQ: ∀ i, Isometric (P i) (Q i))
  (hPE: E = ⋃ i, P i) (hQF: F = ⋃ i, Q i) (hPdisj: Set.PairwiseDisjoint .univ P)
  (hQdisj: Set.PairwiseDisjoint .univ (fun i ↦ (interior (Q i)))) : hE.measure = hF.measure := by
  sorry

/-- Exercise 1.1.18 (1) -/
theorem JordanMeasurable.outer_measure_of_closure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  Jordan_outer_measure (closure E) = Jordan_outer_measure E := by sorry

/-- Exercise 1.1.18 (2) -/
theorem JordanMeasurable.inner_measure_of_interior {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  Jordan_inner_measure (interior E) = Jordan_inner_measure E := by sorry

/-- Exercise 1.1.18 (3) -/
theorem JordanMeasurable.iff_boundary_null {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  JordanMeasurable E ↔ JordanMeasurable.null (frontier E) := by sorry

abbrev bullet_riddled_square : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∉ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

abbrev bullets : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∈ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

theorem bullet_riddled_square.inner : Jordan_inner_measure bullet_riddled_square = 0 := by sorry

theorem bullet_riddled_square.outer : Jordan_outer_measure bullet_riddled_square = 1 := by sorry

theorem bullets.inner : Jordan_inner_measure bullets = 0 := by sorry

theorem bullets.outer : Jordan_outer_measure bullets = 1 := by sorry

theorem bullet_riddled_square.not_jordanMeasurable : ¬ JordanMeasurable bullet_riddled_square := by sorry

theorem bullets.not_jordanMeasurable : ¬ JordanMeasurable bullets := by sorry

/-- Exercise 1.1.19 (Caratheodory property) -/
theorem JordanMeasurable.caratheodory {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) (hF: IsElementary F) :
  Jordan_outer_measure E = Jordan_outer_measure (E ∩ F) + Jordan_outer_measure (E \ F) := by
  sorry
