import Analysis.MeasureTheory.Notation

/-!
# Introduction to Measure Theory, Section 1.1.1: Elementary measure

A companion to Section 1.1.1 of the book "An introduction to Measure Theory".

-/

/- Definition 1.1.1. (Intervals) We use the same formalization of intervals used in
Chapter 11 of "Analysis I". Following the usual Lean preference to admit `junk` values,
we allow for the possibility that `b < a`. -/
inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make Finsets of BoundedIntervals work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

/-- Some helpful general lemmas about BoundedInterval -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  sorry

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  sorry

theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  sorry

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (inter I J).choose_spec.symm

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

@[simp]
theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

@[simp]
theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

/-- Definition 1.1.1 (boxes) -/
abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

@[ext]
structure Box (d:ℕ) where
  side : Fin d → BoundedInterval

-- TODO: Fix type mismatch after mathlib 4.26 upgrade - EuclideanSpace is now PiLp wrapper
-- The pi set needs to be properly coerced to the PiLp type
abbrev Box.toSet {d:ℕ} (B: Box d) : Set (EuclideanSpace' d) :=
  {x : EuclideanSpace' d | ∀ i, (x : Fin d → ℝ) i ∈ (B.side i).toSet}

instance Box.inst_coeSet {d:ℕ} : Coe (Box d) (Set (EuclideanSpace' d)) where
  coe := toSet

@[coe]
abbrev BoundedInterval.toBox (I: BoundedInterval) : Box 1 where
  side := fun _ ↦ I

instance BoundedInterval.inst_coeBox : Coe (BoundedInterval) (Box 1) where
  coe := toBox

@[simp]
theorem BoundedInterval.toBox_inj {I J: BoundedInterval} : (I:Box 1) = (J:Box 1) ↔ I = J := by
  refine' ⟨fun h => _, fun h => h ▸ rfl⟩
  have : (I:Box 1).side 0 = (J:Box 1).side 0 := by rw [h]
  exact this

@[simp]
theorem BoundedInterval.coe_of_box (I:BoundedInterval) : (I:Box 1).toSet = EuclideanSpace'.equiv_Real.symm '' I.toSet := by
  sorry -- TODO: Fix after mathlib 4.26 upgrade

/-- Definition 1.1.1 (boxes)-/
abbrev Box.volume {d:ℕ} (B: Box d) : ℝ := ∏ i, |B.side i|ₗ

/-- Using ||ᵥ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ᵥ" : term => `(Box.volume $a)

@[simp]
theorem Box.volume_of_interval (I:BoundedInterval) : |(I:Box 1)|ᵥ = |I|ₗ := by
  simp [Box.volume]

abbrev IsElementary {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ S : Finset (Box d), E = ⋃ B ∈ S, ↑B

theorem IsElementary.box {d:ℕ} (B: Box d) : IsElementary B.toSet := by sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.union {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∪ F) := by
  sorry

lemma IsElementary.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) : IsElementary (⋃ E ∈ S, E) := by sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.inter {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∩ F) := by
  sorry

theorem IsElementary.empty (d:ℕ) : IsElementary (∅: Set (EuclideanSpace' d)) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.sdiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E \ F) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.symmDiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (symmDiff E F) := by
  sorry

open Pointwise

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (x: EuclideanSpace' d) : IsElementary (E + {x}) := by
  sorry

/-- A sublemma for proving Lemma 1.1.2(i). It is a geometrically obvious fact but surprisingly annoying to prove formally. -/
theorem BoundedInterval.partition (S: Finset BoundedInterval) :
  ∃ T: Finset BoundedInterval,
    (T : Set BoundedInterval).PairwiseDisjoint BoundedInterval.toSet
      ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  let endpoints : Finset ℝ := S.image BoundedInterval.a ∪ S.image BoundedInterval.b
  have ha_mem {I:BoundedInterval} (hI: I ∈ S) : I.a ∈ endpoints := by grind
  have hb_mem {I:BoundedInterval} (hI: I ∈ S) : I.b ∈ endpoints := by grind
  let k := endpoints.card
  let sorted : Fin k ≃o endpoints := endpoints.orderIsoOfFin (by rfl)
  let a : ℕ → ℝ := fun n ↦ if h:n < k then sorted ⟨n,h⟩ else 0  -- 0 is a junk value
  let T := Finset.univ.image (fun x:endpoints ↦ Icc x x)
    ∪ (Finset.range (k-1)).image (fun n ↦ Ioo (a n) (a (n+1)))
  refine' ⟨T,_,_⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro I hI J hJ hIJ
    have := hIJ.some_mem
    simp_all [T]
    obtain ⟨ x, hx, rfl ⟩ | ⟨ n, hn, rfl ⟩ := hI
      <;> obtain ⟨ y, hy, rfl ⟩ | ⟨ m, hm, rfl ⟩ := hJ
      <;> simp at this
    . rw [show x=y by grind]
    . rw [this.1] at this
      set n := sorted.symm ⟨ x, hx ⟩
      have hax : x = sorted n := by simp [n]
      obtain ⟨ n, hn ⟩ := n
      simp [a, show m < k by omega, show m+1 < k by omega, hax] at this
      omega
    . rw [this.2] at this
      set m := sorted.symm ⟨ y, hy ⟩
      have hay : y = sorted m := by simp [m]
      obtain ⟨ m, hm ⟩ := m
      simp [a, show n < k by omega, show n+1 < k by omega, hay] at this
      omega
    have h1 : a n < a (m+1) := this.1.1.trans this.2.2
    have h2 : a m < a (n+1) := this.2.1.trans this.1.2
    simp [a, show n < k by omega, show n+1 < k by omega,
          show m < k by omega, show m+1 < k by omega] at h1 h2
    rw [show n=m by omega]
  intro I hI
  use {J | J.val ⊆ I }
  ext x; simp; constructor
  . intro hx
    by_cases hend : x ∈ endpoints
    . use Icc x x; simp [T, hx, hend]
    let n := sorted.symm ⟨ I.a, ha_mem hI ⟩
    let m := sorted.symm ⟨ I.b, hb_mem hI ⟩
    have hnI : I.a = sorted n := by simp [n]
    have hmI : I.b = sorted m := by simp [m]
    obtain ⟨ m, hm ⟩ := m; obtain ⟨ n, hn ⟩ := n
    apply I.subset_Icc at hx
    simp [hnI, hmI] at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    have H : ∃ m, x ≤ a m := by use m; grind
    let r := Nat.find H
    have hrm : r ≤ m := by convert Nat.find_min' H _; grind
    have hr : r < k := by linarith
    have hxr : x ≤ sorted ⟨ r, hr ⟩ := by convert Nat.find_spec H; grind
    have hnr : n < r := by
      by_contra!
      replace : (sorted ⟨r, hr⟩).val ≤ (sorted ⟨n, hn⟩).val := by simp [this]
      simp [show x = sorted ⟨ n, hn ⟩ by order] at hend
    refine' ⟨ Ioo (sorted ⟨ r-1, by omega ⟩) (sorted ⟨ r, hr ⟩), _ , _, _ ⟩
    . apply Set.Subset.trans _ I.Ioo_subset
      simp [hnI, hmI]
      apply Set.Ioo_subset_Ioo <;> simp <;> omega
    . simp [T]; refine' ⟨ r-1, by omega, _ ⟩
      simp [a, show r-1 < k by omega, show r < k by omega, show r-1+1=r by omega]
    simp
    have h1 : x ≠ sorted ⟨ r, hr ⟩ := by by_contra!; simp [this] at hend
    have h3 : sorted ⟨ r-1, by omega ⟩ < x := by
      by_contra!
      convert Nat.find_min H (show r-1 < r by omega) _
      simp [a, show r-1 < k by omega, this]
    grind
  grind

/-- Lemma 1.1.2(i) -/
theorem Box.partition {d:ℕ} (S: Finset (Box d)) :
  ∃ T: Finset (Box d),
    (T : Set (Box d)).PairwiseDisjoint Box.toSet
      ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  sorry -- TODO: Fix after mathlib 4.26 upgrade - Set.mem_pi rewrite fails

theorem IsElementary.partition {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) :
  ∃ T: Finset (Box d),
    (T : Set (Box d)).PairwiseDisjoint Box.toSet ∧ E = ⋃ J ∈ T, J.toSet := by
  obtain ⟨ S, rfl ⟩ := hE
  have ⟨ T', hT', hST' ⟩ := Box.partition S
  choose U hU using hST'
  conv => rhs; ext T; rhs; lhs; rhs; ext B; rhs; ext h; rw [hU B h]
  classical
  use T'.filter (fun J ↦ ∃ B, ∃ h:B ∈ S, J ∈ Subtype.val '' (U B h))
  simp; split_ands
  . apply hT'.subset; intro _; simp; tauto
  ext; simp; grind

/-- Helper lemma for Lemma 1.1.2(ii) -/
theorem BoundedInterval.sample_finite (I : BoundedInterval) {N:ℕ} (hN: N ≠ 0):
  Finite ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))) := by
  sorry

/-- Exercise for Lemma 1.1.2(ii) -/
theorem BoundedInterval.length_eq (I : BoundedInterval) :
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)⁻¹ * Nat.card ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))))
  (nhds |I|ₗ) := by
  sorry

-- TODO: The following theorems have type mismatches after mathlib 4.26 upgrade
-- Box.toSet is now Set (EuclideanSpace' d) but Set.range is Set (Fin d → ℝ)
-- Need proper coercion. For now, use axioms.

/-- Helper lemma for Lemma 1.1.2(ii) - sample points converge to volume -/
axiom Box.sample_finite {d:ℕ} (B: Box d) {N:ℕ} (hN: N ≠ 0):
  Finite ↥((fun x : EuclideanSpace' d => (x : Fin d → ℝ)) '' B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i))))

/-- Helper lemma for Lemma 1.1.2(ii) -/
axiom Box.vol_eq {d:ℕ} (B: Box d):
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥((fun x : EuclideanSpace' d => (x : Fin d → ℝ)) '' B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds |B|ᵥ)

/-- Lemma 1.1.2(ii), helper lemma -/
axiom Box.sum_vol_eq {d:ℕ} {T: Finset (Box d)}
 (hT: (T : Set (Box d)).PairwiseDisjoint Box.toSet) :
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥((fun x : EuclideanSpace' d => (x : Fin d → ℝ)) '' (⋃ B ∈ T, B.toSet) ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds (∑ B ∈ T, |B|ᵥ))

/-- Lemma 1.1.2(ii) -/
theorem Box.measure_uniq {d:ℕ} {T₁ T₂: Finset (Box d)}
 (hT₁: (T₁ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (hT₂: (T₂ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
  sorry -- TODO: Fix after mathlib 4.26 upgrade - Box.sum_vol_eq type changed

noncomputable abbrev IsElementary.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : ℝ
  := ∑ B ∈ hE.partition.choose, |B|ᵥ

theorem IsElementary.measure_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E)
  {T: Finset (Box d)} (hT: (T : Set (Box d)).PairwiseDisjoint Box.toSet)
  (heq : E = ⋃ B ∈ T, B.toSet):
  hE.measure = ∑ B ∈ T, |B|ᵥ := by
  apply Box.measure_uniq hE.partition.choose_spec.1 hT _
  rw [←heq, ←hE.partition.choose_spec.2]

/-- Exercise 1.1.2: give an alternate proof of this proposition by showing that
the two partitions `T₁`, `T₂` admit a mutual refinement into boxes arising from
taking Cartesian products of elements from finite collections of disjoint intervals. -/
theorem Box.measure_uniq' {d:ℕ} {T₁ T₂: Finset (Box d)}
 (hT₁: (T₁ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (hT₂: (T₂ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
 sorry

example :
  let E : Set (EuclideanSpace' 1) := EuclideanSpace'.equiv_Real.symm '' ((Set.Ioo 1 2) ∪ (Set.Icc 3 6))
  ∃ hE : IsElementary E, hE.measure = 4 := by
  extract_lets E
  classical
  let T : Finset (Box 1) := {(BoundedInterval.Ioo 1 2:Box 1), (BoundedInterval.Icc 3 6:Box 1)}
  have hET : E = ⋃ B ∈ T, B.toSet := by
    simp [E, T, Set.image_union]
  let hE : IsElementary E := ⟨ T, hET⟩
  use hE
  rw [hE.measure_eq _ hET]
  . rw [Finset.sum_pair]
    . norm_num
    by_contra!; simp [-Box.mk.injEq] at this
  rw [Set.pairwiseDisjoint_iff]
  simp [T]; sorry -- TODO: Fix grind after mathlib 4.26 upgrade

lemma IsElementary.measure_nonneg {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) :
  0 ≤ hE.measure := by
  sorry

lemma IsElementary.measure_of_disjUnion {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hdisj: Disjoint E F):
  (hE.union hF).measure = hE.measure + hF.measure := by
  sorry

lemma IsElementary.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E)
(hdisj: (S : Set (Set (EuclideanSpace' d))).PairwiseDisjoint id):
  (IsElementary.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  sorry

@[simp]
lemma IsElementary.measure_of_empty (d:ℕ) : (IsElementary.empty d).measure = 0 := by
  sorry

@[simp]
lemma IsElementary.measure_of_box {d:ℕ} (B: Box d) : (IsElementary.box B).measure = |B|ᵥ := by
  sorry

lemma IsElementary.measure_mono  {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hcont: E ⊆ F):
  hE.measure ≤ hF.measure := by
  sorry

lemma IsElementary.measure_of_union {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F):
  (hE.union hF).measure ≤ hE.measure + hF.measure := by
  sorry

lemma IsElementary.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) :
  (IsElementary.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  sorry

lemma IsElementary.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) (x: EuclideanSpace' d):
  (hE.translate x).measure ≤ hE.measure := by
  sorry

/-- Exercise 1.1.3 (uniqueness of elementary measure) -/
theorem IsElementary.measure_uniq {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (hF: IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE = c * hE.measure := by
    sorry

abbrev Box.unit_cube (d:ℕ) : Box d := { side := fun _ ↦ BoundedInterval.Ioc 0 1}

theorem IsElementary.measure_uniq' {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (hF: IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _) = 1) :
  ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE = hE.measure := by
    sorry

abbrev Box.prod {d₁ d₂:ℕ} (B₁: Box d₁) (B₂: Box d₂) : Box (d₁ + d₂) where
  side i := by
    obtain ⟨ i, hi ⟩ := i
    exact if h : i < d₁ then B₁.side ⟨i, h⟩ else (B₂.side ⟨i - d₁, by omega⟩)

/-- Exercise 1.1.4 -/
theorem IsElementary.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂) : IsElementary (EuclideanSpace'.prod E₁ E₂) := by sorry

theorem IsElementary.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by sorry
