import Mathlib

/-! Formalizing a proof (the prime case of) Erdos problem \#707 recently proven by Alexeev, ChatGPT, Lean, and Mixon at https://borisalexeev.com/papers/erdos707.html, following Theorem 8 proven on page 5 -/

/-- A perfect difference set is a set where every nonzero element is uniquely representable as a difference of two elements of the set. -/
def IsPerfectDifferenceSet {N: ℕ} (B: Finset (ZMod N)) := ∀ d: ZMod N, d ≠ 0 → ∃! b: B × B, b.1.val - b.2.val = d


/-- We will show that the following hypotheses are inconsistent; this is the bulk of the proof of Theorem 8. -/
class Hypotheses where
  N : ℕ
  hodd: Odd N
  B: Finset (ZMod N)
  hdiff: IsPerfectDifferenceSet B
  heven: Even B.card
  h1: 1 ∈ B
  h2: 2 ∈ B
  h4: 4 ∈ B
  h8: 8 ∈ B
  h2_ne_1: (2: ZMod N) ≠ (1: ZMod N)
  h4_ne_1: (4: ZMod N) ≠ (1: ZMod N)
  h4_ne_8: (4: ZMod N) ≠ (8: ZMod N)

export Hypotheses (N hodd B hdiff heven h1 h2 h4 h8 h2_ne_1 h4_ne_1 h4_ne_8)

variable [Hypotheses]

lemma mul_two_inj {x y: ZMod N} (h: 2 * x = 2 * y) : x = y := by
  apply IsUnit.mul_left_cancel _ h
  convert (ZMod.isUnit_prime_iff_not_dvd (n := N) Nat.prime_two).mpr _
  exact Odd.not_two_dvd_nat hodd

lemma diff_uniq {a b c d:B} (ha: a ≠ b) (hsub: a.val-b.val = c.val-d.val) : a=c ∧ b=d := by
  have := hdiff (a-b) (by grind)
  replace : (⟨ a, b ⟩: B × B) = ⟨ c, d ⟩ := by apply this.unique <;> grind
  grind

/-- Given a perfect difference set {lit}``B`` and an element {lit}``a`` not in {lit}``B``, the function {lit}``f_a`` maps each {lit}``b ∈ B`` to the unique {lit}``c ∈ B`` such that {lit}``a-b=c-d`` for some {lit}``d ∈ B``. -/
noncomputable def f {a:ZMod N} (ha: a ∉ B) (b:B): B :=
    (hdiff (a-b.val) (by grind)).choose.1

/-- Though not defined in Theorem 8, it is convenient to also introduce the companion function {lit}``g_a``, defined to be the {lit}``d`` element. -/
noncomputable def g {a:ZMod N} (ha: a ∉ B) (b:B): B :=
    (hdiff (a-b.val) (by grind)).choose.2

lemma f_def {a:ZMod N} (ha: a ∉ B) (b:B) : a - b = f ha b - g ha b := by
  convert (hdiff (a - b.val) (by grind)).choose_spec.1.symm

lemma f_def' {a:ZMod N} (ha: a ∉ B) (b c d:B) : a - b = c - d ↔ c = f ha b ∧ d = g ha b := by
  constructor
  . intro h
    rw [f_def ha b] at h; symm at h
    apply diff_uniq _ h
    rw [←f_def ha b] at h
    grind
  rintro ⟨ rfl, rfl ⟩
  exact f_def ha b

/-- {lit}``f_a`` is an involution. -/
lemma f_inv {a:ZMod N} (ha: a ∉ B) : Function.Involutive (f ha) := by
  intro b
  have h1 := f_def ha b
  replace h1 : a - (f ha b) = b - (g ha b) := by grind
  rw [f_def' ha] at h1
  rw [←h1.1]

/-- Fixed points of {lit}``f_a`` satisfy {lit}``2f_a(b) = a + g_a(b)``. -/
lemma f_fixed {a:ZMod N} {ha: a ∉ B} {b:B} (hb: f ha b = b): 2 * b.val = a + (g ha b).val := by
  have := f_def ha b
  grind


noncomputable def z2_vact {a:ZMod N} (ha: a ∉ B) : AddAction (ZMod 2) B :=
{
  vadd i b := if i=1 then f ha b else b
  zero_vadd b := by
    change (if (0: ZMod 2) = 1 then f ha b else b) = b
    simp
  add_vadd i j b := by
    change (if i + j = 1 then f ha b else b) = if i = 1 then f ha (if j = 1 then f ha b else b) else (if j = 1 then f ha b else b)
    fin_cases i <;> fin_cases j <;> simp
    exact (f_inv ha b).symm
}

/-- If there is one fixed point, there is another. -/
lemma f_second_fixed {a:ZMod N} {ha: a ∉ B} {b:B} (hb: f ha b = b) : ∃ c:B, c ≠ b ∧ f ha c = c := by
  let action := z2_vact ha
  classical
  have := action.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup _ _
  simp only [ZMod.card] at this
  set N :=  Fintype.card (Quotient (action.orbitRel (ZMod 2) { x // x ∈ B }))
  set S := action.fixedBy { x // x ∈ B } 1
  replace := calc
    N * 2 = ∑ a, Fintype.card (action.fixedBy { x // x ∈ B } a) := this.symm
    _ = Fintype.card (action.fixedBy { x // x ∈ B } 0) + Fintype.card S := by
      convert Fin.sum_univ_two _
    _ = B.card + Fintype.card S := by simp
  replace : Even (Fintype.card S) := by
    apply (Nat.even_add.mp ?_).mp heven
    rw [←this]
    grind
  have hs : b ∈ S := by
    change (if (1: ZMod 2) = 1 then f ha b else b) = b
    simp [hb]
  have c1 : Fintype.card S ≥ 1 := by
    simp; use b; simp [hs]
  replace c1 : Fintype.card S ≥ 2 := by grind
  have c2 : S ≠ {b} := by
    contrapose! c1
    simp [c1]
  have c3 : ∃ c:B, c ∈ S ∧ c ≠ b := by
    simp at c2
    grind
  obtain ⟨ c, hc ⟩ := c3
  use c; simp [hc]
  simp [S] at hc
  replace hc := hc.1
  change (if (1: ZMod 2) = 1 then f ha c else c) = c at hc
  simp_all

lemma two_mul_sub_one_notin {x:B} (hx: x.val ≠ 2) : 2 * (x.val - 1) ∉ B := by
  by_contra! this
  replace := diff_uniq (a:= x) (b := ⟨ 2,h2 ⟩) (c := ⟨_,this⟩) (d:=x) (by grind) (by grind)
  grind

lemma first_fixed {x:B} (hx: x.val ≠ 2) : f (two_mul_sub_one_notin hx) x = x := by
  convert ((f_def' (two_mul_sub_one_notin hx) x x ⟨ 2, h2⟩).mp ?_).1.symm
  grind

lemma second_fixed {x:B} (hx: x.val ≠ 2) : ∃ b, b ≠ x ∧ f (two_mul_sub_one_notin hx) b = b :=  f_second_fixed (first_fixed hx)

noncomputable def b (x:B) := if hx: x.val = 2 then ⟨ 2, h2 ⟩ else (second_fixed hx).choose

noncomputable def d (x:B) := if hx: x.val = 2 then ⟨ 2, h2 ⟩ else g (two_mul_sub_one_notin hx) (second_fixed hx).choose

lemma b_neq {x:B} (hx: x.val ≠ 2) : b x ≠ x := by
  simp [b, hx]
  convert (second_fixed hx).choose_spec.1

lemma bd_ident (x:B) : 2 * (b x).val = 2 * (x.val - 1) + (d x).val := by
  by_cases hx: x.val = 2
  · simp [b,d,hx]; ring
  · simp [b, d, hx]
    convert f_fixed _ using 2
    convert (second_fixed hx).choose_spec.2

lemma d_injective : Function.Injective d := by
  intro x x' h
  have h1 := bd_ident x
  have h2 := bd_ident x'
  have h3 : 2 * ((b x).val - b x') = 2 * (x - x') := by grind
  replace h3 := (mul_two_inj h3).symm
  by_contra! this
  replace h3 := diff_uniq this h3
  have h4 := b_neq (x := x)
  have h5 := b_neq (x := x')
  grind

lemma d_surjective : Function.Surjective d := Finite.surjective_of_injective d_injective

lemma d1_eq_4 : d ⟨ 1, h1 ⟩ = ⟨ 4, h4 ⟩ := by
  obtain ⟨ x, hx ⟩ := d_surjective ⟨ 4, h4 ⟩
  have := bd_ident x
  simp [hx] at this
  replace : 2 * (b x).val = 2 * (x.val + 1) := by grind
  replace := mul_two_inj this
  convert hx
  convert congrArg Subtype.val (diff_uniq ?_ ?_ (a := ⟨ 2, h2 ⟩) (b := ⟨ 1, h1 ⟩) (c := b x) (d := x)).2
  . simp; convert h2_ne_1
  grind

lemma d1_eq_8 : d ⟨ 1, h1 ⟩ = ⟨ 8, h8 ⟩ := by
  obtain ⟨ x, hx ⟩ := d_surjective ⟨ 8, h8 ⟩
  have := bd_ident x
  simp [hx] at this
  replace : 2 * (b x).val = 2 * (x.val + 3) := by grind
  replace := mul_two_inj this
  convert hx
  convert congrArg Subtype.val (diff_uniq ?_ ?_ (a := ⟨ 4, h4 ⟩) (b := ⟨ 1, h1 ⟩) (c := b x) (d := x)).2
  . simp; convert h4_ne_1
  grind

lemma contradiction : False := by
  have := d1_eq_8
  rw [d1_eq_4] at this
  simp at this
  exact h4_ne_8 this
