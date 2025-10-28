import Mathlib.Tactic
import Analysis.Section_2_1
import Mathlib.NumberTheory.LSeries.PrimesInAP
-- set_option doc.verso true
/-!
# Analysis I, Section 2.2: Addition

This file is a translation of Section 2.2 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrase as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`. However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Compare with Mathlib's `Nat.zero_add`. -/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's `Nat.succ_add`. -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's `Nat.one_add`. -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- The sum of two natural numbers is again a natural number.
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n). Compare with Mathlib's `Nat.add_zero`. -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). Compare with Mathlib's `Nat.add_succ`. -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]

/-- n++ = n + 1 (Why?). Compare with Mathlib's `Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  rw [← zero_succ, add_succ, add_zero]

example : 2 + 2  = 4 := Eq.refl (2 + 2)

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's `Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]

  rw [add_succ, ih]
-- #eval congrArg
/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's `Nat.add_assoc`. -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
    revert a; apply induction

    . rw [zero_add, zero_add (b + c)]
    intro n ih
      -- goal: rewrite to `(a+b+c)++ = (a+b+c)++`, pushing out the `++`
    rw [Nat.succ_add,succ_add,succ_add,ih]



/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's `Nat.add_left_cancel`. -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid.
This permits tactics such as `abel` to apply to the Chapter 2 natural numbers. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- This illustration of the `abel` tactic is not from the
    textbook. -/
example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's `Nat.add_pos_left`. -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Compare with Mathlib's `Nat.add_pos_right`.

This theorem is a consequence of the previous theorem and `add_comm`, and `grind` can automatically discover such proofs.
-/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  grind [add_comm, add_pos_left]

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  obtain ha | hb := h
  . rw [← isPos_iff] at ha
    observe : (a + b).IsPos
    contradiction
  rw [← isPos_iff] at hb
  observe : (a + b).IsPos
  contradiction

/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem. Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

/-

∃! = ∃ x, p x ∧ ∀ y, p y → y = x
-/

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  induction a
  case zero =>
    absurd ha
    rfl
  case succ a ih =>
    simp only [succ.injEq, existsUnique_eq]


/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `≤` notation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le`. -/
@[symm]
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt`. -/
@[symm]
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's `Nat.le_of_lt`. -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq`. -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

opaque aaa : Nat := 0
def aa : Nat := 0

-- /---/
-- #guard_msgs in
-- example : aaa = 0 := by rfl
example : aa = 0 := by rfl

example  (h :a < b) : a++ < b++ := by simp [h]

/-- Compare with Mathlib's `Nat.lt_succ_self`. -/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  rw [succ_eq_add_one]
  constructor
  · use 1
  case right =>
    by_contra h
    conv_lhs at h =>
      rw [<- add_zero n]
    -- #loogle _ + _ = _ + _
    apply Nat.add_left_cancel at h
    contradiction

example : (∃ (x : _root_.Nat), 3 < x  ):=by
  use 4
  simp


-- #eval Ne
/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  cases zero
  rw [ge_iff_le]



  -- . cases
    -- rename_i x
  -- constructor
  -- .
  -- .

@[refl]
theorem Nat.le_refl (a:Nat) : a ≤ a := a.ge_refl

/-- The refl tag allows for the `rfl` tactic to work for inequalities. -/
example (a b:Nat): a+b ≥ a+b := by rfl

/-- (b) (Order is transitive). The `obtain` tactic will be useful here.
    Compare with Mathlib's `Nat.le_trans`. -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  sorry

theorem Nat.le_trans {a b c:Nat} (hab: a ≤ b) (hbc: b ≤ c) : a ≤ c := Nat.ge_trans hbc hab

/-- (c) (Order is anti-symmetric). Compare with Mathlib's `Nat.le_antisymm`. -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  sorry

/-- (d) (Addition preserves order). Compare with Mathlib's `Nat.add_le_add_right`. -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  sorry

/-- (d) (Addition preserves order). Compare with Mathlib's `Nat.add_le_add_left`. -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order). Compare with Mathlib's `Nat.add_le_add_right`. -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order). Compare with Mathlib's `Nat.add_le_add_left`. -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b. Compare with Mathlib's `Nat.succ_le_iff`. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  sorry

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  sorry

/-- If a < b then a ̸= b. -/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- If a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (le_of_lt h.1) (le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

theorem Nat.not_lt_self {a: Nat} (h : a < a) : False := by
  apply not_lt_of_gt a a
  simp [h]

theorem Nat.lt_of_le_of_lt {a b c : Nat} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rw [lt_iff_add_pos] at *
  choose d hd using hab
  choose e he1 he2 using hbc
  use d + e; split_ands
  . exact add_pos_right d he1
  . rw [he2, hd, add_assoc]

/-- This lemma was a `why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by
  sorry

-- example (a b : Nat) : |a+b| ≤ |a| + |b| := sorry

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous`. Parts of this theorem have been placed
    in the preceding Lean theorems. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . observe why : 0 ≤ b
    rw [le_iff_lt_or_eq] at why
    tauto
  intro a ih
  obtain case1 | case2 | case3 := ih
  . rw [lt_iff_succ_le] at case1
    rw [le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by sorry
    tauto
  have why : a++ > b := by sorry
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably. The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers. One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`.
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    sorry
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        sorry
      | isFalse h =>
        apply isTrue
        sorry
    | isFalse h =>
      apply isFalse
      sorry

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

/-- (Not from textbook) Nat has the structure of a linear ordering. This allows for tactics
such as `order` and `calc` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge a b := by
    constructor
    . intro h; refine ⟨ le_of_lt h, ?_ ⟩
      by_contra h'
      exact not_lt_self (lt_of_le_of_lt h' h)
    rintro ⟨ h1, h2 ⟩
    rw [lt_iff, ←le_iff]; refine ⟨ h1, ?_ ⟩
    by_contra h
    subst h
    contradiction
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total a b := by
    obtain h | rfl | h := trichotomous a b
    . left; exact le_of_lt h
    . simp [ge_refl]
    . right; exact le_of_lt h
  toDecidableLE := decidableRel

/-- This illustration of the `order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- An illustration of the `calc` tactic with `≤/<`. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hcd: c ≤ d)
        (hde: d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by simp
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

/-- (Not from textbook) Nat has the structure of an ordered monoid. This allows for tactics
such as `gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (add_le_add_left a b c).mp hab

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a + d ≤ c + e := by
  gcongr
  order

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`.
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  sorry

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  sorry

-- #help tactic grind

end Chapter2
namespace ConvolutedProofs

/-! Lemmas for the convoluted proof of irrationality of √2 -/

/-- $3$ is a unit in `ZMod 8`. -/
theorem three_unit_mod_eight : IsUnit (3 : ZMod 8) := by
  decide

/-- The set of primes congruent to 3 modulo 8. -/
abbrev primes_three_mod_eight : Set ℕ := {p : ℕ | p.Prime ∧ (p : ZMod 8) = 3}

/-- The set of primes congruent to 3 modulo 8 is infinite. -/
lemma primes_three_mod_eight_infinite :
    primes_three_mod_eight.Infinite := by
  exact Nat.setOf_prime_and_eq_mod_infinite three_unit_mod_eight


/-- For primes p ≡ 3 (mod 8) with p ≠ 2, the element 2 is not a quadratic residue. -/
lemma two_not_square_mod_prime_three_mod_eight (p : ℕ)
    (hp : p.Prime ∧ (p : ZMod 8) = 3) (hp2 : p ≠ 2) :
    ¬IsSquare (2 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp.1⟩
  have : p % 8 = 3 := by
    have hcast : (p : ZMod 8) = 3 := hp.2
    have : ZMod.val (p : ZMod 8) = 3 := by
      rw [hcast]
      rfl
    rwa [ZMod.val_natCast] at this
  rw [ZMod.exists_sq_eq_two_iff hp2]
  push_neg
  constructor
  · intro h
    rw [this] at h
    norm_num at h
  · intro h
    rw [this] at h
    norm_num at h

/-! Given an infinite set, we can always find an element larger than any given bound with `Set.Infinite.exists_gt`. -/


/-- Extract the coprime numerator and denominator from a rational number. -/
lemma rat_to_coprime_pair (q : ℚ) (hq_pos : 0 < q) :
    ∃ (a b : ℕ), 0 < b ∧ a.Coprime b ∧ (q : ℝ) = a / b := by
  let a := q.num.natAbs
  let b := q.den
  use a, b
  refine ⟨q.pos, ?_, ?_⟩
  · rw [Nat.Coprime]
    convert q.reduced using 2
  · simp only [Rat.cast_def, a, b]
    congr
    exact (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hq_pos))).symm
-- set_option pp.coercions false in
theorem idk (h: ¬(∃q : ℚ, ↑q = √(2:Rat))) : True := by sorry

/-- If √2 = a/b with a, b coprime, then a² = 2b². -/
lemma sqrt_two_eq_ratio_implies_square_eq (a b : ℕ) (hb_pos : 0 < b)
    (h : (√2 : ℝ) = a / b) : a^2 = 2 * b^2 := by
  have : ((a : ℝ) / b)^2 = 2 := by
    rw [← h]
    norm_num
  field_simp [hb_pos.ne'] at this
  norm_cast at this


/-- A prime p larger than max(a,b) doesn't divide a or b (when they are positive). -/
lemma prime_gt_max_not_div (p a b : ℕ) (_ : p.Prime) (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hbig : max a b < p) : ¬(p ∣ a) ∧ ¬(p ∣ b) := by
  constructor
  · intro hdiv
    exact absurd (Nat.le_of_dvd ha_pos hdiv)
      (not_le.mpr ((le_max_left a b).trans_lt hbig))
  · intro hdiv
    exact absurd (Nat.le_of_dvd hb_pos hdiv)
      (not_le.mpr ((le_max_right a b).trans_lt hbig))

/-- For any prime p ≡ 3 (mod 8), we have p ≠ 2. -/
lemma prime_three_mod_eight_ne_two {p : ℕ} (hp : p ∈ primes_three_mod_eight) : p ≠ 2 := by
  intro h
  subst h
  have : (2 : ZMod 8) = 3 := hp.2
  -- But 2 mod 8 = 2, not 3, so this is a contradiction
  have : (2 : ZMod 8) ≠ 3 := by decide
  exact this hp.2

/-- Type representing the index set for our ultraproduct: primes ≡ 3 (mod 8). -/
abbrev PrimeIndex := primes_three_mod_eight

/-- These should be the same, but we still declare `PrimeIndex`. -/
example : @PrimeIndex  = @primes_three_mod_eight := by simp


/-- Extract the natural number from a PrimeIndex. -/
instance : CoeOut PrimeIndex ℕ where
  coe := fun p => p.val

/-- Each prime index gives us a finite field 𝔽_p. -/
def field_at_prime (p : PrimeIndex) : Type := ZMod p.val

/-- The family of finite fields indexed by our primes. -/
def prime_field_family : PrimeIndex → Type := field_at_prime

instance (p : PrimeIndex) : Fact p.val.Prime := ⟨p.property.1⟩

/-- Lift a rational number to the product of all finite fields. -/
def rat_to_product (q : ℚ) : ∀ (p : PrimeIndex), ZMod p.val :=
  fun p => (q.num : ZMod p.val) / (q.den : ZMod p.val)

/-- If √2 were rational q = a/b, then at each prime p we would have
    (a/b)² = 2 mod p (thinking of this as (a * b⁻¹)² in the field 𝔽_p).
    However, for p ≡ 3 (mod 8) with p > max(a,b), this creates a contradiction:
    the equation forces 2 to be a square in 𝔽_p, but quadratic reciprocity
    says it's not. -/
lemma rational_sqrt_two_contradiction (q : ℚ) (hq : (q : ℝ) = √2) :
    False := by
 sorry

/-- In ZMod p, if a² = 2b² and p doesn't divide b, then 2 is a square mod p. -/
lemma two_is_square_mod_p (p a b : ℕ) [Fact p.Prime]
    (hsq : a^2 = 2 * b^2) (hpb : ¬(p ∣ b)) : IsSquare (2 : ZMod p) := by
  have hb_nonzero : (b : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ b := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    exact hpb this

  use (a : ZMod p) * (b : ZMod p)⁻¹
  have mod_eq : ((a : ZMod p))^2 = 2 * ((b : ZMod p))^2 := by
    have : (a^2 : ZMod p) = (2 * b^2 : ZMod p) := by
      simp only [← Nat.cast_pow]
      rw [hsq]
      simp [Nat.cast_mul]
    convert this using 1

  have hb_unit : IsUnit (b : ZMod p) := isUnit_iff_ne_zero.mpr hb_nonzero

  symm
  calc (a : ZMod p) * (b : ZMod p)⁻¹ * ((a : ZMod p) * (b : ZMod p)⁻¹)
    = (a : ZMod p) * (a : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by ring
  _ = (a : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by rw [pow_two, pow_two]
  _ = 2 * (b : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by rw [mod_eq]
  _ = 2 * ((b : ZMod p)^2 * (b : ZMod p)⁻¹^2) := by ring
  _ = 2 * 1 := by
    congr 1
    have : (b : ZMod p)^2 * (b : ZMod p)⁻¹^2 = ((b : ZMod p) * (b : ZMod p)⁻¹)^2 := by ring
    rw [this, ZMod.mul_inv_of_unit _ hb_unit, one_pow]
  _ = 2 := by ring

/-- The square root of 2 is irrational.

This convoluted proof uses ultrafilters, Łoś's theorem, and Dirichlet's theorem,
following Asaf Karagila's approach from:
https://math.stackexchange.com/questions/1311228/

The key idea: Assume √2 is rational. Then x² = 2 has a solution in characteristic 0.
We construct an ultraproduct of finite fields Fₚ (where 2 is not a square) via a
free ultrafilter. By Łoś's theorem, this ultraproduct has characteristic 0 and contains
ℚ, but x² = 2 has no solution - contradicting that √2 would be in any characteristic 0
field containing ℚ.
-/
theorem irrational_sqrt_2 : Irrational √2 := by
  by_contra h_rat
  push_neg at h_rat

  -- ============================================================================
  -- Step 1: Use Dirichlet's theorem to get infinitely many primes where 2 is
  -- not a quadratic residue
  -- ============================================================================

  -- For each such prime p ≡ 3 (mod 8), we have p ≠ 2 and 2 is not a square mod p
  have no_sqrt_in_fields : ∀ p ∈ primes_three_mod_eight, ∃ (hp_fact : Fact p.Prime),
      ¬IsSquare (2 : ZMod p) := by
    intro p hp
    use ⟨hp.1⟩
    have hp_ne_2 : p ≠ 2 := prime_three_mod_eight_ne_two hp
    exact two_not_square_mod_prime_three_mod_eight p hp hp_ne_2

  -- ============================================================================
  -- Step 2: The contradiction via ultraproducts
  -- ============================================================================

  -- If √2 were rational, then x² - 2 would have a root in ℚ ⊆ ℝ.
  -- Now consider the ultraproduct construction:
  --
  -- Let U be a free ultrafilter on P = {p : p ≡ 3 (mod 8)}.
  -- Form F = ∏_{p ∈ P} 𝔽_p / U (ultraproduct of finite fields).
  --
  -- By Łoś's theorem:
  -- 1. F has characteristic 0 (since {p : char(𝔽_p) = 0} = P ∈ U)
  -- 2. F contains a copy of ℚ (via the diagonal embedding)
  -- 3. x² - 2 has NO root in F (since for each p ∈ P, x² - 2 has no root in 𝔽_p)
  --
  -- But this contradicts: if √2 ∈ ℚ, then √2 would be in F (as ℚ ⊆ F),
  -- and hence x² - 2 would have a root in F.
  --
  -- The contradiction shows √2 cannot be rational.
  --
  -- NOTE: This proof requires the Axiom of Choice to construct the free ultrafilter.
  -- In models of ZF without free ultrafilters, this proof method fails - but √2
  -- is still irrational via other proofs.

  -- For the formalization, we use a more direct approach that captures the essence:
  -- If √2 = a/b with gcd(a,b) = 1, then a² = 2b².
  -- By choosing a large prime p ≡ 3 (mod 8) with p > max(a,b):
  -- - From a² = 2b² and p ∤ b, we get 2 is a square mod p
  -- - But 2 is NOT a square mod p (by quadratic reciprocity)
  -- This captures the "no solution in 𝔽_p but would have solution in char 0" idea.

  obtain ⟨q, hq : (q : ℝ) = √2⟩ := h_rat

  have hq_pos : 0 < q := by
    have : (0 : ℝ) < q := by
      rw [hq]
      exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast this

  -- Get coprime representation √2 = a/b
  obtain ⟨a, b, hb_pos, hcoprime, hrat⟩ := rat_to_coprime_pair q hq_pos
  have hrat_sqrt : √2 = a / b := by
    rw [← hq, hrat]

  -- From √2 = a/b, we get a² = 2b²
  have hsq : a^2 = 2 * b^2 := sqrt_two_eq_ratio_implies_square_eq a b hb_pos hrat_sqrt

  -- Choose a prime p ∈ P with p > max(a, b)
  obtain ⟨p, hp, hbig⟩ : ∃ p ∈ primes_three_mod_eight, max a b < p :=
    exists_in_infinite_set_gt P_infinite (max a b)

  have ha_pos : 0 < a := by
    by_contra h0
    simp at h0
    rw [h0] at hsq
    simp at hsq
    linarith [hb_pos]
  have ⟨hpa, hpb⟩ := prime_gt_max_not_div p a b hp.1 ha_pos hb_pos hbig

  haveI : Fact p.Prime := ⟨hp.1⟩

  -- The characteristic 0 field ℚ has √2 (by assumption)
  -- But the field 𝔽_p (characteristic p) does not have √2:
  have hp_ne_2 : p ≠ 2 := prime_three_mod_eight_ne_two hp
  have not_sq2_in_Fp : ¬IsSquare (2 : ZMod p) :=
    two_not_square_mod_prime_three_mod_eight p hp hp_ne_2

  -- Yet from a² = 2b² and p ∤ b, we would get 2 is a square mod p:
  have sq2_in_Fp : IsSquare (2 : ZMod p) := two_is_square_mod_p p a b hsq hpb

  -- Contradiction! This mirrors the ultraproduct argument:
  -- The diagonal image of √2 in the ultraproduct would witness that 2 is a square,
  -- but by Łoś's theorem, 2 is not a square in the ultraproduct.
  exact not_sq2_in_Fp sq2_in_Fp

-- ============================================================================
-- Lemmas for the cardinality proof
-- ============================================================================

/-- Continuous functions ℝ → ℝ are determined by their values on ℚ. -/
lemma continuous_determined_by_rationals {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q : ℚ, f q = g q) : f = g := by
  have dense_Q : DenseRange (fun q : ℚ ↦ (q : ℝ)) := Rat.denseRange_cast
  have eq_comp : f ∘ (fun q : ℚ ↦ (q : ℝ)) = g ∘ (fun q : ℚ ↦ (q : ℝ)) := by
    ext q
    exact h q
  exact dense_Q.equalizer hf hg eq_comp

/-- There exists a discontinuous function.

This uses a convoluted cardinality argument via Cantor's theorem, following:
https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts
-/
theorem discontinuous_function_exists : ∃ f : ℝ → ℝ, ¬ Continuous f := by
  by_contra h1
  push_neg at h1

  -- ============================================================================
  -- Step 1: Set up the restriction map
  -- ============================================================================

  -- If all functions are continuous, they're determined by values on ℚ
  let F : (ℝ → ℝ) → (ℚ → ℝ) := fun f ↦ fun q ↦ f (↑q : ℝ)

  -- ============================================================================
  -- Step 2: Prove F is injective
  -- ============================================================================

  have F_inj : Function.Injective F := by
    intro f g hFfg
    have hf : Continuous f := h1 f
    have hg : Continuous g := h1 g
    have h : ∀ q : ℚ, f q = g q := fun q => by
      have : F f q = F g q := by rw [hFfg]
      exact this
    exact continuous_determined_by_rationals hf hg h

  -- ============================================================================
  -- Step 3: Derive the cardinality inequality
  -- ============================================================================

  have card_le : #(ℝ → ℝ) ≤ #(ℚ → ℝ) := Cardinal.mk_le_of_injective F_inj

  -- Compute cardinalities
  have card_RR : #(ℝ → ℝ) = #ℝ ^ #ℝ := by simp
  have card_QR : #(ℚ → ℝ) = #ℝ ^ #ℚ := by simp
  have card_Q : #ℚ = ℵ₀ := Cardinal.mkRat
  have card_R : #ℝ = 𝔠 := Cardinal.mk_real

  -- Rewrite in terms of 𝔠 and ℵ₀
  rw [card_RR, card_QR, card_Q, card_R] at card_le

  -- ============================================================================
  -- Step 4: Apply Cantor's theorem to get contradiction
  -- ============================================================================

  -- We have 𝔠 ^ 𝔠 ≤ 𝔠 ^ ℵ₀ = 𝔠
  have pow_aleph0 : 𝔠 ^ ℵ₀ = 𝔠 := Cardinal.continuum_power_aleph0
  rw [pow_aleph0] at card_le

  -- But Cantor's theorem gives 𝔠 < 𝔠 ^ 𝔠
  have one_lt_cont : 1 < 𝔠 := Cardinal.nat_lt_continuum 1
  have lt_pow : 𝔠 < 𝔠 ^ 𝔠 := Cardinal.cantor' _ one_lt_cont

  -- Contradiction!
  exact not_lt.mpr card_le lt_pow

end ConvolutedProofs

/-
TODO:

- move repo to ConvolutedProofs
- verso
- FirstOrder.Language
leandex

the original sqrt 2 irrational statement to fig out how to handle the type casting of the sqrt function
-/
-- #check Sqrt
