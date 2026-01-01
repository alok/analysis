import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro _; rfl
    symm := by
      intro _ _ hₕ
      grind
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1ₕ h2ₕ; simp_all
      have h3ₕ := congrArg₂ (· + ·) h1ₕ h2ₕ; simp at h3ₕ
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3ₕ
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by
  refine Iff.intro ?mp ?mpr
  case mp => simp [HasEquiv.Equiv, instSetoid]
  case mpr => exact id

abbrev QInt := Quotient PreInt.instSetoid

abbrev QInt.formalDiff (a b:ℕ)  : QInt := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => QInt.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem QInt.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro hₕ; exact Quotient.sound hₕ ⟩

/-- Definition 4.1.1 (Integers) -/
theorem QInt.eq_diff (n:QInt) : ∃ a b, n = a —— b := by
  apply n.ind _
  intro ⟨ a, b ⟩
  use a, b

def QInt.toInt (x : QInt) : Int :=
  x.lift
    (fun ⟨p, q⟩ => (p : Int) - (q : Int))
    (fun ⟨_, _⟩ ⟨_, _⟩ => by simp only [PreInt.eq]; grind)

instance : Lean.Grind.ToInt QInt .ii where
  toInt := QInt.toInt
  toInt_inj x y :=
    Quotient.inductionOn₂ x y <| by
    intro ⟨_, _⟩ ⟨_, _⟩
    simp only [QInt.toInt, Quotient.lift_mk, QInt.eq]
    grind
  toInt_mem x := by simp only [Lean.Grind.IntInterval.mem_ii]

/-- Lemma 4.1.3 (Addition well-defined) -/
instance QInt.instAdd : Add QInt where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1ₕ h2ₕ
    have h1ₕ' : a + b' = a' + b := by simpa [PreInt.eq] using h1ₕ
    have h2ₕ' : c + d' = c' + d := by simpa [PreInt.eq] using h2ₕ
    apply (QInt.eq (a := a + c) (b := b + d) (c := a' + c') (d := b' + d')).2
    calc
      (a + c) + (b' + d') = (a + b') + (c + d') := by abel_nf
      _ = (a' + b) + (c' + d) := by rw [h1ₕ', h2ₕ']
      _ = (a' + c') + (b + d) := by abel_nf)

/-- Definition 4.1.2 (Definition of addition) -/
theorem QInt.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) :=
  Quotient.lift₂_mk _ _ _ _

instance : Lean.Grind.ToInt.Add QInt .ii where
  toInt_add x y :=
    Quotient.inductionOn₂ x y <| by
    intro ⟨_, _⟩ ⟨_, _⟩
    simp [QInt.add_eq, Lean.Grind.ToInt.toInt, QInt.toInt]
    grind

theorem QInt.eq_of_toInt_eq (x y : QInt) :
    Lean.Grind.ToInt.toInt x = Lean.Grind.ToInt.toInt y → x = y := by
  simpa using (Lean.Grind.ToInt.toInt_inj (α:=QInt) (range:=.ii) x y)

@[simp]
theorem QInt.eq_iff_toInt_eq (x y : QInt) :
    x = y ↔ Lean.Grind.ToInt.toInt x = Lean.Grind.ToInt.toInt y := by
  constructor
  · intro hₕ
    simpa using congrArg (Lean.Grind.ToInt.toInt) hₕ
  · exact QInt.eq_of_toInt_eq x y

@[simp]
theorem QInt.toInt_add (x y : QInt) :
    Lean.Grind.ToInt.toInt (x + y) = Lean.Grind.ToInt.toInt x + Lean.Grind.ToInt.toInt y := by
  simpa using (Lean.Grind.ToInt.Add.toInt_add (α:=QInt) (I:=.ii) x y)

-- NOTE: On Lean >= 4.28, marking `QInt.eq_iff_toInt_eq` and `QInt.toInt_add` with
-- `@[grind norm]` lets `by grind` close `addAssoc`/`addComm` directly.

theorem QInt.addAssoc (a b c : QInt) : a + (b + c) = a + b + c := by
  apply QInt.eq_of_toInt_eq
  simp [QInt.toInt_add, add_assoc]

theorem QInt.addComm (a b : QInt) : a + b = b + a := by
  apply QInt.eq_of_toInt_eq
  simp [QInt.toInt_add, add_comm]

end Section_4_1
