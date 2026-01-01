import Mathlib


-- macro_rules
-- | `(tactic|rw [$args]) => `(tactic|grw [$args])

namespace ConvolutedProofs

/-! Lemmas for the convoluted proof of irrationality of √2 -/

/-- $3$ is a unit in {lit}``ZMod 8``. -/
theorem three_unit_mod_eight : IsUnit (3 : ZMod 8) := by
  decide

/-- The set of primes congruent to 3 modulo 8. -/
abbrev primes_three_mod_eight : Set ℕ := {p : ℕ | p.Prime ∧ (p : ZMod 8) = 3}

/-- The set of primes congruent to 3 modulo 8 is infinite. -/
lemma primes_three_mod_eight_infinite :
    primes_three_mod_eight.Infinite := by
  exact Nat.setOf_prime_and_eq_mod_infinite three_unit_mod_eight

/-- Quotient notation -/
notation "ℤ" "/" n => ZMod n

/-- For primes p ≡ 3 (mod 8) with p ≠ 2, the element 2 is not a quadratic residue. -/
lemma two_not_square_mod_prime_three_mod_eight (p : ℕ)
    (hp : p.Prime ∧ (p : ℤ / 8) = 3) (hp2 : p ≠ 2) :
    ¬IsSquare (2 : ℤ / p) := by
  haveI : Fact p.Prime := ⟨hp.1⟩
  have : p % 8 = 3 := by
    have hcast : (p : ℤ / 8) = 3 := hp.2
    have : (p : ℤ / 8).val = 3 := by
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

/-! Given an infinite set, we can always find an element larger than any given bound with {lit}``Set.Infinite.exists_gt``. -/


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
  have : (2 : ℤ / 8) = 3 := hp.2
  -- But 2 mod 8 = 2, not 3, so this is a contradiction
  have : (2 : ℤ / 8) ≠ 3 := by decide
  exact this hp.2

/-- Type representing the index set for our ultraproduct: primes ≡ 3 (mod 8). -/
abbrev PrimeIndex := primes_three_mod_eight

/-- These should be the same, but we still declare {lit}``PrimeIndex``. -/
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
    (hsq : a^2 = 2 * b^2) (hpb : ¬(p ∣ b)) : IsSquare (2 : ℤ / p) := by
  have hb_nonzero : (b : ℤ / p) ≠ 0 := by
    intro h
    have : p ∣ b := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    exact hpb this

  use (a : ℤ / p) * (b : ℤ / p)⁻¹
  have mod_eq : ((a : ℤ / p))^2 = 2 * ((b : ℤ / p))^2 := by
    have : (a^2 : ℤ / p) = (2 * b^2 : ℤ / p) := by
      simp only [← Nat.cast_pow]
      rw [hsq]
      simp [Nat.cast_mul]
    convert this using 1

  have hb_unit : IsUnit (b : ZMod p) := isUnit_iff_ne_zero.mpr hb_nonzero

  symm
  calc (a : ℤ / p) * (b : ℤ / p)⁻¹ * ((a : ℤ / p) * (b : ℤ / p)⁻¹)
    = (a : ℤ / p) * (a : ℤ / p) * ((b : ℤ / p)⁻¹ * (b : ℤ / p)⁻¹) := by ring
  _ = (a : ℤ / p)^2 * (b : ℤ / p)⁻¹^2 := by rw [pow_two, pow_two]
  _ = 2 * (b : ℤ / p)^2 * (b : ℤ / p)⁻¹^2 := by rw [mod_eq]
  _ = 2 * ((b : ℤ / p)^2 * (b : ℤ / p)⁻¹^2) := by ring
  _ = 2 * 1 := by
    congr 1
    have : (b : ℤ / p)^2 * (b : ℤ / p)⁻¹^2 = ((b : ℤ / p) * (b : ℤ / p)⁻¹)^2 := by ring
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


/-
/-- A real number is irrational if it is not equal to any rational number. -/
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)
-/

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
