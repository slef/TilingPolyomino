import Mathlib.Tactic

-- ============================================================
-- Modulo 3 Helper Lemmas
-- ============================================================

theorem mod3_ne_zero_of_mul_mod3_ne_zero_left {n m : ℕ}
    (h : (n * m) % 3 ≠ 0) :
    n % 3 ≠ 0 := by
  intro hn0
  -- From `n % 3 = 0` we get `3 ∣ n`, hence `3 ∣ n * m`, so `(n * m) % 3 = 0`.
  have h3_div_n : 3 ∣ n := Nat.dvd_of_mod_eq_zero hn0
  have h3_div_nm : 3 ∣ n * m := dvd_mul_of_dvd_left h3_div_n m
  have hzero : (n * m) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3_div_nm
  exact h hzero

/- A number modulo `3` is either `0`, `1`, or `2`.  If it is not `0`, it must
be `1` or `2`. -/
theorem mod3_eq_one_or_two_of_ne_zero {n : ℕ} (h : n % 3 ≠ 0) :
    n % 3 = 1 ∨ n % 3 = 2 := by
  -- First, `n % 3` lies in `{0,1,2}` since it is strictly less than `3`.
  have hlt3 : n % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
  -- From `n % 3 ≠ 0` we get `0 < n % 3` and hence `1 ≤ n % 3`.
  have hpos : 0 < n % 3 := Nat.pos_of_ne_zero h
  have hge1 : 1 ≤ n % 3 := Nat.succ_le_of_lt hpos
  -- Rewrite `< 3` as `≤ 2`.
  have hle2 : n % 3 ≤ 2 := by
    have : n % 3 < (2 : ℕ).succ := by simpa using hlt3
    exact Nat.lt_succ_iff.mp this
  -- So either `n % 3 < 2` or `n % 3 = 2`.
  have hlt2_or_eq2 : n % 3 < 2 ∨ n % 3 = 2 := lt_or_eq_of_le hle2
  rcases hlt2_or_eq2 with hlt2 | heq2
  · -- Case `n % 3 < 2`: then in fact `n % 3 ≤ 1`, and together with `1 ≤ n % 3`
    -- we get `n % 3 = 1`.
    have hle1 : n % 3 ≤ 1 := by
      have : n % 3 < (1 : ℕ).succ := by simpa using hlt2
      exact Nat.lt_succ_iff.mp this
    have : n % 3 = 1 := le_antisymm hle1 hge1
    exact Or.inl this
  · -- Case `n % 3 = 2`.
    exact Or.inr heq2

/- If `(n * m) % 3 = 1`, then the residues of `n` and `m` modulo 3 are
either both `1` or both `2`. Mixed congruence classes `{1,2}` give
product ≡ 2 (mod 3), not 1.

This lemma is currently left as a placeholder; the intended proof follows
the standard modular arithmetic argument sketched in the comments above. -/
theorem mod3_both_one_or_two_of_area_mod3_zero
    {n m : ℕ}
    (h : (n * m) % 3 = 1) :
    (n % 3 = 1 ∧ m % 3 = 1) ∨ (n % 3 = 2 ∧ m % 3 = 2) := by
  -- From `(n * m) % 3 = 1` we know the product is not divisible by 3.
  have hnm_ne0 : (n * m) % 3 ≠ 0 := by
    simp [h]
  -- Hence neither factor is `0` mod `3`.
  have hn_ne0 : n % 3 ≠ 0 :=
    mod3_ne_zero_of_mul_mod3_ne_zero_left (n := n) (m := m) hnm_ne0
  have hm_ne0 : m % 3 ≠ 0 := by
    have hmn_ne0 : (m * n) % 3 ≠ 0 := by
      simpa [Nat.mul_comm] using hnm_ne0
    exact mod3_ne_zero_of_mul_mod3_ne_zero_left (n := m) (m := n) hmn_ne0
  -- Each residue modulo `3` is therefore either `1` or `2`.
  have hn_res : n % 3 = 1 ∨ n % 3 = 2 :=
    mod3_eq_one_or_two_of_ne_zero hn_ne0
  have hm_res : m % 3 = 1 ∨ m % 3 = 2 :=
    mod3_eq_one_or_two_of_ne_zero hm_ne0
  -- Analyze the four possible combinations of residues.
  rcases hn_res with hn1 | hn2
  · -- Case `n % 3 = 1`.
    rcases hm_res with hm1 | hm2
    · -- Subcase `m % 3 = 1`: this is one of the desired alternatives.
      left
      exact ⟨hn1, hm1⟩
    · -- Subcase `m % 3 = 2`: then `(n * m) % 3 = 2`, contradicting `h`.
      have hnm2 : (n * m) % 3 = 2 := by
        have hcalc : (n * m) % 3 = (1 * 2) % 3 := by
          simpa [hn1, hm2] using (Nat.mul_mod n m 3)
        simpa using hcalc
      have : (1 : ℕ) ≠ 2 := by decide
      have hf : False := this (h.symm.trans hnm2)
      exact hf.elim
  · -- Case `n % 3 = 2`.
    rcases hm_res with hm1 | hm2
    · -- Subcase `m % 3 = 1`: symmetric to the previous contradictory case.
      have hnm2 : (n * m) % 3 = 2 := by
        have hcalc : (n * m) % 3 = (2 * 1) % 3 := by
          simpa [hn2, hm1] using (Nat.mul_mod n m 3)
        simpa using hcalc
      have : (1 : ℕ) ≠ 2 := by decide
      have hf : False := this (h.symm.trans hnm2)
      exact hf.elim
    · -- Subcase `m % 3 = 2`: this is the other desired alternative.
      right
      exact ⟨hn2, hm2⟩

/-- If `(n * m) % 3 = 2`, then modulo `3` the residues of `n` and `m` are
`1` and `2` in some order. -/
theorem mod3_one_two_or_two_one_of_area_mod3_two
    {n m : ℕ} (h : (n * m) % 3 = 2) :
    (n % 3 = 1 ∧ m % 3 = 2) ∨ (n % 3 = 2 ∧ m % 3 = 1) := by
  -- From `(n * m) % 3 = 2` we know the product is not divisible by 3.
  have hnm_ne0 : (n * m) % 3 ≠ 0 := by
    simp [h]
  -- Hence neither factor is `0` mod `3`.
  have hn_ne0 : n % 3 ≠ 0 :=
    mod3_ne_zero_of_mul_mod3_ne_zero_left (n := n) (m := m) hnm_ne0
  have hm_ne0 : m % 3 ≠ 0 := by
    have hmn_ne0 : (m * n) % 3 ≠ 0 := by
      simpa [Nat.mul_comm] using hnm_ne0
    exact mod3_ne_zero_of_mul_mod3_ne_zero_left (n := m) (m := n) hmn_ne0
  -- Each residue modulo `3` is therefore either `1` or `2`.
  have hn_res : n % 3 = 1 ∨ n % 3 = 2 :=
    mod3_eq_one_or_two_of_ne_zero hn_ne0
  have hm_res : m % 3 = 1 ∨ m % 3 = 2 :=
    mod3_eq_one_or_two_of_ne_zero hm_ne0
  -- Analyze the four possible combinations of residues.
  rcases hn_res with hn1 | hn2
  · -- Case `n % 3 = 1`.
    rcases hm_res with hm1 | hm2
    · -- Subcase `m % 3 = 1`: then `(n * m) % 3 = 1`, contradicting `h = 2`.
      have hnm1 : (n * m) % 3 = 1 := by
        have hcalc : (n * m) % 3 = (1 * 1) % 3 := by
          simpa [hn1, hm1] using (Nat.mul_mod n m 3)
        simpa using hcalc
      -- This contradicts `h : (n * m) % 3 = 2`.
      have hnm1' : (2 : ℕ) = 1 := by simp [h] at hnm1
      have hfalse : False := (by decide : (2 : ℕ) ≠ 1) hnm1'
      exact hfalse.elim
    · -- Subcase `m % 3 = 2`: this is one of the desired alternatives.
      left
      exact ⟨hn1, hm2⟩
  · -- Case `n % 3 = 2`.
    rcases hm_res with hm1 | hm2
    · -- Subcase `m % 3 = 1`: this is the other desired alternative.
      right
      exact ⟨hn2, hm1⟩
    · -- Subcase `m % 3 = 2`: then `(n * m) % 3 = 1`, contradicting `h = 2`.
      have hnm1 : (n * m) % 3 = 1 := by
        have hcalc : (n * m) % 3 = (2 * 2) % 3 := by
          simpa [hn2, hm2] using (Nat.mul_mod n m 3)
        simpa using hcalc
      -- This contradicts `h : (n * m) % 3 = 2`.
      have hnm1' : (2 : ℕ) = 1 := by simp [h] at hnm1
      have hfalse : False := (by decide : (2 : ℕ) ≠ 1) hnm1'
      exact hfalse.elim
