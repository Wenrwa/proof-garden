import ProofGarden.Defs

/-!
# Lemma: every number ≥ 2 has a prime factor

The smallest divisor of `n` that is at least 2 is prime.
-/

namespace ProofGarden

/-- Every natural number `n ≥ 2` is divisible by some prime. -/
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p, IsPrime p ∧ p ∣ n := by
  -- Strong induction, done as ordinary induction on a bound `m ≥ n`.
  have key : ∀ m n, n ≤ m → 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n := by
    intro m
    induction m with
    | zero => intro n hn h2; omega
    | succ m ih =>
      intro n hn h2
      by_cases hp : IsPrime n
      · exact ⟨n, hp, Nat.dvd_refl n⟩
      · have hex : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
          refine Classical.byContradiction fun hc => ?_
          apply hp
          refine ⟨h2, fun d hd => ?_⟩
          by_cases h1 : d = 1
          · exact Or.inl h1
          · refine Or.inr (Classical.byContradiction fun hne => hc ⟨d, hd, h1, hne⟩)
        obtain ⟨d, hd, h1, hne⟩ := hex
        have hd0 : d ≠ 0 := by
          rintro rfl
          have := Nat.eq_zero_of_zero_dvd hd
          omega
        have hle : d ≤ n := Nat.le_of_dvd (by omega) hd
        have hd2 : 2 ≤ d := by omega
        obtain ⟨p, hp', hpd⟩ := ih d (by omega) hd2
        exact ⟨p, hp', Nat.dvd_trans hpd hd⟩
  exact key n n (Nat.le_refl n) h

end ProofGarden
