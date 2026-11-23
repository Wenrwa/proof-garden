import ProofGarden.Defs

/-!
# Euclid's lemma

If a prime divides a product, it divides one of the factors. This is the fact
that makes prime factorisations unique.
-/

namespace ProofGarden

/-- If `p` is prime and `p ∣ a * b`, then `p ∣ a` or `p ∣ b`. -/
theorem euclids_lemma {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · refine Or.inr ?_
    -- `gcd p a` divides `p`, so it is `1` or `p`; it cannot be `p` since `p ∤ a`.
    have hcop : Nat.Coprime p a := by
      rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | h1
      · exact h1
      · exfalso
        apply hpa
        rw [← h1]
        exact Nat.gcd_dvd_right p a
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop h

end ProofGarden
