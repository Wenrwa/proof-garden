/-!
# Lemma: if a square is even, the number is even

An odd number times an odd number is odd, so if `p * p` is even then `p` is.
-/

namespace ProofGarden

/-- If 2 divides `p * p`, then 2 divides `p`. -/
theorem two_dvd_of_two_dvd_mul_self {p : Nat} (h : 2 ∣ p * p) : 2 ∣ p := by
  rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
  · exact Nat.dvd_of_mod_eq_zero h0
  · exfalso
    have hsq : (p * p) % 2 = 1 := by
      rw [Nat.mul_mod, h1]
    have hdiv : (p * p) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    omega

end ProofGarden
