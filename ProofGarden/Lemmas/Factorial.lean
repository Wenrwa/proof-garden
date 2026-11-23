import ProofGarden.Defs

/-!
# Lemma: facts about the factorial

Two small facts Euclid's proof needs: `n!` is never zero, and every number
from 1 to `n` divides `n!`.
-/

namespace ProofGarden

/-- The factorial of any number is positive. -/
theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => exact Nat.one_pos
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

/-- Every `k` with `1 ≤ k ≤ n` divides `n!`. -/
theorem dvd_fact {k n : Nat} (h₁ : 1 ≤ k) (h₂ : k ≤ n) : k ∣ fact n := by
  induction n with
  | zero => omega
  | succ m ih =>
    show k ∣ (m + 1) * fact m
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left (fact m) (m + 1))
    · have hkm : k = m + 1 := by omega
      rw [hkm]
      exact Nat.dvd_mul_right (m + 1) (fact m)

end ProofGarden
