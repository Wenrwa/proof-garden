import ProofGarden.Defs

/-!
# Lemma: twice the sum 0 + 1 + ... + n is n(n+1)

Gauss's pairing trick without division: writing the sum forwards and
backwards and adding gives `n` pairs of `n + 1`. Stated without `/` so it
can be proved by plain induction.
-/

namespace ProofGarden

/-- `2 * (0 + 1 + ... + n) = n * (n + 1)`. -/
theorem two_mul_sum_upto (n : Nat) :
    2 * sumRange (n + 1) (fun i => i) = n * (n + 1) := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    show 2 * (sumRange (k + 1) (fun i => i) + (k + 1)) = (k + 1) * (k + 1 + 1)
    rw [Nat.mul_add, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

end ProofGarden
