import ProofGarden.Defs

/-!
# The first n odd numbers add up to n²

`1 + 3 + 5 + ... + (2n - 1) = n²`. Picture each odd number as an L-shaped
layer wrapped around a square.
-/

namespace ProofGarden

/-- `1 + 3 + ... + (2n - 1) = n * n`. -/
theorem sum_of_odds (n : Nat) : sumRange n (fun i => 2 * i + 1) = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumRange k (fun i => 2 * i + 1) + (2 * k + 1) = (k + 1) * (k + 1)
    rw [ih]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega

end ProofGarden
