import ProofGarden.Defs

/-!
# Powers of two add up to one less than the next

`1 + 2 + 4 + ... + 2ⁿ⁻¹ = 2ⁿ - 1`: a binary number made of `n` ones is one
short of `2ⁿ`. Stated with `+ 1` on the left to avoid natural-number subtraction.
-/

namespace ProofGarden

/-- `(2⁰ + 2¹ + ... + 2ⁿ⁻¹) + 1 = 2ⁿ`. -/
theorem sum_powers_of_two (n : Nat) : sumRange n (fun i => 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hs : sumRange (k + 1) (fun i => 2 ^ i) = sumRange k (fun i => 2 ^ i) + 2 ^ k := rfl
    rw [hs, Nat.pow_succ]
    omega

end ProofGarden
