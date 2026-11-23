import ProofGarden.Defs
import ProofGarden.Lemmas.GaussDouble

/-!
# Nicomachus's theorem

The sum of the first cubes is the square of the sum of the first numbers:
`1³ + 2³ + ... + n³ = (1 + 2 + ... + n)²`.
-/

namespace ProofGarden

/-- Algebra step: if `2 * s = k * (k + 1)` then `s² + (k+1)³ = (s + (k+1))²`. -/
theorem nicomachus_step (s k : Nat) (h : 2 * s = k * (k + 1)) :
    s * s + (k + 1) ^ 3 = (s + (k + 1)) * (s + (k + 1)) := by
  have hk : 2 * s * (k + 1) = k * (k + 1) * (k + 1) := by rw [h]
  have hc : (k + 1) ^ 3 = (k + 1) * (k + 1) * (k + 1) := by rw [Nat.pow_succ, Nat.pow_two]
  rw [hc]
  grind

/-- `0³ + 1³ + ... + n³ = (0 + 1 + ... + n)²`. -/
theorem nicomachus (n : Nat) :
    sumRange (n + 1) (fun i => i ^ 3) = (sumRange (n + 1) (fun i => i)) ^ 2 := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    show sumRange (k + 1) (fun i => i ^ 3) + (k + 1) ^ 3
      = (sumRange (k + 1) (fun i => i) + (k + 1)) ^ 2
    rw [ih, Nat.pow_two, Nat.pow_two]
    exact nicomachus_step (sumRange (k + 1) (fun i => i)) k (two_mul_sum_upto k)

end ProofGarden
