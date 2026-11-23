import ProofGarden.Defs
import ProofGarden.Lemmas.GaussDouble

/-!
# Gauss's sum

The numbers from 1 to `n` add up to `n(n+1)/2`, the trick young Gauss is said
to have used to add 1 to 100 in seconds.
-/

namespace ProofGarden

/-- `1 + 2 + ... + n = n * (n + 1) / 2`. -/
theorem gauss_sum (n : Nat) : sumRange (n + 1) (fun i => i) = n * (n + 1) / 2 := by
  have h := two_mul_sum_upto n
  rw [Nat.mul_comm 2] at h
  exact (Nat.div_eq_of_eq_mul_left (Nat.zero_lt_succ 1) h.symm).symm

end ProofGarden
