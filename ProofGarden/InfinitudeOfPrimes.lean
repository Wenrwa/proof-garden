import ProofGarden.Defs
import ProofGarden.Lemmas.Factorial
import ProofGarden.Lemmas.PrimeFactor

/-!
# Euclid: there are infinitely many primes

However large a number `n` you pick, there is a prime bigger than it.
(Any prime factor of `n! + 1` works: it cannot be ≤ `n`, since those all divide `n!`.)
-/

namespace ProofGarden

/-- For every `n` there is a prime `p` with `n < p`. -/
theorem infinitely_many_primes (n : Nat) : ∃ p, n < p ∧ IsPrime p := by
  have h2 : 2 ≤ fact n + 1 := by
    have := fact_pos n
    omega
  obtain ⟨p, hp, hpd⟩ := exists_prime_factor h2
  refine ⟨p, ?_, hp⟩
  refine Classical.byContradiction fun hlt => ?_
  have hpn : p ≤ n := by omega
  have hp2 : 2 ≤ p := hp.1
  have hdiv : p ∣ fact n := dvd_fact (by omega) hpn
  have h1 : p ∣ 1 := (Nat.dvd_add_right hdiv).mp hpd
  have := Nat.le_of_dvd (by omega) h1
  omega

end ProofGarden
