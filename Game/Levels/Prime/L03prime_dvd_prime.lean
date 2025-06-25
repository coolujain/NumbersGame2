import Game.Levels.Division.L10dvd_mul_right
import Game.Levels.Division.L06zero_dvd
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.LessOrEqual.L01le_refl
import Game.MyNat.Division


World "Prime"
Level 3
Title "prime_dvd_prime"

TheoremTab "prime"

namespace MyNat

Introduction
"
  In this level, we will prove that for two primes p and q, if p | q then p = q.

"
/-- `prime_dvd_prime ` is a proof that `if a prime number divides another prime, then these two primes are equal`.-/
TheoremDoc MyNat.prime_dvd_prime as "prime_dvd_prime" in "prime"

Statement prime_dvd_prime
    (p q : ℕ)
    (h1  : 2 ≤ p)
    (h2 : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p)
    (h3  : 2 ≤ q)
    (h4 : ∀ n : ℕ, n ∣ q → n = 1 ∨ n = q)
    (h5  : p ∣ q) :
    p = q := by
  apply h4 at h5
  cases h5
  rw[h] at h1
  rw[one_eq_succ_zero] at h1
  rw[two_eq_succ_one] at h1
  apply succ_le_succ at h1
  apply le_zero at h1
  tauto
  exact h

Conclusion
"
  Well done! This is an important theorem to understand primes.
"
