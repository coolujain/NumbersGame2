import Game.Levels.Division.L10dvd_mul_right
import Game.Levels.Division.L06zero_dvd
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.LessOrEqual.L01le_refl
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms


World "Prime"
Level 2
Title "prime_dvd_prime"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that for two primes p and q, if p | q then p = q.

"
/-- `prime_dvd_prime ` is a proof that `if a prime number divides another prime, then these two primes are equal`.-/
TheoremDoc MyNat.prime_dvd_prime as "prime_dvd_prime" in "∣"

def prime (n :  ℕ) : Prop :=
  2 <= n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

Statement prime_dvd_prime
    (p q : ℕ)
    (h1  : prime p)
    (h2: prime q)
    (h3  : p ∣ q) :
    p = q := by
  unfold prime at h1
  unfold prime at h2
  cases h1 with h1p h2p
  cases h2 with h2q h3q
  apply h3q at h3
  cases h3
  rw[h] at h1p
  rw[one_eq_succ_zero] at h1p
  rw[two_eq_succ_one] at h1p
  apply succ_le_succ at h1p
  apply le_zero at h1p
  tauto
  exact h

Conclusion
"
  Congratulations!
"
