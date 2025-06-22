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
/-- `not_prime_four ` is a proof that `if a prime number divides another prime, then these two primes are equal`.-/
TheoremDoc MyNat.not_prime_four as "not_prime_four" in "∣"

def prime (n :  ℕ) : Prop :=
  2 <= n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

Statement not_prime_four:
  ¬ prime 4 := by
  intro h
  unfold prime at h
  cases h with h1 h2
  have h3 : (succ 1) ∣ 4 := by
    use (succ 1)
    decide
  have h4 : (succ 1) = 1 ∨ (succ 1) = 4 :=
    h2 (succ 1) h3
  cases h4 with left right
  trivial
  trivial


Conclusion
"
  Congratulations!
"
