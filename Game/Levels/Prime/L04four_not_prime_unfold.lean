import Game.Levels.Division.L10dvd_mul_right
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms


World "Prime"
Level 4
Title "four_not_prime"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that four is not prime.

"
/-- `not_prime_four ` is a proof that `four is not prime, basically it is the proof that there exists a number other thn four and one that divide four.`.-/
TheoremDoc MyNat.not_prime_four as "not_prime_four" in "∣"

def prime (n :  ℕ) : Prop :=
  2 <= n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

Statement not_prime_four:
  ¬ prime 4 := by
  intro h
  unfold prime at h
  cases h with h1 h2
  Hint "prove that (succ 1) divides 4"
  have h3 : (succ 1) ∣ 4 := by
    use (succ 1)
    decide
  Hint "apply the definition of prime"
  have h4 : (succ 1) = 1 ∨ (succ 1) = 4 :=
    h2 (succ 1) h3
  cases h4 with left right
  trivial
  trivial


Conclusion
"
  Congratulations!
"
