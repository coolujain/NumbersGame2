import Game.Levels.Division.L10dvd_mul_right
import Game.MyNat.Division
import Game.MyNat.Prime
import Game.MyNat.PeanoAxioms


World "Prime"
Level 4
Title "four_not_prime"

TheoremTab "prime"

namespace MyNat

/-- -/
DefinitionDoc MyNat.prime as "prime"

NewDefinition MyNat.prime

Introduction
"
  In this level, we will prove that four is not prime.

"
/-- `four_not_prime ` is a proof that `four is not prime, basically it is the proof that there exists a number other thn four and one that divide four.`.-/
TheoremDoc MyNat.four_not_prime as "four_not_prime" in "prime"

Statement four_not_prime:
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
