import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Division.L07dvd_le
import Game.MyNat.Prime

World "Prime"
Level 2
Title ""


namespace MyNat

/-- -/
DefinitionDoc MyNat.prime as "prime"

NewDefinition MyNat.prime

Introduction
"
  In this level, we will prove that 2 is prime.
"
/-- `two_is_prime` is a proof that 2 is prime .-/
TheoremDoc MyNat.two_is_prime as "two_is_prime" in "prime"



Statement two_is_prime : prime 2 := by
  unfold prime
  Hint "Try using constructor to break down the ∧ into two goals"
  constructor
  apply le_refl
  intro m hm
  Hint "To continue the proof ,consider what assumptions you would need to be able to apply dvd_le"
  have h2 : 2 ≠ 0 := succ_ne_zero 1
  apply dvd_le m 2 hm at h2
  Hint "Try applying le_two"
  apply le_two at h2
  cases h2 with hzero hrest
  rw [hzero] at hm
  apply zero_dvd at hm
  rw [two_eq_succ_one] at hm
  apply succ_ne_zero at hm
  contradiction
  exact hrest

TheoremTab "prime"

Conclusion
"
  Congratulations! You have proven that 2 is prime.
"
