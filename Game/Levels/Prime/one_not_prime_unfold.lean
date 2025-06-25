import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Division.L07dvd_le
import Game.Levels.Prime.is_prime_two_unfold

World "Prime"
Level 1
Title "one_not_prime"

TheoremTab "prime"

namespace MyNat

Introduction
"
  In this level, we will prove that one is not prime.
"
/-- `one_not_prime` is a proof that 1 is not prime .-/
TheoremDoc MyNat.one_not_prime as "one_not_prime" in "prime"


Statement one_not_prime
: ¬ prime 1 := by
  Hint "Try 'unfold prime'"
  unfold prime
  intro h
  cases h with h1 h2
  rw [two_eq_succ_one] at h1
  cases h1
  rw [succ_add] at h
  rw [one_eq_succ_zero] at h
  apply succ_inj at h
  rw [succ_add] at h
  apply zero_ne_succ at h
  exact h


Conclusion
"
  Congratulations! You have proven your first level in prime world.
"
