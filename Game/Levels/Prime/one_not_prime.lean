import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Division.L07dvd_le


World "Prime"
Level 4
Title "one_not_prime"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that one is not prime.
"
/-- `one_not_prime` is a proof that 1 is not prime .-/
TheoremDoc MyNat.one_not_prime as "one_not_prime" in "∣"


Statement one_not_prime
  : (∃ y, y ∣ 1 ∧ y ≠ 1 ∧ y ≠ 1)  ∨ (1<=2) := by
  right
  decide
