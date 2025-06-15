import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Division.L07dvd_ls

World "Prime"
Level 1
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that 2 is prime.
"

def prime (n :  ℕ) : Prop :=
  2 <= n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

      
/-- `is_prime2 ` is a proof that `2 is a prime number`.-/
TheoremDoc MyNat.is_prime2 as "is_prime2" in "∣"

Statement is_prime2
    (m : ℕ) : (2 ≤ 2) ∧ ( m ∣ 2 →  m = 1 ∨ m = 2) := by
    constructor
    decide
    intro h2
    have h4 :2 ≠ 0 := (succ_ne_zero 1) -- when we add the hint add it for this line and the line under by telling them to use dvd_le and use have
    apply dvd_le m 2 h2 at h4
    apply le_two at h4 -- hint..?
    cases h4
    rw[h] at h2
    apply zero_dvd at h2
    tauto
    exact h

Conclusion
"
  Congratulations! You have proven your first theorem about division.
"
