import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Division.L07dvd_le

World "Prime"
Level 1
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that 2 is prime.
"
/-- `two_is_prime` is a proof that 2 is prime .-/
TheoremDoc MyNat.two_is_prime as "two_is_prime" in "∣"

def prime (n :  ℕ) : Prop :=
  2 <= n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

      
Statement two_is_prime
   : prime 2 := by
  unfold prime
  constructor
  apply le_refl
  intro m hm 
  have h2 : 2 ≠ 0 := succ_ne_zero 1
  apply dvd_le m 2 hm at h2 
  apply le_two at h2
  cases h2 with hzero hrest
  rw [hzero] at hm
  apply zero_dvd at hm
  rw [two_eq_succ_one] at hm
  apply succ_ne_zero at hm
  tauto
  exact hrest
