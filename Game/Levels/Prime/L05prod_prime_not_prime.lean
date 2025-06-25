import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd


World "Prime"
Level 5
Title "prod_prime_not_prime"

TheoremTab "prime"

namespace MyNat

Introduction
"
  In this level, we will prove that the product of two prime numbers is not prime.
"
/-- `two_is_prime` is a proof that 2 is prime .-/
TheoremDoc MyNat.prod_prime_not_prime as "prod_prime_not_prime" in "prime"


Statement prod_prime_not_prime
  (m n : ℕ)
  (h1 : m ≥ 2)
  (h2 : ∀ x, x ∣ m → x = 1 ∨ x = m)
  (h3 : n ≥ 2)
  (h4 : ∀ x, x ∣ n → x = 1 ∨ x = n) :
  (∃ y, y ∣ m * n ∧ y ≠ 1 ∧ y ≠ m * n)  ∨ (m*n<=2) := by
  left
  use m
  constructor
  use n
  rfl
  constructor
  intro hm
  rw [hm] at h1
  rw [two_eq_succ_one] at h1
  have h5 : 1<= succ 1 := le_succ_self 1
  have h6 : 1 = succ 1 := le_antisymm 1 (succ 1) h5 h1
  rw [one_eq_succ_zero] at h6
  apply succ_inj at h6
  apply zero_ne_succ at h6
  exact h6
  intro hm
  cases m
  cases h1 with l hl
  rw [two_eq_succ_one] at hl
  rw [succ_add] at hl
  apply zero_ne_succ at hl
  exact hl
  have h5: succ a ≠  0  := succ_ne_zero a
  symm at hm
  apply mul_right_eq_self at hm
  rw [hm] at h3
  cases h3 with k hk
  rw [one_eq_succ_zero] at hk
  rw [two_eq_succ_one] at hk
  rw [succ_add] at hk
  apply succ_inj at hk
  rw [one_eq_succ_zero] at hk
  rw [succ_add] at hk
  apply zero_ne_succ at hk
  exact hk
  exact h5

Conclusion
"
  Congratulations, you have proven the last theorem in prime world!
"
