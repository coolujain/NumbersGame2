import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Prime.is_prime_two_unfold

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
  (h1 : prime m)
  (h2 : prime n):
  ¬ prime (m*n) := by
  unfold prime
  intro h3
  cases h3 with h13 h23
  have h4 : n ∣ m * n := by
    use m
    rw [mul_comm]
    rfl
  have h5 := h23 n h4
  unfold prime at h2
  cases h5 with h51 h52
  rw [h51] at h2
  cases h2 with h21 h22
  cases h21
  rw [one_eq_succ_zero] at h
  rw [two_eq_succ_one] at h
  rw [succ_add] at h
  apply succ_inj at h
  rw [one_eq_succ_zero] at h
  rw [succ_add] at h
  apply zero_ne_succ at h
  exact h
  unfold prime at h1
  cases n
  cases h2 with h21 h22
  cases h21
  rw [two_eq_succ_one] at h
  rw [succ_add] at h
  apply zero_ne_succ at h
  exact h
  have h6: succ a  ≠  0  := succ_ne_zero a
  symm at h52
  rw [mul_comm] at h52
  apply mul_right_eq_self at h52
  rw [h52] at h1
  cases h1 with h12 h22
  cases h12
  rw [one_eq_succ_zero] at h
  rw [two_eq_succ_one] at h
  rw [succ_add] at h
  apply succ_inj at h
  rw [one_eq_succ_zero] at h
  rw [succ_add] at h
  apply zero_ne_succ at h
  exact h
  exact h6

Conclusion
"
  Congratulations, you have proven the last theorem in prime world!
"
