import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms
import Game.Levels.LessOrEqual.L11le_two
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Division.L07dvd_le

World "Prime"
Level 2
Title "is_prime_two"

TheoremTab "prime"

namespace MyNat

Introduction
"
  In this level, we will prove that 2 is prime.
"
      
/-- `is_prime_two ` is a proof that `2 is a prime number, such that there are no numbers other than 1 and 2 that divide 2. It will be useful to consider using dvd_le.`.-/
TheoremDoc MyNat.is_prime_two as "is_prime_two" in "prime"

Statement is_prime_two
    (m : ℕ) : (2 ≤ 2) ∧ ( m ∣ 2 →  m = 1 ∨ m = 2) := by
    constructor
    decide
    intro h2
    Hint "to continue the proof, consider what assumptions you need to prove to use dvd_le"
    have h4 :2 ≠ 0 := (succ_ne_zero 1)
    apply dvd_le m 2 h2 at h4
    Hint "previously we proved that 0,1 and 2 are less than or equal to 2. "
    apply le_two at h4
    cases h4
    rw[h] at h2
    apply zero_dvd at h2
    tauto
    exact h

Conclusion
"
  My proof:
```
  constructor
    decide
    intro h2
    have h4 :2 ≠ 0 := (succ_ne_zero 1)
    apply dvd_le m 2 h2 at h4
    apply le_two at h4
    cases h4
    rw[h] at h2
    apply zero_dvd at h2
    tauto
    exact h
```
"
