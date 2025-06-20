import Mathlib.Init.Core
import Game.MyNat.Definition
import Game.MyNat.Multiplication
import Game.MyNat.Division
import Game.MyNat.LE



namespace MyNat



def prime (p : ℕ) := 2 ≤ p ∧ ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p




end MyNat
