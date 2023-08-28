import Mathlib

open Polynomial
open Nat
open Algebra

theorem prop_1_1_18 (n : Nat) : n^2%3 = 0 ∨ n^2%3 = 1 := by

  have div_3_rem (n : ℕ) : ∃ k : Nat, n = 3*k ∨ n = 3*k+1 ∨ n = 3*k+2 := by
    induction n with
    | zero =>
      apply Exists.intro 0
      apply Or.intro_left
      simp
    | succ d hd =>
      rcases hd with ⟨k, h⟩
      rcases h with h₁ | h₂ | h₃
      {
        apply Exists.intro k
        apply Or.intro_right
        apply Or.intro_left
        rw [h₁]
      }
      {
        apply Exists.intro k
        apply Or.intro_right
        apply Or.intro_right
        rw [h₂]
      }
      {
        apply Exists.intro (k + 1)
        apply Or.intro_left
        rw [h₃, ← Nat.add_succ]
        rfl
      }

  have f := div_3_rem n
  rcases f with ⟨k, h⟩
  rcases h with h₁ | h₂ | h₃
  {
    apply Or.intro_left
    simp [h₁, Nat.pow_succ, Nat.mul_mod]
  }
  {
    apply Or.intro_right
    simp [h₂, Nat.pow_succ, Nat.mul_mod, Nat.add_mod]
  }
  {
    apply Or.intro_right
    simp [h₃, Nat.pow_succ, Nat.mul_mod, Nat.add_mod]
  }

theorem exer_1_1_19 (n : ℕ) : n^2%5 = 0 ∨ n^2%5 = 1 ∨ n^2%5 = 4 := by
  -- TODO: see if `m % n ∈ {0, ..., n - 1}` can be generalized and matched

  have div_5_rem (n : ℕ) :
    ∃ k : ℕ, n = 5*k ∨ n = 5*k+1 ∨ n = 5*k+2 ∨ n = 5*k+3 ∨ n = 5*k+4 :=
  by
    induction n with
    | zero =>
      apply Exists.intro 0
      left
      simp
    | succ d hd =>
      rcases hd with ⟨k, h₁ | h₂ | h₃ | h₄ | h₅⟩
      {
        apply Exists.intro k
        right
        left
        simp [h₁]
      }
      {
        apply Exists.intro k
        right
        right
        left
        simp [h₂]
      }
      {
        apply Exists.intro k
        right
        right
        right
        left
        simp [h₃]
      }
      {
        apply Exists.intro k
        right
        right
        right
        right
        simp [h₄]
      }
      {
        apply Exists.intro (k + 1)
        left
        simp [h₅]
        rfl
      }

  have f := div_5_rem n
  sorry

theorem exer_1_1_20 (a b : ℝ) (h : a^2 - 4*b ≠ 0) :
  ∃ α β c : ℂ, α - β = c ∨ α - β = c * i :=
by
  sorry -- TODO

def Isℚ (x : ℝ) : Prop := ∃ a b : ℤ, b ≠ 0 ∧ x = a / b

-- same as `mul_div_mul_right_eq_div` but without Group instance
-- theorem both_mul (a b c : ℝ) (hc : c ≠ 0) : a / b = (a * c) / (b * c) := by
--  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
--  congr
--  ring_nf
--  rw [mul_assoc, mul_inv_cancel hc]
--  ring_nf

theorem prop_1_1_23 (x y : ℝ) (h₁ : Isℚ x) (h₂ : Isℚ (x + y)) : Isℚ y := by
  rcases h₁ with ⟨a, b, b0, xh⟩
  rcases h₂ with ⟨c, d, d0, sh⟩

  apply Exists.intro (c * b - a * d)
  apply Exists.intro (b * d)
  
  rw [xh] at sh
  sorry

theorem exer_1_1_24 : ℕ := by sorry

