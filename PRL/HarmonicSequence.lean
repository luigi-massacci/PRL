import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem harmonic : ConvergesTo (fun n : ℕ ↦ 1/n) (0) := by
  rw [ConvergesTo]
  intro ε εpos
  have : ∃ N : ℕ, ε⁻¹ < ↑N := by exact exists_nat_gt ε⁻¹
  rcases this with ⟨N, inv_eps_lt_N⟩
  use N
  intro n ngeN
  simp only [one_div, sub_zero]
  have ε_inv_pos : 0 < ε⁻¹ := by exact inv_pos.mpr εpos
  have Npos      : (0 : ℝ) < N := by linarith --lt_trans ε_inv_pos inv_eps_lt_N
  have hN_rev    : (↑N)⁻¹ < ε := inv_lt_of_inv_lt εpos inv_eps_lt_N
  have npos      : 0 < (n : ℝ) := Npos.trans_le (by exact_mod_cast ngeN)
  have nge_rev   : (n : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [inv_le_inv npos Npos]; exact_mod_cast ngeN
  have inv_n_pos : 0 < (↑n)⁻¹:= inv_pos_of_pos npos
  rw [abs_of_pos inv_n_pos]
  apply lt_of_le_of_lt nge_rev hN_rev
