import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint

variable {X : Type _} [MetricSpace X]

class isKatetov (f : X → ℝ) : Prop where
  le_dist : ∀ x y, |f x - f y| ≤ dist x y
  le_add : ∀ x y, dist x y ≤ f x + f y

theorem katetov_nonneg {f : X → ℝ} (h : isKatetov f) (x : X) : 0 ≤ f x := by
  have : 0 ≤ f x + f x := by rw [← dist_self x]; exact isKatetov.le_add x x
  linarith

instance (f : X → ℝ) (h : isKatetov f) : PseudoMetricSpace (OnePoint X) where
  dist x y :=
    match x, y with
    | none, none => 0
    | some x, none => f x
    | some x, some y => dist x y
    | none, some y => f y
  dist_self x := by
    rcases x with none | x <;> simp
  dist_comm x y:= by
    cases x <;> cases y <;> simp [dist_comm]
  dist_triangle x y z := by
    rcases x with none | x <;> rcases y with none | y <;> rcases z with none | z <;> simp
    · exact katetov_nonneg h y
    · rw [dist_comm]
      have := le_of_abs_le (@isKatetov.le_dist _ _ f _ z y)
      linarith
    · exact isKatetov.le_add x z
    · have := le_of_abs_le (@isKatetov.le_dist _ _ f _ x y)
      linarith
    · exact dist_triangle x y z
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
