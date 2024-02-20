import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint

variable {X : Type _} [MetricSpace X] [Nonempty X]

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


def E (X: Type*) [MetricSpace X] := {f : X → ℝ | isKatetov f}

theorem E_def : f ∈ E X ↔ isKatetov f := by simp [E]

instance : MetricSpace (E X) where
  dist f g := sSup {|(f : X → ℝ) x - (g : X → ℝ) x| | x : X}
  dist_self f := by simp [dist]
  dist_comm f g := by simp [dist, abs_sub_comm]
  dist_triangle f g h := by
    have x₀ := Classical.choice ‹Nonempty X›
    have hf : ∀ x, |(f : X → ℝ) x - dist x x₀| ≤ (f : X → ℝ) x₀ := by
      intro x
      have := @isKatetov.le_add _ _ f (E_def.mp (by aesop)) x x₀
      refine abs_le.mpr ?_
      constructor
      · linarith
      · have := le_of_abs_le (@isKatetov.le_dist _ _ f (E_def.mp (by aesop)) x x₀)
        linarith
    have hg : ∀ x, |(g : X → ℝ) x - dist x x₀| ≤ (g : X → ℝ) x₀ := by
      intro x
      have := @isKatetov.le_add _ _ g (E_def.mp (by aesop)) x x₀
      refine abs_le.mpr ?_
      constructor
      · linarith
      · have := le_of_abs_le (@isKatetov.le_dist _ _ g (E_def.mp (by aesop)) x x₀)
        linarith
    have h₁: ∀ x, |(f : X → ℝ) x - dist x x₀| + |(g : X → ℝ) x - dist x x₀|  ≤ (f : X → ℝ) x₀ + (g : X → ℝ) x₀ := by
      intro x
      exact add_le_add (hf x) (hg x)
    have h₂ : ∀ (x : X), |(f : X → ℝ)  x - (g : X → ℝ) x| ≤ |(f : X → ℝ) x - dist x x₀| + |(g : X → ℝ) x - dist x x₀|:= by
      intro x
      rw [← abs_sub_comm (dist x x₀) ((g : X → ℝ) x)]
      apply abs_sub_le ((f : X → ℝ) x) (dist x x₀) ((g : X → ℝ) x)
    have : ∀ x, |(f : X → ℝ) x - (g : X → ℝ) x| ≤ (f : X → ℝ) x₀ + (g : X → ℝ) x₀ := by
      intro x
      exact le_trans (h₂ x) (h₁ x)
    simp [dist]
    sorry
    -- set s := fun (f g : E X) ↦ {|(f : X → ℝ) x - (g : X → ℝ) x| | x : X} with s_def
    -- have : ∀ f g, Set.Nonempty (s f g) := by
    --   intro f g
    --   simp [s_def]
    --   use |(f : X → ℝ) x₀ - (g : X → ℝ) x₀|
    --   simp
