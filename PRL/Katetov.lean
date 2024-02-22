import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Pointwise

variable {X : Type _} [MetricSpace X]

class isKatetov (f : X → ℝ) : Prop where
  le_dist : ∀ x y, |f x - f y| ≤ dist x y
  le_add : ∀ x y, dist x y ≤ f x + f y

-- Make into packages structor like Stieltjes This is more like "Continuous"

theorem katetov_nonneg {f : X → ℝ} (h : isKatetov f) (x : X) : 0 ≤ f x := by
  have : 0 ≤ f x + f x := by rw [← dist_self x]; exact isKatetov.le_add x x
  linarith

instance {f : X → ℝ} (h : isKatetov f) : PseudoMetricSpace (OnePoint X) where
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



-- def E (X: Type*) [MetricSpace X] := {f : X → ℝ | isKatetov f}

structure KatetovMap (X : Type*) [MetricSpace X] where
  toFun : X → ℝ
  isKatetovtoFun : isKatetov toFun

notation "E(" X ")" => KatetovMap X

class KatetovMapClass (F : Type*) (X : outParam <| Type*) [MetricSpace X]
  extends FunLike F X fun _ => ℝ where
  /-- Continuity -/
  map_katetov (f : F) : isKatetov f

-- @[ext]
-- theorem ext {f g : E(X)} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
--   FunLike.ext _ _ h

-- theorem E_def : f ∈ E X ↔ isKatetov f := by simp [E]

lemma helper (x₀ : X) (h : isKatetov f) : ∀ x, |f x - dist x x₀| ≤ f x₀ := by
  refine fun x ↦ abs_le.mpr ?_
  constructor
  · have := @isKatetov.le_add _ _ f h x x₀
    linarith
  · have := le_of_abs_le (@isKatetov.le_dist _ _ f h x x₀)
    linarith

theorem bounded_dist {f g : X → ℝ} (hf : isKatetov f) (hg : isKatetov g) : BddAbove {|f x - g x| | x : X} := by
  by_cases hn : Nonempty X
  · have x₀ := Classical.choice ‹Nonempty X›
    refine ⟨f x₀ + g x₀, fun _ ⟨x, hx⟩ ↦ ?_⟩
    rw [← hx]
    have h₂ : |f x - g x| ≤ |f x - dist x x₀| + |g x - dist x x₀|:= by
      rw [← abs_sub_comm (dist x x₀) (g x)]
      apply abs_sub_le (f x) (dist x x₀) (g x)
    exact le_trans h₂ (add_le_add (helper x₀ hf x) (helper x₀ hg x))
  · refine ⟨0, fun _ ⟨x, hx⟩ ↦ False.elim (hn ⟨x⟩)⟩

lemma sSup_eq_zero (s : Set ℝ) (hb : BddAbove s) (snonneg : ∀ x ∈ s, 0 ≤ x) (hsup : sSup s = 0) : ∀ x ∈ s, x = 0 := by
  intro x xs
  apply le_antisymm
  rw [← hsup]
  exact le_csSup hb xs
  exact snonneg x xs


noncomputable instance [Nonempty X] : MetricSpace E(X) where
  dist f g := sSup {|f.toFun x - g.toFun x| | x : X}
  dist_self f := by simp [dist]
  dist_comm f g := by simp [dist, abs_sub_comm]
  dist_triangle f g h := by
    simp [dist]
    apply Real.sSup_le
    · rintro val ⟨x, rfl⟩
      rw [← csSup_add]
      · apply le_trans <| abs_sub_le (f.toFun x) (g.toFun x) (h.toFun x)
        apply le_csSup
        · apply BddAbove.add <;> apply bounded_dist <;> simp [KatetovMap.isKatetovtoFun]
        · refine Set.mem_add.mpr ⟨|f.toFun x - g.toFun x|, |g.toFun x - h.toFun x|, ?_⟩
          simp
      · have x₀ := Classical.choice ‹Nonempty X›
        use |f.toFun x₀ - g.toFun x₀| ; simp
      · apply bounded_dist <;> simp [KatetovMap.isKatetovtoFun]
      · have x₀ := Classical.choice ‹Nonempty X›
        use |g.toFun x₀ - h.toFun x₀| ; simp
      · apply bounded_dist <;> simp [KatetovMap.isKatetovtoFun]
    · apply add_nonneg <;>
      {
        apply Real.sSup_nonneg
        rintro val ⟨x, rfl⟩
        apply abs_nonneg
      }
  eq_of_dist_eq_zero := by
    intro f g h
    simp [dist] at h
    apply sSup_eq_zero at h
    ·
      exact eq_of_sub_eq_zero <| abs_eq_zero.mp (h |f.toFun x - g.toFun x| ⟨x, rfl⟩)
    · apply bounded_dist <;> simp [KatetovMap.isKatetovtoFun]
    · rintro _ ⟨x, rfl⟩; exact abs_nonneg _
  edist_dist x y:= by exact ENNReal.coe_nnreal_eq _
