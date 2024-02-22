import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Pointwise

variable {X : Type _} [MetricSpace X]

structure isKatetov (f : X → ℝ) : Prop where
  le_dist : ∀ x y, |f x - f y| ≤ dist x y
  le_add : ∀ x y, dist x y ≤ f x + f y

theorem isKatetov_def {_ : MetricSpace X} {f : X → ℝ} :
  isKatetov f ↔ (∀ x y, |f x - f y| ≤ dist x y) ∧ (∀ x y, dist x y ≤ f x + f y) :=
  ⟨fun h ↦ ⟨h.le_dist, h.le_add⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

structure KatetovMap (X : Type*) [MetricSpace X] where
  protected toFun : X → ℝ
  protected isKatetovtoFun : isKatetov toFun

notation "E(" X ")" => KatetovMap X

section

class KatetovMapClass (F : Type*) (X : outParam <| Type*) [MetricSpace X]
  extends FunLike F X fun _ => ℝ where
  /-- Continuity -/
  map_katetov (f : F) : isKatetov f

end

export KatetovMapClass (map_katetov)

section KatetovMapClass

variable {F X : Type*} [MetricSpace X]
variable [KatetovMapClass F X]

@[coe] def toKatetovMap (f : F) : E(X) := ⟨f, map_katetov f⟩

instance : CoeTC F E(X) := ⟨toKatetovMap⟩

end KatetovMapClass

namespace KatetovMap

variable {X : Type*} [MetricSpace X]

instance funLike : FunLike E(X) X fun _ ↦ ℝ where
  coe := KatetovMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance toKatetovMapClass : KatetovMapClass E(X) X where
  map_katetov := KatetovMap.isKatetovtoFun

@[simp]
theorem toFun_eq_coe {f : E(X)} : f.toFun = (f : X → ℝ) := rfl

instance : CanLift (X → ℝ) E(X) FunLike.coe isKatetov := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

def Simps.apply (f : E(X)) : X → ℝ := f

initialize_simps_projections KatetovMap (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [KatetovMapClass F X] (f : F) :
  ⇑(f : E(X)) = f := rfl

@[ext]
theorem ext {f g : E(X)} (h : ∀ a, f a = g a) : f = g := FunLike.ext _ _ h

protected def copy (f : E(X)) (f' : X → ℝ) (h : f' = f) : E(X) where
  toFun := f'
  isKatetovtoFun := h.symm ▸ f.isKatetovtoFun

@[simp]
theorem coe_copy (f : E(X)) (f' : X → ℝ) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : E(X)) (f' : X → ℝ) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h

variable {f g : E(X)}

theorem katetov_set_coe (s : Set E(X)) (f : s) : isKatetov (f : X → ℝ) :=
  f.1.isKatetovtoFun

theorem coe_injective : @Function.Injective E(X) (X → ℝ) (↑) := fun f g h => by
  cases f; cases g; congr

@[simp]
theorem coe_mk (f : X → ℝ) (h : isKatetov f) : ⇑(⟨f, h⟩ : E(X)) = f :=
  rfl

lemma helper (x₀ : X) (f : E(X)) : ∀ x, |f x - dist x x₀| ≤ f x₀ := by
  refine fun x ↦ abs_le.mpr ?_
  constructor
  · have := (@isKatetov.le_add _ _ _ (map_katetov f) x x₀)
    linarith
  · have := le_of_abs_le (@isKatetov.le_dist _ _ _ (map_katetov f) x x₀)
    linarith

theorem bounded_dist {f g : E(X)} : BddAbove {|f x - g x| | x : X} := by
  by_cases hn : Nonempty X
  · have x₀ := Classical.choice ‹Nonempty X›
    refine ⟨f x₀ + g x₀, fun _ ⟨x, hx⟩ ↦ ?_⟩
    rw [← hx]
    have h₂ : |f x - g x| ≤ |f x - dist x x₀| + |g x - dist x x₀|:= by
      rw [← abs_sub_comm (dist x x₀) (g x)]
      apply abs_sub_le (f x) (dist x x₀) (g x)
    apply le_trans h₂ (add_le_add (helper x₀ f x) (helper x₀ g x))
  · refine ⟨0, fun _ ⟨x, _⟩ ↦ False.elim (hn ⟨x⟩)⟩

lemma sSup_eq_zero (s : Set ℝ) (hb : BddAbove s) (snonneg : ∀ x ∈ s, 0 ≤ x) (hsup : sSup s = 0) : ∀ x ∈ s, x = 0 := by
  intro x xs
  apply le_antisymm
  rw [← hsup]
  exact le_csSup hb xs
  exact snonneg x xs

theorem katetov_nonneg (f : E(X)) (x : X) : 0 ≤ f x := by
  have : 0 ≤ f x + f x := by rw [← dist_self x]; exact (map_katetov f).le_add x x
  linarith

noncomputable instance [Nonempty X] : MetricSpace E(X) where
  dist f g := sSup {|f x - g x| | x : X}
  dist_self f := by simp [dist]
  dist_comm f g := by simp [dist, abs_sub_comm]
  dist_triangle f g h := by
    simp [dist]
    apply Real.sSup_le
    · rintro val ⟨x, rfl⟩
      rw [← csSup_add]
      · apply le_trans <| abs_sub_le (f x) (g x) (h x)
        apply le_csSup
        · apply BddAbove.add <;> apply bounded_dist
        · refine Set.mem_add.mpr ⟨|f.toFun x - g.toFun x|, |g.toFun x - h.toFun x|, ?_⟩; simp
      · have x₀ := Classical.choice ‹Nonempty X›
        use |f.toFun x₀ - g.toFun x₀| ; simp
      · apply bounded_dist
      · have x₀ := Classical.choice ‹Nonempty X›
        use |g.toFun x₀ - h.toFun x₀| ; simp
      · apply bounded_dist
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
    · ext x
      exact eq_of_sub_eq_zero <| abs_eq_zero.mp (h |f.toFun x - g.toFun x| ⟨x, rfl⟩)
    · apply bounded_dist
    · rintro _ ⟨x, rfl⟩; exact abs_nonneg _
  edist_dist x y:= by exact ENNReal.coe_nnreal_eq _


instance (f : E(X)) : PseudoMetricSpace (OnePoint X) where
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
    · exact katetov_nonneg f y
    · rw [dist_comm]
      have := le_of_abs_le ((map_katetov f).le_dist z y)
      linarith
    · exact (map_katetov f).le_add x z
    · have := le_of_abs_le ((map_katetov f).le_dist x y)
      linarith
    · exact dist_triangle x y z
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
