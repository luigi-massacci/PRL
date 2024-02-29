import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Pointwise
import Mathlib.Topology.Separation
import Mathlib.Topology.MetricSpace.PseudoMetric

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
  map_katetov (f : F) : isKatetov f

end

export KatetovMapClass (map_katetov)

section KatetovMapClass

variable {F X : Type*} [MetricSpace X]
variable [KatetovMapClass F X]

@[coe] def toKatetovMap (f : F) : E(X) := ⟨f, map_katetov f⟩

instance : CoeTC F E(X) := ⟨toKatetovMap⟩

end KatetovMapClass

#check ContinuousMapClass

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

end KatetovMap

lemma helper (x₀ : X) (f : E(X)) : ∀ x, |f x - dist x x₀| ≤ f x₀ := by
  refine fun x ↦ abs_le.mpr ⟨?_, ?_⟩
  · linarith [(map_katetov f).le_add x x₀]
  · linarith [le_of_abs_le <| (map_katetov f).le_dist x x₀]

theorem bounded_dist {f g : E(X)} : BddAbove {|f x - g x| | x : X} := by
  by_cases hn : Nonempty X
  · have x₀ := Classical.choice ‹Nonempty X›
    refine ⟨f x₀ + g x₀, fun _ ⟨x, hx⟩ ↦ ?_⟩; rw [← hx]
    have h : |f x - g x| ≤ |f x - dist x x₀| + |g x - dist x x₀|:= by
      rw [← abs_sub_comm (dist x x₀) (g x)]; apply abs_sub_le (f x) (dist x x₀) (g x)
    apply le_trans h <| add_le_add (helper x₀ f x) (helper x₀ g x)
  · refine ⟨0, fun _ ⟨x, _⟩ ↦ False.elim (hn ⟨x⟩)⟩

lemma sSup_eq_zero (s : Set ℝ) (hb : BddAbove s) (snonneg : ∀ x ∈ s, 0 ≤ x) (hsup : sSup s = 0)
  : ∀ x ∈ s, x = 0 := by
  refine (fun x xs ↦ le_antisymm (by rw [← hsup]; exact le_csSup hb xs) (snonneg x xs))


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
        apply le_csSup (by apply BddAbove.add <;> apply bounded_dist)
        refine Set.mem_add.mpr ⟨|f x - g x|, |g x - h x|, (by simp)⟩
      · have x₀ := Classical.choice ‹Nonempty X›
        use |f x₀ - g x₀| ; simp
      · apply bounded_dist
      · have x₀ := Classical.choice ‹Nonempty X›
        use |g x₀ - h x₀| ; simp
      · apply bounded_dist
    · apply add_nonneg <;>
      { apply Real.sSup_nonneg; rintro val ⟨x, rfl⟩; apply abs_nonneg}
  eq_of_dist_eq_zero := by
    intro f g h
    simp [dist] at h
    apply sSup_eq_zero at h
    · ext x
      exact eq_of_sub_eq_zero <| abs_eq_zero.mp (h |f x - g x| ⟨x, rfl⟩)
    · apply bounded_dist
    · rintro _ ⟨x, rfl⟩; exact abs_nonneg _
  edist_dist x y:= by exact ENNReal.coe_nnreal_eq _

open Function Set Filter Topology TopologicalSpace Metric


theorem dist_coe_le_dist [Nonempty X] (f g : E(X)) (x : X) : dist (f x) (g x) ≤ dist f g :=
  by refine le_csSup bounded_dist (by simp [dist])

theorem dist_le (C0 : (0 : ℝ) ≤ C) (f g : E(X)) [Nonempty X]:
  dist f g ≤ C ↔ ∀ x : X, dist (f x) (g x) ≤ C := by
  refine ⟨fun h x => le_trans (dist_coe_le_dist _ _ x) h, fun H ↦ ?_⟩
  simp [dist]
  apply Real.sSup_le (by simp [*] at *; assumption) (C0)


noncomputable instance [Nonempty X] : CompleteSpace E(X) :=
  Metric.complete_of_cauchySeq_tendsto fun (u : ℕ → E(X)) (hf : CauchySeq u) => by
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have u_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist _ _ x) (b_bound n m N hn hm)
    have ux_cau : ∀ x, CauchySeq fun n => u n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, u_bdd x, b_lim⟩
    choose f hf using fun x => cauchySeq_tendsto_of_complete (ux_cau x)
    have fF_bdd : ∀ x N, dist (u N x) (f x) ≤ b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hf x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => u_bdd x N n N (le_refl N) hn⟩)
    have kat_f : isKatetov f := by
      constructor <;> intro x y
      · have h₃: ∀ ε > 0, |f x - f y| ≤ 2*ε + dist x y:= by
          intro ε εpos
          rcases Metric.tendsto_atTop.mp (hf x) ε εpos with ⟨Nx, hNx⟩
          rcases Metric.tendsto_atTop.mp (hf y) ε εpos with ⟨Ny, hNy⟩
          simp [dist] at *
          set N := max Nx Ny
          specialize hNx N (show _ by simp)
          specialize hNy N (show _ by simp)
          rw [← add_zero (f x)]
          rw [abs_sub_comm] at hNx
          rw [abs_sub_comm] at hNy
          rw [(show 0 = u N x - u N x + u N y - u N y by ring)]
          have : f x + ((u N) x - (u N) x + (u N) y - (u N) y) - f y
            = (f x - (u N) x) + ((u N) y - f y) + ((u N x) - (u N y)) := by ring
          rw [this]
          have h₄ : |(f x - (u N) x) + ((u N) y - f y) + ((u N x) - (u N y))|
            ≤ |(f x - (u N) x) + ((u N) y - f y)| + |((u N x) - (u N y))| := by
            apply abs_add _ ((u N x) - (u N y))
          have h₅ : |(f x - (u N) x) + ((u N) y - f y)| + |((u N x) - (u N y))|
            ≤ |(f x - (u N) x)| + |((u N) y - f y)| + |((u N x) - (u N y))| :=
            by
            apply add_le_add_right (abs_add (f x - (u N) x) ((u N) y - f y))
          have h₆: |(f x - (u N) x) + ((u N) y - f y) + ((u N x) - (u N y))|
            ≤ |(f x - (u N) x)| + |((u N) y - f y)| + |((u N x) - (u N y))| := by
              apply le_trans h₄ h₅
          have h₇ : |(f x - (u N) x)| + |((u N) y - f y)| + |((u N x) - (u N y))|
            ≤ 2*ε + dist x y := by
              rw [abs_sub_comm _ (f y)]
              have := (map_katetov (u N)).le_dist x y
              linarith
          apply le_trans h₆ h₇
        refine le_of_forall_pos_le_add (fun ε εpos ↦ ?_)
        linarith [(h₃ (ε/2) (by exact half_pos εpos))]
      · have h₁: ∀z,∀ ε > 0, ∃ N, ∀ n ≥ N, |f z - u n z| < ε := by
          intro z
          have := Metric.tendsto_atTop.mp (hf z)
          simp_rw [dist_comm] at this
          exact this
        have h₂: 0 = f x - f x + f y - f y := by ring
        have h₄ : ∀ n, dist x y ≤ u n x + u n y := by intro n; exact (map_katetov (u n)).le_add x y
        have h₃ : ∀ ε > 0, dist x y ≤ f x + f y + 2*ε := by
          intro ε εpos
          have hx := h₁ x ε εpos
          have hy := h₁ y ε εpos
          rcases hx with ⟨Nx, hNx⟩
          rcases hy with ⟨Ny, hNy⟩
          set N := max Nx Ny
          specialize hNx N (show _ by simp)
          specialize hNy N (show _ by simp)
          specialize h₄ N
          rw [← add_zero (u N y)] at h₄
          rw [h₂] at h₄
          have : (u N) x + ((u N) y + (f x - f x + f y - f y)) = f x + f y + (u N x - f x) + (u N y - f y) := by ring
          rw [this] at h₄
          rw [abs_sub_comm] at hNx
          rw [abs_sub_comm] at hNy
          have : (u N) x - f x ≤ ε := by apply le_of_lt (lt_of_abs_lt hNx)
          have : (u N) y - f y ≤ ε := by apply le_of_lt (lt_of_abs_lt hNy)
          have : dist x y ≤ f x + f y + 2*ε := by linarith
          assumption
        apply le_of_forall_pos_le_add
        intro ε εpos
        specialize h₃ (ε/2) (by linarith)
        ring_nf at h₃
        assumption
    · use ⟨f, kat_f⟩
      refine' tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) _ b_lim)
      refine (fun N ↦ (dist_le (b0 N) (u N) ⟨f, kat_f⟩).mpr (fun x => fF_bdd x N))

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
      linarith [le_of_abs_le ((map_katetov f).le_dist z y)]
    · exact (map_katetov f).le_add x z
    · linarith [le_of_abs_le ((map_katetov f).le_dist x y)]
    · exact dist_triangle x y z
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
