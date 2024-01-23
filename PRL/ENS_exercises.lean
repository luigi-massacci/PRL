import Mathlib.Tactic
import Mathlib.Order.Interval

theorem strict_mono_or_anti_of_continuos_injective
  (f : ℝ → ℝ) (cont_f : Continuous f) (f_inj : f.Injective) : StrictMono f ∨ StrictAnti f := by
  by_cases h : ∃ x y, x < y ∧ f x < f y
  · left
    by_contra hf
    simp [StrictMono] at hf
    sorry
  · push_neg at h
    right
    refine fun x y x_lt_y ↦ lt_of_le_of_ne (h x y x_lt_y)
      (fun fx_eq_fy ↦ ne_of_lt x_lt_y ((f_inj fx_eq_fy).symm))

#check StrictMonoOn

theorem strict_mono_or_anti_of_continuos_injective'
  (f : ℝ → ℝ) (cont_f : Continuous f) (f_inj : f.Injective) : StrictMono f ∨ StrictAnti f := by
  set A := {(x, y) : ℝ × ℝ | x < y } with A_def
  have h_A : IsPreconnected A := by sorry
  set g : ℝ × ℝ → ℝ := fun (x, y) => f x - f y with g_def
  have cont_g : Continuous g := by continuity
  have h_gA : IsPreconnected (g '' A) := IsPreconnected.image h_A g cont_g.continuousOn
  have g_ne_zero : ∀ x y, x ≠ y → g (x, y) ≠ 0 :=
    fun x y x_ne_y g_eq_zero ↦ x_ne_y (f_inj (sub_eq_zero.mp g_eq_zero))
  have : 0 ∉ g '' A := by aesop
  have gA_I := IsPreconnected.mem_intervals h_gA
  have : (∀ z ∈ g '' A, z < 0) ∨ (∀ z ∈ g '' A, 0 < z):= by sorry
  rcases this with h | h
  case' inl => left
  case' inr => right
  all_goals {
    intro x y x_lt_y
    have := h _ (Set.mem_image_of_mem g (show (x, y) ∈ A by exact x_lt_y))
    aesop
  }
