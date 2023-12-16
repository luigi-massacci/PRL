import Mathlib.Tactic
import Mathlib.Data.Set.Function

variable (P : Prop)

#check Fin 2
#eval (0 : Fin 2)
#eval (5 : Fin 2)

lemma or_distrib (A B C) : A ∨ (B ∧ C) ↔ (B ∨ A) ∧ (C ∨ A) := by aesop

lemma contrapositive (P Q : Prop): (P → Q) → (¬Q → ¬P) := fun pq nq p ↦ nq (pq p)

theorem lem : P ∨ ¬P := by
  set U : Set (Fin 2) := {x | x = 0 ∨ P} with U_def
  set V : Set (Fin 2) := {x | x = 1 ∨ P} with V_def
  have zero_in_U: 0 ∈ U := by simp
  have zero_in_V : 1 ∈ V := by simp
  set UV : Set (Set (Fin 2)) := {U, V} with UV_def
  have nempU : Set.Nonempty U := by exact Set.nonempty_of_mem zero_in_U
  have nempV : Set.Nonempty V := by exact Set.nonempty_of_mem zero_in_V
  have : ∀ S ∈ UV, Set.Nonempty S:= by
    intro S hS
    cases' hS with u v
    rw [u]
    assumption
    rw [v]
    assumption
  have : ∀ S ∈ UV, ∃ n ∈ S, n = 0 ∨ n = 1 := by
    intro s hs
    cases' hs with u v
    rw [u]
    use 0
    simp
    rw [v]
    use 1
    simp
  choose! f hf using this
  have P_to_U_eq_V: P → (U = V) := by
    intro p
    ext x
    simp
    constructor
    refine fun _ ↦ Or.inr p
    refine fun _ ↦ Or.inr p
  have fU := (hf U (by exact Set.mem_insert U {V})).1
  have fV := (hf V (by exact Set.mem_insert_of_mem U V_def)).1
  have : (f U = 0 ∨ P) ∧ (f V = 1 ∨ P) := by
    have fUP : f U = 1 → P := by
      intro h; simp [h] at fU; assumption
    have fVP : f V = 0 → P := by
      intro h; simp [h] at fV; assumption
    have hfU : f U = 0 ∨ f U = 1 := (hf U (by exact Set.mem_insert U {V})).2
    have hfV : f V = 0 ∨ f V = 1 := (hf V (by exact Set.mem_insert_of_mem U V_def)).2
    cases' hfU with fU0 fU1
    cases' hfV with fV0 fV1
    exact ⟨Or.inl fU0, Or.inr (fVP fV0)⟩
    exact ⟨Or.inl fU0, Or.inl fV1⟩
    cases' hfV with fV0 fV1
    exact ⟨Or.inr (fUP fU1), Or.inr (fVP fV0)⟩
    exact ⟨Or.inr (fUP fU1), Or.inl fV1⟩
  have lem₁ : P ∨ (f U ≠ f V) := by
    have := (or_distrib _ _ _).mpr this
    cases' this with hp hf₂
    left
    assumption
    right
    intro h
    rw [h] at hf₂
    have : (0 : Fin 2) = 1 := by
      rw [← hf₂.1]
      rw [← hf₂.2]
    norm_num at this
  cases' lem₁ with p np
  left
  assumption
  right
  apply contrapositive
  exact P_to_U_eq_V
  intro h
  rw [h] at np
  contradiction

variable (X Y : Type _) (f : X → Y) [TopologicalSpace X] [TopologicalSpace Y]
variable (A : Set X)

open Topology TopologicalSpace
open Function

example (hf : Continuous f) (hf₂ : Surjective f) (hA : Dense A) : Dense (f '' A) := by
  refine dense_iff_inter_open.mpr ?_
  intro U openU nemptyU
  have : IsOpen (f⁻¹' U) := by exact IsOpen.preimage hf openU
  have h : Set.Nonempty ((f⁻¹' U) ∩ A) := by
    apply Dense.inter_open_nonempty hA (f ⁻¹' U) this ?_
    exact Set.Nonempty.preimage nemptyU hf₂
  have sub : f '' ((f⁻¹' U) ∩ A) ⊆ f '' (f⁻¹' U) ∩ f '' A := by exact Set.image_inter_subset _ _ _
  rw [Set.image_preimage_eq U hf₂] at sub
  rw [Set.inter_comm] at sub
  have : Set.Nonempty (f '' (A ∩ f⁻¹' U)) := by
    rw [Set.inter_comm]
    apply Set.Nonempty.image
    exact h
  exact Set.Nonempty.mono sub this
