import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Order

open Set Filter Topology TopologicalSpace

@[simp]
def ParticularPointTopology {α : Type*} (p : α) := {∅} ∪ {S : Set α | p ∈ S}

variable {α : Type*} (p : α)

instance : TopologicalSpace α where
  IsOpen := ParticularPointTopology p
  isOpen_univ := by
    simp
    right
    trivial
  isOpen_inter := by
    simp; refine fun s t hs ht ↦ ?_
    rcases hs with e | ne
    left
    aesop
    rcases ht with e | ne₁
    left
    aesop
    right
    exact ⟨ne, ne₁⟩
  isOpen_sUnion := by
    simp; intro S hS
    by_cases h: Set.Nonempty (⋃₀ S)
    choose! w hw using (Nonempty.of_sUnion h)
    rcases (hS w hw) with e | ne
    left
    sorry
    sorry
    sorry



namespace ParticularPointTopology



end ParticularPointTopology
