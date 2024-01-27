import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Order

open Set Filter Topology TopologicalSpace

def ParticularPointTopology (α : Type*) (p : α) := α

namespace ParticularPointTopology

instance {α : Type*} (p : α) : Inhabited (ParticularPointTopology α p) where
  default := p

def of : α ≃ ParticularPointTopology α p:=
  Equiv.refl α

variable {α : Type*} (p : α)

instance : TopologicalSpace (ParticularPointTopology α p) where
  IsOpen s := s.Nonempty → p ∈ s
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    exact ⟨hs ⟨x, hxs⟩, ht ⟨x, hxt⟩⟩
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hxt⟩
    exact mem_sUnion_of_mem (h t hts ⟨x, hxt⟩) hts





end ParticularPointTopology
