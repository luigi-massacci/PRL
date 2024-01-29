import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Order

open Topology TopologicalSpace Set Function Classical
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

theorem isOpen_iff {s : Set (ParticularPointTopology α p)} : IsOpen s ↔ s.Nonempty → p ∈ s :=
  Iff.rfl

theorem isOpen_iff' {s : Set (ParticularPointTopology α p)} : IsOpen s ↔ s = ∅ ∨ p ∈ s := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

-- theorem isClosed_iff {s : Set (CofiniteTopology α)} : IsClosed s ↔ s = univ ∨ s.Finite := by
--   simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]

-- theorem nhds_eq (a : (ParticularPointTopology α p)) : 𝓝 a = pure p ⊓ pure a := by
--   ext x
--   simp [mem_nhds_iff, isOpen_iff]
--   constructor
--   intro ⟨t, htx, htp, hta⟩
--   exact Filter.mem_inf_of_right (htx hta)
--   rintro ⟨s, hsp, v, hva, hx⟩
--   refine ⟨x, Eq.subset rfl, ?_⟩







-- theorem mem_nhds_iff {a : CofiniteTopology α} {s : Set (CofiniteTopology α)} :
--     s ∈ 𝓝 a ↔ a ∈ s ∧ sᶜ.Finite := by simp [nhds_eq]
-- #align cofinite_topology.mem_nhds_iff CofiniteTopology.mem_nhds_iff



theorem empty_interior_of_closed {s : Set (CofiniteTopology α)} (hs : IsClosed s) : s = ∅ := by
  sorry







end ParticularPointTopology
