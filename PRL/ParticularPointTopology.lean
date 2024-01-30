import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Order

open Topology TopologicalSpace Set Function Classical Filter
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

theorem isClosed_iff {s : Set (ParticularPointTopology α p)} : IsClosed s ↔ s = univ ∨ p ∉ s := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_empty_iff, mem_compl_iff]

theorem nhds_eq (a : (ParticularPointTopology α p)) : 𝓝 a = 𝓟 {a, p} := by
  ext x
  simp [_root_.mem_nhds_iff, isOpen_iff]
  constructor
  intro ⟨t, htx, htp, hta⟩
  refine insert_subset (htx hta) (singleton_subset_iff.mpr (htx (htp (nonempty_of_mem hta))))
  refine fun h ↦ ⟨{a, p}, h, fun _ ↦ mem_insert_of_mem a rfl, mem_insert a {p}⟩

theorem mem_nhds_iff {a : (ParticularPointTopology α p)} {s : Set (ParticularPointTopology α p)} :
    s ∈ 𝓝 a ↔ a ∈ s ∧ p ∈ s := by
    simp [nhds_eq]
    constructor
    refine fun h ↦ ⟨h <| mem_insert a {p}, h <| mem_insert_of_mem a rfl⟩
    intro h x hx
    aesop

theorem empty_interior_of_closed {s : Set (ParticularPointTopology α p)} (hs : IsClosed s) (huniv : s ≠ univ)
  : interior s = ∅ := by
  simp only [isClosed_iff] at hs
  rcases hs with h | h
  · contradiction
  · have : p ∉ interior s := not_mem_subset interior_subset h
    rcases (@isOpen_iff' _ _ (interior s)).mp <| isOpen_interior
    · assumption
    · contradiction

theorem lem_not_valid (p : α) (hp : {p} ≠ univ) : {↑p} ∪ (interior {↑p}ᶜ) ≠ (univ : Set (ParticularPointTopology α p)) := by
  rcases (isOpen_iff' _).mp isOpen_interior with h | h
  · rw [h]
    aesop
  · rw [empty_interior_of_closed]
    · aesop
    · simp [isClosed_iff]
      simp [isOpen_iff]
    · aesop




end ParticularPointTopology
