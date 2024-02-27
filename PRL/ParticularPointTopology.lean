import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Order

open Topology TopologicalSpace Set Function Classical Filter

/-- A type synonym equipped with the topology whose open sets are the empty set
and the sets containing a specified point -/


def ParticularPoint (X : Type*) (p : X) := X

namespace ParticularPoint

def of : X ≃ ParticularPoint X p:=
  Equiv.refl X

variable {X : Type*} (p : X) {s : Set (ParticularPoint X p)} (a : (ParticularPoint X p))

instance : TopologicalSpace (ParticularPoint X p) where
  IsOpen s := s.Nonempty → p ∈ s
  isOpen_univ := by simp only [mem_univ, implies_true]
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    exact ⟨hs ⟨x, hxs⟩, ht ⟨x, hxt⟩⟩
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hxt⟩
    exact mem_sUnion_of_mem (h t hts ⟨x, hxt⟩) hts

theorem isOpen_iff  : IsOpen s ↔ s.Nonempty → p ∈ s :=
  Iff.rfl

theorem isOpen_iff' : IsOpen s ↔ s = ∅ ∨ p ∈ s := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem isClosed_iff : IsClosed s ↔ s = univ ∨ p ∉ s := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_empty_iff, mem_compl_iff]

theorem nhds_eq : 𝓝 a = 𝓟 {a, p} := by
  ext u
  simp [_root_.mem_nhds_iff, isOpen_iff]
  constructor
  intro ⟨t, htu, htp, hta⟩
  refine insert_subset (htu hta) (singleton_subset_iff.mpr (htu (htp (nonempty_of_mem hta))))
  refine fun h ↦ ⟨{a, p}, h, fun _ ↦ mem_insert_of_mem a rfl, mem_insert a {p}⟩

theorem mem_nhds_iff :
    s ∈ 𝓝 a ↔ a ∈ s ∧ p ∈ s := by
    simp [nhds_eq]
    constructor
    refine fun h ↦ ⟨h <| mem_insert a {p}, h <| mem_insert_of_mem a rfl⟩
    rintro ⟨as, ps⟩ x (hx | hx) <;> (rw [hx]; assumption)

theorem empty_interior_of_closed {s : Set (ParticularPoint X p)} (hs : IsClosed s) (huniv : s ≠ univ)
  : interior s = ∅ := by
  simp only [isClosed_iff] at hs
  rcases hs with h | h
  · contradiction
  · have : p ∉ interior s := not_mem_subset interior_subset h
    rcases (@isOpen_iff' _ _ (interior s)).mp <| isOpen_interior
    · assumption
    · contradiction

instance : T0Space (ParticularPoint X p) where
  t0 x y h:= by
    have : y ∈ {x, p} ∧ p ∈ {x, p} := by
      rw [← (@mem_nhds_iff _ _ {x, p}), ← h]; simp [nhds_eq, subset_refl]
    have : x ∈ {y, p} ∧ p ∈ {y, p} := by
      rw [← (@mem_nhds_iff _ _ {y, p}), h]; simp [nhds_eq, subset_refl]
    aesop

instance : SeparableSpace (ParticularPoint X p) where
  exists_countable_dense := by
    refine ⟨{p}, countable_singleton p, dense_iff_inter_open.mpr ?_⟩
    refine fun U h₁ h₂ ↦ inter_singleton_nonempty.mpr <| ((isOpen_iff _).mp h₁ h₂)

instance : FirstCountableTopology (ParticularPoint X p) where
  nhds_generated_countable := by
    refine fun a ↦ ⟨{{a, p}}, ?_⟩
    simp only [countable_singleton, nhds_eq, generate_singleton, and_self]

theorem lem_not_valid (p : X) (hp : {p} ≠ univ) : {↑p} ∪ (interior {↑p}ᶜ) ≠ (univ : Set (ParticularPoint X p)) := by
  rcases (isOpen_iff' _).mp isOpen_interior with h | _
  · rw [h]
    aesop
  · rw [empty_interior_of_closed]
    · aesop
    · simp [isClosed_iff, isOpen_iff]
    · aesop


end ParticularPoint
