import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Order

open Topology TopologicalSpace Set Function Classical Filter

/-!
# Particular Point topology

This file introduces the Scott Particular Point topology on a type.

## Main definitions


## Main statements


## Implementation notes


## References


## Tags

Particular Point topology
-/

section ParticularPoint

/- A nonempty set `s` is open in the Particular Point topology iff
it contains some particular point p -/
def ParticularPoint (α : Type*) (p : α) : TopologicalSpace α where
  IsOpen s := s.Nonempty → p ∈ s
  isOpen_univ := by simp only [mem_univ, implies_true]
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    exact ⟨hs ⟨x, hxs⟩, ht ⟨x, hxt⟩⟩
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hxt⟩
    exact mem_sUnion_of_mem (h t hts ⟨x, hxt⟩) hts

variable (α : Type*) (p : α) [TopologicalSpace α]

/-- Predicate for a topological space to be equipped with the Particular Point Topology for some point. -/
class IsParticularPoint : Prop where
  topology_eq_particularPoint : ‹TopologicalSpace α› = ParticularPoint α p

instance : @IsParticularPoint α p (ParticularPoint α p) :=
  @IsParticularPoint.mk _ _ (ParticularPoint α p) rfl

namespace IsParticularPoint
variable (α: Type*) (p : α) [TopologicalSpace α] [IsParticularPoint α p] {s : Set α}

lemma topology_eq : ‹_› = ParticularPoint α p := topology_eq_particularPoint

lemma isOpen_iff :
    IsOpen s ↔ s.Nonempty → p ∈ s := by erw [@topology_eq α p _]; rfl

lemma isOpen_iff' : IsOpen s ↔ s = ∅ ∨ p ∈ s := by
  simp only [isOpen_iff α p, nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem isClosed_iff : IsClosed s ↔ s = univ ∨ p ∉ s := by
  simp only [← isOpen_compl_iff, isOpen_iff' α p , compl_empty_iff, mem_compl_iff]

theorem nhds_eq (a : α) : 𝓝 a = 𝓟 {a, p} := by
  ext u
  simp [_root_.mem_nhds_iff, isOpen_iff]
  constructor
  intro ⟨t, htu, htp, hta⟩
  refine insert_subset (htu hta) (singleton_subset_iff.mpr (htu ?_))
  exact (isOpen_iff α p).mp htp (Set.nonempty_of_mem hta)
  refine fun h ↦ ⟨{a, p}, h, ?_, mem_insert a {p}⟩
  refine (isOpen_iff α p).mpr (fun _ ↦ mem_insert_of_mem a rfl)

theorem mem_nhds_iff {a : α} :
    s ∈ 𝓝 a ↔ a ∈ s ∧ p ∈ s := by
    simp [nhds_eq α p]
    constructor
    refine fun h ↦ ⟨h <| mem_insert a {p}, h <| mem_insert_of_mem a rfl⟩
    rintro ⟨as, ps⟩ x (hx | hx) <;> (rw [hx]; assumption)

theorem empty_interior_of_closed (hs : IsClosed s) (huniv : s ≠ univ)
  : interior s = ∅ := by
  simp only [isClosed_iff α p] at hs
  rcases hs with h | h
  · contradiction
  · have : p ∉ interior s := not_mem_subset interior_subset h
    rcases (@isOpen_iff' α p _ _ (interior s)).mp <| isOpen_interior
    · assumption
    · contradiction

end IsParticularPoint

def WithParticularPoint (α : Type*) (p : α) := α

namespace WithParticularPoint

@[match_pattern] def toParticularPoint : α ≃ WithParticularPoint α p := Equiv.refl _

/-- `ofParticularPoint` is the identity function from the `WithParticularPoint` of a type. -/
@[match_pattern] def ofParticularPoint : WithParticularPoint α p ≃ α := Equiv.refl _

@[simp] lemma toParticularPoint_symm_eq : (@toParticularPoint α p).symm = ofParticularPoint α p:= rfl
@[simp] lemma ofParticularPoint_symm_eq : (@ofParticularPoint α p).symm = toParticularPoint α p := rfl
@[simp] lemma toParticularPoint_ofParticularPoint (a : WithParticularPoint α p) : toParticularPoint α p (ofParticularPoint α p a) = a := rfl
@[simp] lemma ofParticularPoint_toParticularPoint (a : α) : ofParticularPoint α p (toParticularPoint α p a) = a := rfl


/-- A recursor for `WithParticularPoint`. Use as `induction x using WithParticularPoint.rec`. -/
protected def rec {β : WithParticularPoint α p → Sort _}
    (h : ∀ a, β (toParticularPoint α p a)) : ∀ a, β a := fun a ↦ h (ofParticularPoint α p a)

instance : Nonempty (WithParticularPoint α p) := by exact Nonempty.intro p
instance : Inhabited (WithParticularPoint α p) := by exact { default := p }

instance : TopologicalSpace (WithParticularPoint α p) := ParticularPoint α p
instance : IsParticularPoint (WithParticularPoint α p) p := ⟨rfl⟩

end WithParticularPoint

open IsParticularPoint

instance : T0Space (WithParticularPoint α p) where
  t0 x y h:= by
    have : y ∈ {x, p} ∧ p ∈ {x, p} := by
      rw [← (@mem_nhds_iff (WithParticularPoint α p) _ _ _ {x, p}), ← h];
      simp [@nhds_eq (WithParticularPoint α p) p, subset_refl]
    have : x ∈ {y, p} ∧ p ∈ {y, p} := by
      rw [← (@mem_nhds_iff (WithParticularPoint α p) _ _ _ {y, p}), h];
      simp [@nhds_eq (WithParticularPoint α p) p, subset_refl]
    aesop

instance : SeparableSpace (WithParticularPoint α p) where
  exists_countable_dense := by
    refine ⟨{p}, countable_singleton p, dense_iff_inter_open.mpr ?_⟩
    refine fun U h₁ h₂ ↦ inter_singleton_nonempty.mpr <| (isOpen_iff (WithParticularPoint α p) p).mp h₁ h₂

instance : FirstCountableTopology (WithParticularPoint α p) where
  nhds_generated_countable := by
    refine fun a ↦ ⟨{{a, p}}, ?_⟩
    simp only [countable_singleton, nhds_eq (WithParticularPoint α p) p, generate_singleton, and_self]

end ParticularPoint
