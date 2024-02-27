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

* [Steen and Seebach, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

Particular Point topology
-/

section ParticularPoint

/- A nonempty set `s` is open in the Particular Point topology iff
it contains some particular point p -/
def ParticularPoint (X : Type*) (p : X) : TopologicalSpace X where
  IsOpen s := s.Nonempty → p ∈ s
  isOpen_univ := by simp only [mem_univ, implies_true]
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    exact ⟨hs ⟨x, hxs⟩, ht ⟨x, hxt⟩⟩
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hxt⟩
    exact mem_sUnion_of_mem (h t hts ⟨x, hxt⟩) hts

variable (X : Type*) (p : X) [TopologicalSpace X]

/-- Predicate for a topological space to be equipped with the Particular Point Topology for some point. -/
class IsParticularPoint : Prop where
  topology_eq_particularPoint : ‹TopologicalSpace X› = ParticularPoint X p

instance : @IsParticularPoint X p (ParticularPoint X p) :=
  @IsParticularPoint.mk _ _ (ParticularPoint X p) rfl

namespace IsParticularPoint
variable (X: Type*) (p : X) [TopologicalSpace X] [IsParticularPoint X p] {s : Set X}

lemma topology_eq : ‹_› = ParticularPoint X p := topology_eq_particularPoint

lemma isOpen_iff :
    IsOpen s ↔ s.Nonempty → p ∈ s := by erw [@topology_eq X p _]; rfl

lemma isOpen_iff' : IsOpen s ↔ s = ∅ ∨ p ∈ s := by
  simp only [isOpen_iff X p, nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem isClosed_iff : IsClosed s ↔ s = univ ∨ p ∉ s := by
  simp only [← isOpen_compl_iff, isOpen_iff' X p , compl_empty_iff, mem_compl_iff]

theorem nhds_eq (a : X) : 𝓝 a = 𝓟 {a, p} := by
  ext u
  simp [_root_.mem_nhds_iff, isOpen_iff]
  constructor
  intro ⟨t, htu, htp, hta⟩
  refine insert_subset (htu hta) (singleton_subset_iff.mpr (htu ?_))
  exact (isOpen_iff X p).mp htp (Set.nonempty_of_mem hta)
  refine fun h ↦ ⟨{a, p}, h, ?_, mem_insert a {p}⟩
  refine (isOpen_iff X p).mpr (fun _ ↦ mem_insert_of_mem a rfl)

theorem mem_nhds_iff {a : X} :
    s ∈ 𝓝 a ↔ a ∈ s ∧ p ∈ s := by
    simp [nhds_eq X p]
    constructor
    refine fun h ↦ ⟨h <| mem_insert a {p}, h <| mem_insert_of_mem a rfl⟩
    rintro ⟨as, ps⟩ x (hx | hx) <;> (rw [hx]; assumption)

theorem empty_interior_of_closed (hs : IsClosed s) (huniv : s ≠ univ)
  : interior s = ∅ := by
  simp only [isClosed_iff X p] at hs
  rcases hs with h | h
  · contradiction
  · have : p ∉ interior s := not_mem_subset interior_subset h
    rcases (@isOpen_iff' X p _ _ (interior s)).mp <| isOpen_interior
    · assumption
    · contradiction

end IsParticularPoint

def WithParticularPoint (X : Type*) (p : X) := X

namespace WithParticularPoint

@[match_pattern] def toParticularPoint : X ≃ WithParticularPoint X p := Equiv.refl _

/-- `ofParticularPoint` is the identity function from the `WithParticularPoint` of a type. -/
@[match_pattern] def ofParticularPoint : WithParticularPoint X p ≃ X := Equiv.refl _

@[simp] lemma toParticularPoint_symm_eq : (@toParticularPoint X p).symm = ofParticularPoint X p:= rfl
@[simp] lemma ofParticularPoint_symm_eq : (@ofParticularPoint X p).symm = toParticularPoint X p := rfl
@[simp] lemma toParticularPoint_ofParticularPoint (a : WithParticularPoint X p) : toParticularPoint X p (ofParticularPoint X p a) = a := rfl
@[simp] lemma ofParticularPoint_toParticularPoint (a : X) : ofParticularPoint X p (toParticularPoint X p a) = a := rfl


/-- A recursor for `WithParticularPoint`. Use as `induction x using WithParticularPoint.rec`. -/
protected def rec {β : WithParticularPoint X p → Sort _}
    (h : ∀ a, β (toParticularPoint X p a)) : ∀ a, β a := fun a ↦ h (ofParticularPoint X p a)

instance : Nonempty (WithParticularPoint X p) := by exact Nonempty.intro p
instance : Inhabited (WithParticularPoint X p) := by exact { default := p }

instance : TopologicalSpace (WithParticularPoint X p) := ParticularPoint X p
instance : IsParticularPoint (WithParticularPoint X p) p := ⟨rfl⟩

end WithParticularPoint

open IsParticularPoint

instance : T0Space (WithParticularPoint X p) where
  t0 x y h:= by
    have : y ∈ {x, p} ∧ p ∈ {x, p} := by
      rw [← (@mem_nhds_iff (WithParticularPoint X p) _ _ _ {x, p}), ← h];
      simp [@nhds_eq (WithParticularPoint X p) p, subset_refl]
    have : x ∈ {y, p} ∧ p ∈ {y, p} := by
      rw [← (@mem_nhds_iff (WithParticularPoint X p) _ _ _ {y, p}), h];
      simp [@nhds_eq (WithParticularPoint X p) p, subset_refl]
    aesop

instance : SeparableSpace (WithParticularPoint X p) where
  exists_countable_dense := by
    refine ⟨{p}, countable_singleton p, dense_iff_inter_open.mpr ?_⟩
    refine fun U h₁ h₂ ↦ inter_singleton_nonempty.mpr <| (isOpen_iff (WithParticularPoint X p) p).mp h₁ h₂

instance : FirstCountableTopology (WithParticularPoint X p) where
  nhds_generated_countable := by
    refine fun a ↦ ⟨{{a, p}}, ?_⟩
    simp only [countable_singleton, nhds_eq (WithParticularPoint X p) p, generate_singleton, and_self]

end ParticularPoint
