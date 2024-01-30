import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Order

variable {α : Type*} [TopologicalSpace α]

instance : HeytingAlgebra (TopologicalSpace.Opens α) where
  himp s v := ⟨interior (sᶜ ∪ v), isOpen_interior⟩
  le_himp_iff s v u := by sorry
  compl s := ⟨interior (sᶜ ∪ ⊥), isOpen_interior⟩
  himp_bot s := rfl
