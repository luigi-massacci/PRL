import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.Topology.MetricSpace.CantorScheme
import Mathlib.Topology.Bases


variable {G : Type}  [Group G] [Fintype G]

def EqInv : Set G :=
  {x : G | x * x = 1}

def UnEqInv : Set G :=
  {x : G | x * x ≠ 1}

open Set

example
(h₀ : Even (ncard (univ : Set G))):
∃ a ≠ (1 : G), a * a = 1 := by
  by_contra h'; push_neg at h'
  have h₁ : EqInv ∪ UnEqInv = (univ : Set G) := by
    ext x
    simp [EqInv, UnEqInv]
    exact eq_or_ne (x * x) 1
  have card_eq : ncard (univ : Set G) = ncard EqInv + ncard UnEqInv := by
    rw [← h₁]
    apply ncard_union_eq -- found with obvious moogle query
    -- all three by exact?
    exact disjoint_left.mpr fun ⦃a⦄ a_1 a => a a_1
    exact toFinite EqInv
    exact toFinite UnEqInv
  have card_one : ncard EqInv = 1 := by
    apply ncard_eq_one.mpr -- by apply?
    use (1 : G)
    ext x
    constructor
    · intro h
      simp [EqInv] at h
      exact not_not_mem.mp fun a => h' x a h -- by exact?
    · intro h
      simp [*, EqInv] at * -- simp simp simp
      simp [h]
  have even_uneq : Even (ncard (UnEqInv : Set G)) := by sorry --this is the hard one
  have odd_card : Odd (ncard (univ : Set G)) := by
    simp [card_eq, card_one, even_uneq] -- simp simp simp
  exact Nat.odd_iff_not_even.mp odd_card h₀ -- found with obvious moogle query


open Filter

#check tendsto_nhdsWithin_mono_left
example :
  Tendsto (fun (x : ℝ) => 1/x) (nhdsWithin 0 (Set.Ioo 0 1)) atTop := by
  simp only [one_div]
  apply (tendsto_nhdsWithin_mono_left Set.Ioo_subset_Ioi_self tendsto_inv_zero_atTop)

example :
  Tendsto (fun (x : ℝ) => 1/x) (nhdsWithin 0 (Set.Ioo 0 1)) atTop := by
  simp only [one_div]
  show_term aesop
  exact tendsto_inv_zero_atTop

example :
  Tendsto (fun (x : ℝ) => 1/x) (nhdsWithin 0 (Set.Ioo 0 1)) atTop := by
  simp only [one_div]
  rw [nhdsWithin_Ioo_eq_nhdsWithin_Ioi zero_lt_one]
  exact tendsto_inv_zero_atTop

example {u : ℕ → ENNReal} (hu : Filter.Tendsto u Filter.atTop (nhds 0))
  {a : ENNReal} (ha : ∀ n : ℕ, a ≤ u n.succ) : a ≤ 0 := by
  apply ge_of_tendsto hu
  refine eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
  rw [← Nat.succ_pred_eq_of_pos hn]
  exact ha _

open Filter
open Set

variable (a b : ℝ)

example (ha : 0 < a) (hb : 0 < b) :
  Tendsto (fun (x:ℝ) => (1 - a * x)⁻¹)
         (nhdsWithin (a⁻¹) (Ioo 0 (a⁻¹))) atTop := by
  have : Tendsto (fun (x:ℝ) => a * x)
         (nhdsWithin (a⁻¹) (Ioo 0 (a⁻¹))) (nhds 1) := by
    apply @tendsto_mul _ this
