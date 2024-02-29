import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Algebra.Order.Field


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
