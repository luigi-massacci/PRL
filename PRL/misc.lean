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

-- example (ha : 0 < a) (hb : 0 < b) :
--   Tendsto (fun (x:ℝ) => (1 - a * x)⁻¹)
--          (nhdsWithin (a⁻¹) (Ioo 0 (a⁻¹))) atTop := by
--   have : Tendsto (fun (x:ℝ) => a * x)
--          (nhdsWithin (a⁻¹) (Ioo 0 (a⁻¹))) (nhds 1) := by
--     apply @tendsto_mul _ this


example {X Y : Type*} {U V : Set Y} (h : U ⊆ V) (f : X → Y) : f ⁻¹' U ⊆ f ⁻¹' V := by
  intro _; apply h


lemma helper₁ {α : Type*} {f g : α → ℝ} (hf : BddAbove (Set.range f))
  (hg : BddAbove (Set.range g)) (fpos : ∀ x, 0 ≤ f x) (gpos : ∀ x, 0 ≤ g x) :
    BddAbove {f x - g x | x} := by
  obtain ⟨Cf, hf⟩ := hf
  obtain ⟨Cg, hg⟩ := hg
  refine ⟨Cf+Cg, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc
  _ ≤ |f x - g x|   := by exact le_abs_self _
  _ ≤ |f x| + |g x| := by exact abs_sub _ _
  _ = f x + g x := by rw [abs_of_nonneg (fpos x), abs_of_nonneg (gpos x)]
  _ ≤ _  := by refine add_le_add (hf (by simp)) (hg (by simp))

lemma helper₁₁ {α : Type*} {f g : α → ℝ} (hf : BddAbove (Set.range f))
  (hg : BddAbove (Set.range g)) (fpos : ∀ x, 0 ≤ f x) (gpos : ∀ x, 0 ≤ g x) :
    BddAbove {|f x - g x| | x} := by
  obtain ⟨Cf, hf⟩ := hf
  obtain ⟨Cg, hg⟩ := hg
  refine ⟨Cf+Cg, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc
  _ ≤ |f x| + |g x| := by exact abs_sub _ _
  _ = f x + g x := by rw [abs_of_nonneg (fpos x), abs_of_nonneg (gpos x)]
  _ ≤ _  := by refine add_le_add (hf (by simp)) (hg (by simp))

lemma helper₂ {α : Type*} {f g : α → ℝ} (hα : Nonempty α) (hf : BddAbove (Set.range f))
  (hg : BddAbove (Set.range g)) (fpos : ∀ x, 0 ≤ f x) (gpos : ∀ x, 0 ≤ g x) :
    sSup {f x | x} ≤ sSup {f x - g x | x} + sSup {g x | x} := by
    rw [← csSup_add]
    · apply csSup_le
      · have z₀ := Classical.choice hα
        refine ⟨f z₀, by simp⟩
      · rintro _ ⟨x, rfl⟩
        apply le_csSup
        · apply BddAbove.add (helper₁ hf hg fpos gpos)  hg
        · apply Set.mem_add.mpr ⟨f x - g x, by simp, g x, by simp, by ring⟩
    · have z₀ := Classical.choice hα
      refine ⟨f z₀ - g z₀, by simp⟩
    · exact (helper₁ hf hg fpos gpos)
    · have z₀ := Classical.choice hα
      refine ⟨g z₀, by simp⟩
    · exact hg


lemma helper₃ {α : Type*}  {f g : α → ℝ} (hα : Nonempty α) (hb : BddAbove (Set.range |f - g|))
  (fpos : ∀ x, 0 ≤ f x) (gpos : ∀ x, 0 ≤ g x) :
    sSup {f x | x} ≤ sSup {|f x - g x| | x} + sSup {g x | x} := by
  by_cases hf : BddAbove (Set.range f)
  · by_cases hg : BddAbove (Set.range g)
    · apply le_trans (helper₂ hα hf hg fpos gpos)
      apply add_le_add_right
      apply csSup_le
      · have z₀ := Classical.choice hα
        refine ⟨f z₀ - g z₀, by simp⟩
      · rintro _ ⟨x, rfl⟩
        apply le_csSup_of_le (helper₁₁ hf hg fpos gpos) (by simp) (le_abs_self _)
    · have : ¬BddAbove (Set.range |f - g|) := by
        intro hc
        obtain ⟨C, hC⟩ := hc
        obtain ⟨Cf, hf⟩ := hf
        rw [mem_upperBounds] at hC
        rw [mem_upperBounds] at hf
        simp_rw [abs_sub_comm f g] at hC
        apply hg
        refine ⟨C + Cf, ?_⟩
        rintro y ⟨x, rfl⟩
        calc
          _ = |g x| := by rw [abs_of_nonneg (gpos x)]
          _ = |(g x - f x) + f x| := by ring_nf
          _ ≤ |g x - f x| + |f x| := by exact abs_add (g x - f x) _
        apply add_le_add
        · apply hC
          refine ⟨x, rfl⟩
        · apply hf
          refine ⟨x, Eq.symm <| abs_of_nonneg (fpos x)⟩
      contradiction
  · by_cases hg : BddAbove (Set.range g)
    · sorry
    · simp [Real.sSup_def]
      aesop <;> (try contradiction)
      sorry



lemma abs_sub_Ssup_le_sup {α : Type*}  (f g : α → ℝ) (hα : Nonempty α)
  (hb : BddAbove (Set.range |f - g|)) (fpos : ∀ x, 0 ≤ f x) (gpos : ∀ x, 0 ≤ g x) :
  |sSup {f x | x} - sSup {g x | x}| ≤ sSup {|f x - g x| | x} := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have : BddAbove (Set.range |g - f|) := by
        simp_rw [abs_sub_comm f g] at hb
        exact hb
      have := helper₃ hα this gpos fpos
      simp_rw [abs_sub_comm] at this
      linarith
    · linarith [helper₃ hα hb fpos gpos]
