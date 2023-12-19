import Mathlib.Tactic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Bases
import Mathlib.Topology.Perfect
import Mathlib.Data.Set.Finite
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Urysohn

open Pointwise Int Topology

-- First Version
-- def ArithSequence (a b : ℤ) := {n | a ∣ n - b }

-- Nicer version with Thanks to Alex J. Best
def ArithSequence (m n : ℤ) := {m} * (⊤ : Set ℤ) + {n}

example (n : ℤ) : Even n ↔  n ∈ ArithSequence 2 0 := by
  constructor <;> simp [ArithSequence]

def Opens : Set (Set ℤ) := {∅} ∪ { U | ∀n ∈ U, ∃ m : ℤ, 1 ≤ m ∧ ArithSequence m n ⊆ U}

lemma Opens_isOpenEmpty : ∅ ∈ Opens := by
  simp [Opens]

lemma Opens_isOpenZ : Set.univ ∈ Opens := by
  simp [Opens]
  use 1

lemma Opens_isOpen_sUnion : ∀ C : Set (Set ℤ), (∀ (U : Set ℤ), U ∈ C → U ∈ Opens) → (⋃₀ C) ∈ Opens := by
  simp [Opens]
  intro C hC n S S_in_C n_in_S
  rcases hC S S_in_C n n_in_S with ⟨m, one_le_m, Smn_in_S⟩
  refine ⟨m, one_le_m, ?_⟩
  intro k k_in_Smn
  refine ⟨S, S_in_C, ?_⟩
  apply subset_trans Smn_in_S <;> tauto

lemma Opens_isOpenInter : ∀ U V : Set ℤ , U ∈ Opens → V ∈ Opens → U ∩ V ∈ Opens:= by
  simp [Opens]
  intro U V hU hV n n_in_U n_in_V
  rcases hU _ n_in_U with ⟨u, one_le_u, S_in_u⟩
  rcases hV _ n_in_V with ⟨v, one_le_v, S_in_v⟩
  use u*v
  constructor
  · exact one_le_mul_of_one_le_of_one_le one_le_u one_le_v
  refine ⟨subset_trans ?_ S_in_u, subset_trans ?_ S_in_v⟩ <;> (simp [ArithSequence]; intro a ⟨k, hk⟩)
  · use v*k; ring_nf; assumption
  · use u*k; ring_nf; rw [mul_comm v u]; assumption

instance SequenceTopology : TopologicalSpace ℤ
  where
    IsOpen := Opens
    isOpen_inter := Opens_isOpenInter
    isOpen_sUnion := Opens_isOpen_sUnion
    isOpen_univ := Opens_isOpenZ

lemma IsOpen_of_ArithSequence (a b : ℤ) (one_le_a : 1 ≤ a) : IsOpen (ArithSequence a b) := by
  right
  simp
  intro n n_in_seq
  refine ⟨a, one_le_a, ?_⟩
  intro k k_in_seq_ab
  simp [ArithSequence] at *
  rcases k_in_seq_ab with ⟨u, hu⟩
  rcases n_in_seq with ⟨v, hv⟩
  use (u+v)
  ring_nf
  rw [hu, hv]
  ring

lemma Infinite_of_ArithSequence {a b : ℤ} (ha : 1 ≤ a ) : Set.Infinite (ArithSequence a b) := by
  refine Set.infinite_of_not_bddAbove ?_
  intro h
  cases' h with w hw
  by_cases wpos : 0 < w
  · by_cases bpos : 0 < b
    · specialize hw (show a*w + b ∈ ArithSequence a b by simp [ArithSequence])
      nlinarith
    · specialize hw (show a*(w - b + 1) + b ∈ ArithSequence a b by simp [ArithSequence])
      nlinarith
  by_cases bpos : 0 < b
  · specialize hw (show b ∈ ArithSequence a b by simp [ArithSequence])
    nlinarith
  · specialize hw (show a*(-w - b + 1) + b ∈ ArithSequence a b by simp [ArithSequence])
    nlinarith

lemma IsClosed_of_ArithSequence (a b : ℤ) (one_le_a : 1 ≤ a) : IsClosed (ArithSequence a b) := by
  constructor
  right
  intro n n_in_seq_ab
  refine ⟨a, one_le_a, ?_⟩
  intro k k_in_seq_an
  simp [ArithSequence] at *
  intro m hm
  rcases k_in_seq_an with ⟨u, hu⟩
  specialize n_in_seq_ab (m - u)
  ring_nf at n_in_seq_ab
  rw [hm, hu] at n_in_seq_ab
  ring_nf at n_in_seq_ab
  exact n_in_seq_ab trivial

lemma IsClopen_of_ArithSequence (a b : ℤ) (one_le_a : 1 ≤ a) : IsClopen (ArithSequence a b) :=
  ⟨IsOpen_of_ArithSequence a b one_le_a,  IsClosed_of_ArithSequence a b one_le_a⟩

lemma Infinite_of_IsOpen {U : Set ℤ}: Set.Nonempty U →  IsOpen U  → Set.Infinite U := by
  intro nonempty_U open_U
  cases' open_U with emptyU seq_in_U
  · aesop
  · rcases nonempty_U with ⟨n, n_in_U⟩
    rcases seq_in_U n n_in_U with ⟨m, one_le_m, seq_m_in_U⟩
    apply Set.Infinite.mono seq_m_in_U
    apply Infinite_of_ArithSequence one_le_m

lemma not_closed_of_complement_of_finite {U : Set ℤ} (nonempty_U : Set.Nonempty U)
    (finite_U : Set.Finite U) : ¬(IsClosed Uᶜ) := by
  intro closed_U
  have : IsOpen U := by rw [← compl_compl U]; exact isOpen_compl_iff.mpr closed_U
  have := Infinite_of_IsOpen nonempty_U this
  contradiction

-- With Thanks to Ruben Wan de Welde
lemma exists_prime_factor (n : ℤ) (n_ne_one : n ≠ 1) (n_ne_negone : n ≠ -1):
    ∃ p, Nat.Prime p ∧ ∃m, (↑p) * m = n:= by
  use n.natAbs.minFac
  constructor
  · refine Nat.minFac_prime ?_
    have := @Int.natAbs_eq_iff_sq_eq n 1
    aesop
  use n / n.natAbs.minFac
  rw [mul_comm, Int.ediv_mul_cancel]
  rw [Int.ofNat_dvd_left]
  exact Nat.minFac_dvd (Int.natAbs n)

-- Old version kept for comparison
-- lemma exists_prime_factor (n : ℤ) (hn : n ≠ -1 ∧ n ≠ 1) : ∃ p k, Nat.Prime p ∧ p*k = n := by
--   by_cases n_pos : 0 < n
--   · have nonempty_factors : (toNat n).factors ≠ [] := by
--       simp
--       intro h
--       cases' h with n_le_zero n_eq_one
--       · linarith
--       · have : 1 < n := lt_of_le_of_ne (by linarith) (Ne.symm hn.2)
--         have : 1 < toNat n := by exact lt_toNat.mpr (this)
--         linarith
--     have : ∃ p, p ∈ (Int.toNat n).factors := by
--       exact List.exists_mem_of_ne_nil ((toNat n).factors) nonempty_factors
--     rcases this with ⟨p, hp⟩
--     rcases Nat.dvd_of_mem_factors hp with ⟨k, hk⟩
--     refine ⟨p, k, Nat.prime_of_mem_factors hp, ?_⟩
--     rw_mod_cast [← hk]
--     exact toNat_of_nonneg (show 0 ≤ n by linarith)
--   · by_cases nzero : n = 0
--     · refine ⟨2, 0, ?_⟩
--       simp [nzero, Nat.prime_two]
--     · have n_lt_zero : n < 0 := by
--         push_neg at n_pos
--         apply lt_of_le_of_ne n_pos nzero
--       have neg_n_ne_one : -n ≠ 1 := by intro h; simp [← h] at hn
--       have : (toNat (-n)).factors ≠ [] := by
--         simp
--         intro h
--         cases' h with zero_le_n n_eq_one
--         · linarith
--         · have : 1 < -n := lt_of_le_of_ne (by linarith) (Ne.symm neg_n_ne_one)
--           have : 1 < toNat (-n) := by exact lt_toNat.mpr (this)
--           linarith
--       have : ∃ p, p ∈ (toNat (-n)).factors := by
--         exact List.exists_mem_of_ne_nil ((toNat (-n)).factors) this
--       rcases this with ⟨p, hp⟩
--       rcases Nat.dvd_of_mem_factors hp with ⟨k, hk⟩
--       refine ⟨p, -k, Nat.prime_of_mem_factors hp, ?_⟩
--       rw_mod_cast [(show (p : ℤ) * (-k : ℤ) = -(p*k : ℤ) by ring), ← hk]
--       rw [toNat_of_nonneg (show 0 ≤ -n by linarith)]
--       ring

lemma ne_eq_mul_even_self {x y : ℤ} (hx : x ≠ 0)(heq : x * (2 * y) = x) : False := by
  have : 2 * y = 1 := by
    nth_rewrite 2 [← mul_one x] at heq
    rw [Int.eq_of_mul_eq_mul_left hx heq]
  have : (2 * y) % 2 = 1 % 2 := by rw [this]
  norm_num at this

lemma primes_cover : ⋃ p ∈ { p : ℕ | Nat.Prime p }, ArithSequence p 0 = {-1, 1}ᶜ := by
  ext n
  simp [ArithSequence]
  constructor
  · intro h
    rcases h with ⟨p, prime_p, k, hpk⟩
    intro hn
    have not_unit_p := by exact Prime.not_unit (Nat.prime_iff_prime_int.mp prime_p)
    cases' hn with hn hn
    · rw [hn] at hpk
      have p_unit : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := by exact eq_one_or_neg_one_of_mul_eq_neg_one hpk
      cases' p_unit <;> aesop
    · rw [hn] at hpk
      have p_unit : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := by exact eq_one_or_neg_one_of_mul_eq_one hpk
      cases' p_unit <;> aesop
  · intro hn
    push_neg at hn
    exact exists_prime_factor n hn.2 hn.1

lemma Infinite_Primes : Set.Infinite { p : ℕ  | Nat.Prime p } := by
  by_contra h
  have finite_primes : Set.Finite { p : ℕ | Nat.Prime p } := by exact Set.not_infinite.mp h
  have isClosed_primes_union : IsClosed (⋃ p ∈ { p : ℕ | Nat.Prime p }, ArithSequence p 0) := by
    refine Set.Finite.isClosed_biUnion finite_primes ?_
    intro p prime_p
    have one_le_p : (1 : ℤ) ≤ (p : ℤ) := by exact toNat_le.mp (le_of_lt (Nat.Prime.one_lt prime_p))
    exact IsClosed_of_ArithSequence p 0 one_le_p
  rw [primes_cover] at isClosed_primes_union
  have nonempty_units : Set.Nonempty {-1, 1} := by exact (Set.insert_nonempty (-1) {1})
  have finite_units : Set.Finite {-1, 1} := by exact (Set.toFinite {-1, 1})
  exact not_closed_of_complement_of_finite nonempty_units finite_units isClosed_primes_union


--------------------------------------------------------------------------------
-- MORE TOPOLOGICAL PROPERTIES OF THE PROFINITE TOPOLOGY ON Z
--------------------------------------------------------------------------------

-- Maybe a little bit more cleanup tbd here
lemma singleton_eq_intersection (n : ℤ): {n} = ⋂ k ≥ 1, ArithSequence k n := by
  ext m
  constructor
  · intro m_eq_n
    simp [ArithSequence]
    refine fun i _ ↦ ⟨0, ?_⟩
    rw [m_eq_n]
    ring
  · intro m_in_inter
    simp [ArithSequence] at m_in_inter
    have : ∃x, m = x + n := by
      rcases m_in_inter 1 (by norm_num) with ⟨x, m_eq_xn⟩
      ring_nf at m_eq_xn
      use x
      rw [m_eq_xn]
      ring
    rcases this with ⟨x, hx⟩
    rw [hx]at m_in_inter
    ring_nf at m_in_inter
    by_cases x_pos : 0 < x
    · rcases m_in_inter (2*x) (by linarith) with ⟨y, two_xy_eq_x⟩
      have x_eq_zero : x = 0 := by
          have : x * (2*y) = x := by nth_rewrite 2 [← two_xy_eq_x]; ring
          exact False.elim (ne_eq_mul_even_self (ne_of_gt x_pos) this)
      rw [x_eq_zero] at hx
      simp [hx]
    · by_cases x_eq_zero : x = 0
      · rw [x_eq_zero] at hx
        simp [hx]
      · push_neg at x_pos
        push_neg at x_eq_zero
        have : 1 ≤ 2*(-x) := by
          have : 0 ≤ -x := by linarith
          have h₁ : 0 ≠ -x := by exact Ne.symm ( Int.neg_ne_zero.mpr x_eq_zero)
          have : 0 < -x := by exact lt_of_le_of_ne this h₁
          linarith
        rcases m_in_inter (2*(-x)) this with ⟨y, two_xy_eq_x⟩
        have : x * (2 * (-y)) = x := by nth_rewrite 2 [← two_xy_eq_x]; ring
        exact False.elim (ne_eq_mul_even_self (by exact x_eq_zero) this)

lemma singletons_closed (n : ℤ): IsClosed {n} := by
  rw [singleton_eq_intersection]
  refine isClosed_biInter ?_
  intro i one_le_i
  apply IsClosed_of_ArithSequence i n one_le_i


lemma cancel_abs (a b : ℤ) (ha : 0 < a) (hb : 0 ≤ b) (hab : a*b + b = a) : False := by
  by_cases hb2 : b = 0
  rw [hb2] at hab
  linarith
  push_neg at hb2
  have : 0 < b := by nlinarith
  nlinarith


instance Haussdorf_of_ArithSequenceTopology : T2Space ℤ := by
  constructor
  intro p q p_ne_q
  use ArithSequence (|p - q| + 1) p
  use ArithSequence (|p - q| + 1) q
  constructor
  apply IsOpen_of_ArithSequence
  have : 0 ≤ |p - q| := by exact abs_nonneg (p - q)
  linarith
  constructor
  apply IsOpen_of_ArithSequence
  have : 0 ≤ |p - q| := by exact abs_nonneg (p - q)
  linarith
  constructor
  simp [ArithSequence]
  constructor
  simp [ArithSequence]
  intro S S_sub_p S_sub_q
  simp at *
  by_contra h
  rcases Set.not_subset_iff_exists_mem_not_mem.mp h with ⟨m, m_in_s, hm⟩
  have hmp : m ∈ ArithSequence (|p - q| + 1) p := by aesop
  have hmq : m ∈ ArithSequence (|p - q| + 1) q := by aesop
  simp [ArithSequence] at hmp
  simp [ArithSequence] at hmq
  rcases hmp with ⟨y, hy⟩
  rcases hmq with ⟨x, hx⟩
  have : (|p - q| + 1) * |x - y| = |p - q| := by
    have : (|p - q| + 1) * (x - y) = p - q := by
      rw [mul_sub]
      rw [hy, hx]
      ring_nf
    nth_rewrite 2 [←this]
    rw [abs_mul]
    have : abs (|p - q| + 1) = |p - q| + 1 := by
      apply abs_of_pos
      have : 0 ≤ |p - q| := by exact abs_nonneg (p - q)
      linarith
    rw [this]
  ring_nf at this
  apply cancel_abs |p - q| |x - y|
  apply lt_of_le_of_ne
  exact abs_nonneg (p - q)
  intro h
  symm at h
  have := abs_eq_zero.mp h
  apply p_ne_q
  rw [← zero_add q]
  rw [← this]
  ring_nf
  exact abs_nonneg (x - y)
  assumption


lemma IsTotallyDisconnected_of_ArithSequence : IsTotallyDisconnected (⊤ : Set ℤ) := by
  apply isTotallyDisconnected_of_isClopen_set
  intro p q pneq
  use ArithSequence (|p - q| + 1) p
  constructor
  apply IsClopen_of_ArithSequence
  have : 0 ≤ |p - q| := by exact abs_nonneg (p - q)
  linarith
  constructor
  simp [ArithSequence]
  simp [ArithSequence]
  intro x
  intro hp
  have : (|p - q| + 1) * |x| = |p - q| := by
    have h : |p - q| = |q - p| := by exact abs_sub_comm p q
    have : q + -p = q - p := by ring
    rw [this] at hp
    nth_rewrite 2 [h]
    rw [←hp]
    rw [abs_mul]
    have : abs (|p - q| + 1) = |p - q| + 1 := by
      apply abs_of_pos
      have : 0 ≤ |p - q| := by exact abs_nonneg (p - q)
      linarith
    rw [this]
  apply cancel_abs |p - q| |x|
  apply lt_of_le_of_ne
  exact abs_nonneg (p - q)
  intro h
  symm at h
  have := abs_eq_zero.mp h
  apply pneq
  rw [← zero_add q]
  rw [← this]
  ring_nf
  exact abs_nonneg x
  ring_nf at this
  assumption


def basis := { U | ∃ m n : ℤ, 1 ≤ m ∧ U = ArithSequence m n}

instance IsSecondCountable : SecondCountableTopology ℤ := by sorry


instance Regular_of_ArithSequenceTopology : RegularSpace ℤ := by
  apply RegularSpace.ofExistsMemNhdsIsClosedSubset
  intro n S hS
  rcases mem_nhds_iff.mp hS with ⟨U, subsetU, openU, nU⟩
  cases' openU with emptyU arithU
  aesop
  simp at arithU
  specialize arithU n nU
  rcases arithU with ⟨m, hm, seq⟩
  use ArithSequence m n
  constructor
  refine mem_nhds_iff.mpr ?h.left.a
  use ArithSequence m n
  constructor
  rfl
  constructor
  exact IsOpen_of_ArithSequence _ _ hm
  simp [ArithSequence]
  constructor
  exact IsClosed_of_ArithSequence _ _ hm
  apply subset_trans seq subsetU

instance T3SpaceZ : T3Space ℤ := by infer_instance


instance : TopologicalSpace.MetrizableSpace ℤ := by infer_instance

lemma Perfect_Z : Perfect (⊤ : Set ℤ) := by
  constructor
  · simp
  · apply preperfect_iff_nhds.mpr
    intro n _ U ngh_U_n
    have : Set.Infinite U := by
      rcases mem_nhds_iff.mp ngh_U_n with ⟨V, V_sub_U, openV, n_in_V⟩
      apply Set.Infinite.mono V_sub_U
      apply Infinite_of_IsOpen (Set.nonempty_of_mem n_in_V) openV
    have := Set.Infinite.exists_not_mem_finite this (Set.finite_singleton n)
    aesop
