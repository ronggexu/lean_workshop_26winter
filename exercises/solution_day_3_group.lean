import Mathlib

section GroupTheory

open Subgroup

/-
  Let G be a group. Let H be a subgroup of G of index p, where p is a prime.
  Then H is a maximal subgroup of G.
-/
theorem covby_top_of_index_eq_prime {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (h_idx : H.index = p) : CovBy H ⊤ := by
  have hp : p.Prime := Fact.out
  refine ⟨Ne.lt_top (fun h => ?_), fun K h₁ h₂ => ?_⟩
  · simp [h] at h_idx
    simp [← h_idx, Nat.not_prime_one] at hp
  · have h₃ := Subgroup.relIndex_mul_index h₁.le
    have h₄ : (H.relIndex K * K.index).Prime := by rwa [h₃, h_idx]
    rcases Nat.prime_mul_iff.mp h₄ with (⟨-, h₅⟩ | ⟨-, h₅⟩)
    · rw [Subgroup.index_eq_one] at h₅
      simp [h₅] at h₂
    · rw [Subgroup.relIndex_eq_one] at h₅
      exact h₁.not_ge h₅

/-
  Let G be a p-group. Let H be a maximal subgroup of G.
  Prove that [G : H] = p.

  Hint: Show that H is normal in G.
-/
theorem index_eq_prime_of_covby_top (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] [Fact (IsPGroup p G)]
    {H : Subgroup G} (h_max : CovBy H ⊤) : H.index = p := by
  have hp : p.Prime := Fact.out
  simp only [covBy_top_iff] at h_max
  have G_nilpotent : Group.IsNilpotent G := IsPGroup.isNilpotent (p := p) Fact.out
  have H_normal : H.Normal := Subgroup.NormalizerCondition.normal_of_coatom H normalizerCondition_of_isNilpotent h_max
  have H_p_group : IsPGroup p H := IsPGroup.to_subgroup Fact.out H
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp H_p_group
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.index = p ^ k := IsPGroup.index Fact.out H
  have heq := Subgroup.card_mul_index H
  rw [hn, hk, ← pow_add] at heq
  have hk_ne_zero : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero, index_eq_one] at hk
    exact h_max.ne_top hk
  have hdiv_pow : p ^ (n + 1) ∣ Nat.card G := by
    rw [← heq]
    refine pow_dvd_pow _ ?_
    simp [Nat.one_le_iff_ne_zero.mpr hk_ne_zero]
  obtain ⟨K, hK₁, hK₂⟩ := Sylow.exists_subgroup_card_pow_succ hdiv_pow hn
  obtain rfl : K = ⊤ := by
    refine h_max.lt_iff.mp (lt_of_le_of_ne hK₂ ?_)
    rintro rfl
    rw [hn, pow_succ, left_eq_mul₀ (pow_ne_zero n (Nat.Prime.ne_zero hp))] at hK₁
    simp [hK₁, Nat.not_prime_one] at hp
  simp at hK₁
  simp [hK₁, Nat.pow_right_inj (Nat.Prime.one_lt hp)] at heq
  simpa [heq] using hk

end GroupTheory
