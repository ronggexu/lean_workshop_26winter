import Mathlib
set_option linter.unnecessarySimpa false

/-!
# Several Properties in Localization of Rings and Modules

This file contains 4 important properties on localizations of rings and modules,
demonstrating that localization is an exact functor and behaves well
with respect to quotients and submodules.

## Main results

* `Prop 1.12` (**Exactness of Localization**): Shows that the localization functor `S⁻¹`
  is exact. That is, if `L ⟶ M ⟶ N` is an exact sequence of `R`-modules, then their
  localizations `S⁻¹L ⟶ S⁻¹M ⟶ S⁻¹N` form an exact sequence of `S⁻¹R`-modules.
* `Lemma 1.13` (**Localization respects quotients**): For a submodule `N` of `M`, there is
  a natural isomorphism between the localization of the quotient `S⁻¹(M/N)` and
  the quotient of the localizations `(S⁻¹M)/(S⁻¹N)`.
* `Prop 1.14` (**Iso of Localization of ideals**): For an ideal `I` of a ring `A`, the localization
  `S⁻¹I` is an ideal of the localized ring `S⁻¹A`. Furthermore, the localization of
  the quotient ring `A/I` at the image of `S` is isomorphic to `(S⁻¹A)/(S⁻¹I)`.
* `Lemma 1.15` (**Submodules of localized modules**): Characterizes submodules of a
  localized module `S⁻¹M`. Specifically, every submodule `N' \subseteq S⁻¹M` is of the form
  `S⁻¹N` for some submodule `N \subseteq M`, where `N` can be taken as the preimage of `N'`.

## Tags

localization, exactness, quotient modules, ideals, submodules
-/

open Function LocalizedModule Algebra

section LocalizationExact

variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {L M N : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
variable [Module R L] [Module R M] [Module R N]
variable (u : L →ₗ[R] M) (v : M →ₗ[R] N)

-- If u and v are exact, then their localizations are exact.
theorem localization_exact (h : Exact u v) : Exact (map S u) (map S v) :=
  LocalizedModule.map_exact S u v h

end LocalizationExact

section LocalizationQuotient

variable {R : Type u_5} {M : Type u_7}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable (S : Submonoid R) (M' : Submodule R M)

/-- The canonical isomorphism between localization of
 a quotient and quotient of the localization. -/
noncomputable def localized_QuotientEquiv :
(LocalizedModule S M ⧸ Submodule.localized S M') ≃ₗ[R] LocalizedModule S (M ⧸ M') :=
  (localizedQuotientEquiv S M').restrictScalars R

end LocalizationQuotient

/-variable {R : Type u_5} {M : Type u_7} [CommRing R] [AddCommGroup M] [Module R M]
variable (p : Submonoid R) (M' : Submodule R M)

-- The def of localizedQuotientEquiv in Mathlib
noncomputable def localizedQuotientEquiv' :
    (LocalizedModule p M ⧸ M'.localized p) ≃ₗ[Localization p] LocalizedModule p (M ⧸ M') :=
  have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalizedQuotient p) (LocalizedModule.mkLinearMap _ _)
    |>.restrictScalars _

-- The same theorem in R-module isomorphism version
noncomputable def localizedQuotientEquiv'' :
    (LocalizedModule p M ⧸ M'.localized p) ≃ₗ[R] LocalizedModule p (M ⧸ M') :=
  IsLocalizedModule.linearEquiv p (M'.toLocalizedQuotient p) (LocalizedModule.mkLinearMap _ _)

-- Comparison between IsLocalizedModule.linearEquiv and IsLocalization.algEquiv
/-noncomputable def IsLocalizedModule.linearEquiv
{R : Type u_1} [CommSemiring R] (S : Submonoid R) {M : Type u_2}
{M' : Type u_3} {M'' : Type u_4} [AddCommMonoid M] [AddCommMonoid M']
[AddCommMonoid M''] [Module R M] [Module R M'] [Module R M'']
(f : M →ₗ[R] M') (g : M →ₗ[R] M'') [IsLocalizedModule S f] [IsLocalizedModule S g] :
M' ≃ₗ[R] M''-/

/-noncomputable def IsLocalization.algEquiv
{R : Type u_1} [CommSemiring R] (M : Submonoid R) (S : Type u_2)
[CommSemiring S] [Algebra R S] [IsLocalization M S] (Q : Type u_4)
[CommSemiring Q] [Algebra R Q] [IsLocalization M Q] :
S ≃ₐ[R] Q-/ -/

section RingLocalizationQuotient

-- From R-algEquiv induce ringEquiv
noncomputable def IsLocalization_ringEquiv
{R : Type u_1} [CommSemiring R] (M : Submonoid R) (S : Type u_2)
[CommSemiring S] [Algebra R S] [IsLocalization M S] (Q : Type u_4)
[CommSemiring Q] [Algebra R Q] [IsLocalization M Q] : S ≃+* Q :=
(IsLocalization.algEquiv M S Q).toRingEquiv

-- A version which states the 'IsLocalization' explicitly
noncomputable def IsLocalization_ringEquiv_of_maps
  {R : Type u₁} [CommSemiring R] (M : Submonoid R)
  {S : Type u₂} [CommSemiring S] [Algebra R S]
  {Q : Type u₃} [CommSemiring Q] [Algebra R Q]
  (hf : IsLocalization M S) (hg : IsLocalization M Q)
  : S ≃+* Q :=
(IsLocalization.algEquiv M S Q).toRingEquiv

end RingLocalizationQuotient

section LocalizationOfIdeals

variable (A : Type*) [CommRing A]
variable (I : Ideal A)
variable (S : Submonoid A)

-- Part 1: S⁻¹I is an ideal of S⁻¹A
noncomputable def localization_of_ideal : Ideal (Localization S) :=
  I.map (algebraMap A (Localization S))

#check localization_of_ideal
-- (A : Type u_1) → [inst : CommRing A] → Ideal A → (S : Submonoid A)
-- → Ideal (Localization S)

-- Part 2: S̄⁻¹(A/I) is isomorphic to S⁻¹A/S⁻¹I as rings
-- where S̄ is the image of S by the natural map A → A/I
noncomputable def localization_quotient_iso :
let π := Ideal.Quotient.mk I
let S_bar := S.map π
Localization S_bar ≃+* Localization S ⧸ I.map (algebraMap A (Localization S)) := by
  intro π S_bar
  let J : Ideal (Localization S) := I.map (algebraMap A (Localization S))
  -- algebraMap : A →+* S⁻¹A
  -- to_quot : A →+* (S⁻¹A / S⁻¹I)
  let to_quot : A →+* (Localization S ⧸ J) :=
  (Ideal.Quotient.mk J).comp (algebraMap A (Localization S))
  -- to_quot 在 I 上为 0，从而诱导出商上的映射
  have to_quot_spec : ∀ i : A, i ∈ I → to_quot i = 0 := by
    intro i hi
    have : algebraMap A (Localization S) i ∈ J :=
    Ideal.mem_map_of_mem (algebraMap A (Localization S)) hi
    change (Ideal.Quotient.mk J) (algebraMap A (Localization S) i) = 0
    exact (Submodule.Quotient.mk_eq_zero J).mpr
     (Ideal.mem_map_of_mem (algebraMap A (Localization S)) hi)
  -- on_quot : (A ⧸ I) →+* (S⁻¹A / S⁻¹I)
  let on_quot : (A ⧸ I) →+* (Localization S ⧸ J) := Ideal.Quotient.lift I to_quot to_quot_spec
  -- S_bar 的元素在目标中为单位
  have map_s_units : ∀ s : A, s ∈ S → IsUnit (on_quot (π s)) := by
    intro s hs
    -- on_quot (π s) = (Ideal.Quotient.mk J) (algebraMap A (Localization M) s)
    have : on_quot (π s) = (Ideal.Quotient.mk J) (algebraMap A (Localization S) s) := by
      rw [Ideal.Quotient.lift_mk I to_quot to_quot_spec]
      rfl
    rw [this]
    have hu : IsUnit (algebraMap A (Localization S) s) :=
      IsLocalization.map_units (M := S) (Localization S) ⟨s, hs⟩
    exact IsUnit.map (Ideal.Quotient.mk J).toMonoidHom hu
  -- φ : S_bar⁻¹(A/I) →+* (S⁻¹A / S⁻¹I)
  let φ : Localization S_bar →+* (Localization S ⧸ J) :=
    IsLocalization.lift fun s_bar : S_bar => by
      obtain ⟨a, ⟨s, hs, rfl⟩⟩ := s_bar
      exact map_s_units s hs
  -- A → S_bar⁻¹(A/I)
  let a_to_Sbar : A →+* Localization S_bar := (algebraMap (A ⧸ I) (Localization S_bar)).comp π
  have a_to_Sbar_s_unit : ∀ s, s ∈ S → IsUnit (a_to_Sbar s) := by
    intro s hs
    simp only [a_to_Sbar, RingHom.comp_apply]
    have h : π s ∈ S_bar := Submonoid.mem_map_of_mem π hs
    exact IsLocalization.map_units (Localization S_bar) ⟨π s, h⟩
  -- Λ : S⁻¹A → S_bar⁻¹(A/I)
  let Λ : Localization S →+* Localization S_bar :=
    IsLocalization.lift fun s : S => a_to_Sbar_s_unit s.val s.prop
  -- Λ 在 J 上为 0，从而诱导出商上的映射
  have Λ_annihilates_J : ∀ x, x ∈ J → Λ x = 0 := by
    intro x hx
    -- `Ideal.map` 在当前 mathlib 中的定义是 `Ideal.span (f '' I)`，
    -- 所以证明 Λ 在 J 上为 0 等价于证明 `J ≤ ker Λ`。
    have hJ : J ≤ RingHom.ker Λ := by
      -- 展开 J = I.map (algebraMap ...)
      dsimp [J, Ideal.map]
      -- 用 `Ideal.span_le`：只需在生成元上落入 ker
      refine (Ideal.span_le).2 ?_
      intro z hz
      rcases hz with ⟨i, hi, rfl⟩
      -- 目标：Λ (algebraMap i) = 0
      have hcomp : (Λ.comp (algebraMap A (Localization S))) = a_to_Sbar :=
        IsLocalization.lift_comp (g := a_to_Sbar)
          (hg := fun y : S => a_to_Sbar_s_unit y.val y.prop)
      have hΛ : Λ (algebraMap A (Localization S) i) = a_to_Sbar i := by
        simpa [RingHom.comp_apply] using congrArg (fun f => f i) hcomp
      -- i ∈ I，因此 π i = 0，从而 a_to_Sbar i = 0
      have hpi : π i = 0 := by
        have : (Ideal.Quotient.mk I) i = 0 :=
          (Ideal.Quotient.eq_zero_iff_mem (I := I) (a := i)).2 hi
        simpa [π] using this
      have ha : a_to_Sbar i = 0 := by
        simp [a_to_Sbar, RingHom.comp_apply, hpi]
      simp [RingHom.mem_ker, hΛ, ha]
    -- 从 x ∈ J 得到 x ∈ ker Λ，也就是 Λ x = 0
    exact hJ hx
  -- ψ : (S⁻¹A / S⁻¹I) → S_bar⁻¹(A/I)
  let ψ : (Localization S ⧸ J) →+* Localization S_bar :=
    Ideal.Quotient.lift J Λ Λ_annihilates_J
  -- 验证互为逆
  have comp1 : (ψ.comp φ) = RingHom.id (Localization S_bar) := by
    -- 用局部化的 ext：只需在 `algebraMap` 的像上一致
    apply IsLocalization.ringHom_ext S_bar
    ext a
    -- 将“复合相等”的目标化成在生成元 `π a` 上的等式
    simp only [RingHom.comp_apply]
    -- 先把 φ ∘ algebraMap 化简成 on_quot
    have hgφ : ∀ y : S_bar, IsUnit (on_quot y) := by
      rintro ⟨_, ⟨s, hs, rfl⟩⟩
      exact map_s_units s hs
    have hφcomp : (φ.comp (algebraMap (A ⧸ I) (Localization S_bar))) = on_quot := by
      simpa [φ] using (IsLocalization.lift_comp (g := on_quot) (hg := hgφ))
    have hφeval : φ (algebraMap (A ⧸ I) (Localization S_bar) (π a)) = on_quot (π a) := by
      simpa [RingHom.comp_apply] using congrArg (fun f => f (π a)) hφcomp
    -- 再把 Λ ∘ algebraMap 化简成 a_to_Sbar
    have hΛcomp : (Λ.comp (algebraMap A (Localization S))) = a_to_Sbar :=
      IsLocalization.lift_comp (g := a_to_Sbar)
        (hg := fun y : S => a_to_Sbar_s_unit y.val y.prop)
    have hΛeval : Λ (algebraMap A (Localization S) a) = a_to_Sbar a := by
      simpa [RingHom.comp_apply] using congrArg (fun f => f a) hΛcomp
    -- 计算 (ψ ∘ φ) 在生成元上的值
    calc
      (ψ.comp φ) (algebraMap (A ⧸ I) (Localization S_bar) (π a))
          = ψ (on_quot (π a)) := by
            simp [RingHom.comp_apply, hφeval]
      _ = ψ ((Ideal.Quotient.mk J) (algebraMap A (Localization S) a)) := by
            -- on_quot (π a) = mkJ (algebraMap a)
        simpa [on_quot, to_quot, π] using
          (Ideal.Quotient.lift_mk I to_quot to_quot_spec a)
      _ = Λ (algebraMap A (Localization S) a) := by
            simpa using
              (Ideal.Quotient.lift_mk (I := J)
                (a := algebraMap A (Localization S) a)
                (f := Λ) (H := Λ_annihilates_J))
      _ = algebraMap (A ⧸ I) (Localization S_bar) ((Ideal.Quotient.mk I) a) := by
        simp [a_to_Sbar, RingHom.comp_apply, π, hΛeval]
  have comp2 : (φ.comp ψ) = RingHom.id (Localization S ⧸ J) := by
    -- 用 `Ideal.Quotient.ringHom_ext`（当前 mathlib 的唯一性引理）
    -- 把目标化为在 `Ideal.Quotient.mk J` 的像上相等。
    apply Ideal.Quotient.ringHom_ext (I := J)
    ext x
    -- 先证明 `(φ ∘ Λ) = mk J`，再配合 `ψ (mkJ x) = Λ x`。
    have hgφ : ∀ y : S_bar, IsUnit (on_quot y) := by
      rintro ⟨_, ⟨s, hs, rfl⟩⟩
      exact map_s_units s hs
    have hφcomp : (φ.comp (algebraMap (A ⧸ I) (Localization S_bar))) = on_quot := by
      simpa [φ] using (IsLocalization.lift_comp (g := on_quot) (hg := hgφ))
    have φΛ_eq_mk : (φ.comp Λ) = (Ideal.Quotient.mk J) := by
      -- 用局部化的 ext：只需在 `algebraMap A (Localization S)` 的像上一致
      apply IsLocalization.ringHom_ext S
      ext a
      have hΛcomp : (Λ.comp (algebraMap A (Localization S))) = a_to_Sbar :=
        IsLocalization.lift_comp (g := a_to_Sbar)
          (hg := fun y : S => a_to_Sbar_s_unit y.val y.prop)
      have hΛeval : Λ (algebraMap A (Localization S) a) = a_to_Sbar a := by
        simpa [RingHom.comp_apply] using congrArg (fun f => f a) hΛcomp
      have hφeval : φ (a_to_Sbar a) = on_quot (π a) := by
        -- 由 hφcomp 得到 φ(algebraMap (π a)) = on_quot (π a)
        have : φ (algebraMap (A ⧸ I) (Localization S_bar) (π a)) = on_quot (π a) := by
          simpa [RingHom.comp_apply] using congrArg (fun f => f (π a)) hφcomp
        simpa [a_to_Sbar, RingHom.comp_apply] using this
      -- 右边：on_quot (π a) = mkJ (algebraMap a)
      have hon : on_quot (π a) = (Ideal.Quotient.mk J) (algebraMap A (Localization S) a) := by
        -- on_quot 是对 I 的 lift
        simpa [on_quot, to_quot, π] using (Ideal.Quotient.lift_mk I to_quot to_quot_spec a)
      -- 收尾
      simpa [RingHom.comp_apply, hΛeval, hφeval, hon]
    -- 现在计算两边在生成元上的值
    simp only [RingHom.comp_apply]
    -- ψ (mkJ x) = Λ x
    have hψ : ψ ((Ideal.Quotient.mk J) x) = Λ x := by
      simpa [ψ] using (Ideal.Quotient.lift_mk (I := J) (a := x) (f := Λ) (H := Λ_annihilates_J))
    -- 代入并用 φΛ_eq_mk
    calc
      φ (ψ ((Ideal.Quotient.mk J) x)) = φ (Λ x) := by simpa [hψ]
      _ = (Ideal.Quotient.mk J) x := by
        simpa [RingHom.comp_apply] using congrArg (fun f => f x) φΛ_eq_mk
  -- bijectivity
  have bij : Function.Bijective (φ : Localization S_bar → Localization S ⧸ J) := by
    refine ⟨?_,?_⟩
    · intro a b h
      have ha : ψ (φ a) = a := by
        simpa [RingHom.comp_apply] using congrArg (fun f => f a) comp1
      have hb : ψ (φ b) = b := by
        simpa [RingHom.comp_apply] using congrArg (fun f => f b) comp1
      have hψ : ψ (φ a) = ψ (φ b) := by
        simpa using congrArg (fun t => ψ t) h
      calc
        a = ψ (φ a) := ha.symm
        _ = ψ (φ b) := hψ
        _ = b := hb
    · intro y
      refine ⟨ψ y, ?_⟩
      simpa [RingHom.comp_apply] using congrArg (fun f => f y) comp2
  exact RingEquiv.ofBijective φ bij

end LocalizationOfIdeals

section LocalizationSubmodule

open Function LocalizedModule

variable {R : Type*} [CommRing R]
variable (S : Submonoid R)
variable (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (N : Submodule R M)
variable (N' : Submodule (Localization S) (LocalizedModule S M))
variable (I' : Ideal (Localization S))

/-- Preimage of a submodule of S⁻¹M, as a submodule of M, under the map M → S⁻¹M.
Usage : comap_submodule S N', where N' is a submodule of S⁻¹M. -/
def comap_submodule : Submodule R M := {
      carrier := {m | mk m 1 ∈ N'}
      zero_mem' := N'.zero_mem
      add_mem' := fun hx hy => by
        rename_i a b
        simp only [Set.mem_setOf_eq] at hx hy; simp only [Set.mem_setOf_eq]
        have : mk (a + b) (1 : S) = mk a 1 + mk b 1 := by calc
          mk (a + b) 1 = LocalizedModule.mk ((1 : S) • a + (1 : S) • b) (1 * 1) := by
            simp only [one_smul, mul_one]
          _ = mk a 1 + mk b 1 := by rw[← mk_add_mk]
        rw[this]; exact add_mem hx hy
      smul_mem' := fun r m hm => by
        simp only [Set.mem_setOf_eq] at hm; simp only [Set.mem_setOf_eq]
        have : mk (r • m) (1 : S) = r • (mk m 1) := by calc
          mk (r • m) 1 = LocalizedModule.mk (r • m) (1 * 1) := by simp_all only [mul_one]
          _ = (Localization.mk r (1 : S)) • (mk m (1 : S)) := by rw[← mk_smul_mk]
        rw[this]; apply N'.smul_mem'
        simp_all only [Submodule.carrier_eq_coe, SetLike.mem_coe]
    }

/-- For the map M → S⁻¹M, if N equals to preimage of N' as set,
then N' = S⁻¹N as submodules of S⁻¹M. -/
lemma eq_localization_primage (h : (N : Set M) = {m | mk m 1 ∈ N'})
    : N' = Submodule.localized S N := by
  apply le_antisymm
  · intro x hx
    have : x ∈ Submodule.localized S ⊤ := by
      simp_all only [Submodule.localized'_top, Submodule.mem_top]
    rw[Submodule.mem_localized'] at this -- Use this to write x in the form of m/s.
    rcases this with ⟨m, hm, s, hs⟩
    refine (Submodule.mem_localized' (Localization S) S (mkLinearMap S M) N x).mpr ?_; use m
    constructor
    · let s' := Localization.mk (s : R) (1 : S)
      suffices : s' • x ∈ N' -- Module is closed under smul.
      · apply SetLike.mem_coe.mp; rw[h]; simp only [Set.mem_setOf_eq]
        have hs' : s' • x = mk m 1 := by calc
          s' • x = (Localization.mk (s : R) 1) • (mk m s) := by
            simp only [s']; rw[← hs]
            have hl : IsLocalizedModule.mk' (mkLinearMap S M) m s = mk m s := by
              rw[IsLocalizedModule.mk_eq_mk'] -- Transfer mk' into mk.
            rw[hl]
          _ = mk ((s : R) • m) (1 * s) := by rw[mk_smul_mk]
          _ = mk m 1 := by exact mk_cancel_common_right 1 s m
        rw[← hs']; exact this
      · exact Submodule.smul_mem N' s' hx
    · use s
  · intro x hx
    rw[Submodule.mem_localized'] at hx
    rcases hx with ⟨m, hm, s, hs⟩
    rw[← IsLocalizedModule.mk_eq_mk'] at hs -- Transfer mk' into mk.
    have : mk m s = (Localization.mk 1 s) • (mk m 1) := by calc
      mk m s = mk ((1 : R) • m) (s * 1) := by simp only [one_smul, mul_one]
      _ = (Localization.mk 1 s) • (mk m 1) := by rw[← mk_smul_mk]
    rw[← hs, this]
    apply Submodule.smul_mem N' (Localization.mk 1 s) -- Module is closed under smul.
    apply SetLike.mem_coe.mpr at hm -- m ∈ ↑N ↔ m ∈ N
    simp_all only [Set.mem_setOf_eq]

/-- Given an submodule of S⁻¹M, then it is a localization of a submodule of M. -/
theorem localization_of_submodule_localization : ∃ N, N' = Submodule.localized S N := by
  use comap_submodule S N'; apply eq_localization_primage; exact rfl

/-
theorem localization_of_submodule_localization₀ : ∃ N, N' = Submodule.localized S N := by
  let N : Submodule R M := {
      carrier := {m | mk m 1 ∈ N'}
      zero_mem' := N'.zero_mem
      add_mem' := fun hx hy => by
        rename_i a b
        simp only [Set.mem_setOf_eq] at hx hy; simp only [Set.mem_setOf_eq]
        have : mk (a + b) (1 : S) = mk a 1 + mk b 1 := by calc
          mk (a + b) 1 = mk ((1 : S) • a + (1 : S) • b) (1 * 1) := by simp only [one_smul, mul_one]
          _ = mk a 1 + mk b 1 := by rw[← mk_add_mk]
        rw[this]
        exact add_mem hx hy
      smul_mem' := fun r m hm => by
        simp only [Set.mem_setOf_eq] at hm; simp only [Set.mem_setOf_eq]
        have : mk (r • m) (1 : S) = r • (mk m 1) := by calc
          mk (r • m) 1 = mk (r • m) (1 * 1) := by simp_all only [mul_one]
          _ = (Localization.mk r (1 : S)) • (mk m (1 : S)) := by rw[← mk_smul_mk]
        rw[this]
        apply N'.smul_mem'
        simp_all only [Submodule.carrier_eq_coe, SetLike.mem_coe]
    }
  refine ⟨N, ?_⟩; apply le_antisymm
  · intro x hx
    have : x ∈ Submodule.localized S ⊤ := by
      simp_all only [Submodule.localized'_top, Submodule.mem_top]
    rw[Submodule.mem_localized'] at this
    rcases this with ⟨m, hm, s, hs⟩
    refine (Submodule.mem_localized' (Localization S) S (mkLinearMap S M) N x).mpr ?_; use m
    constructor
    · let s' := Localization.mk (s : R) (1 : S)
      suffices : s' • x ∈ N'
      · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_setOf_eq, N]
        have hs' : s' • x = mk m 1 := by calc
          s' • x = (Localization.mk (s : R) 1) • (mk m s) := by
            simp only [s']; rw[← hs]
            have hl : IsLocalizedModule.mk' (mkLinearMap S M) m s = mk m s := by
              rw[IsLocalizedModule.mk_eq_mk']
            rw[hl]
          _ = mk ((s : R) • m) (1 * s) := by rw[mk_smul_mk]
          _ = mk m 1 := by exact mk_cancel_common_right 1 s m
        rw[← hs']
        exact this
      · exact Submodule.smul_mem N' s' hx
    · use s
  · intro x hx
    rw[Submodule.mem_localized'] at hx
    rcases hx with ⟨m, hm, s, hs⟩
    rw[← IsLocalizedModule.mk_eq_mk'] at hs
    have : mk m s = (Localization.mk 1 s) • (mk m 1) := by calc
      mk m s = mk ((1 : R) • m) (s * 1) := by simp only [one_smul, mul_one]
      _ = (Localization.mk 1 s) • (mk m 1) := by rw[← mk_smul_mk]
    rw[← hs, this]
    apply Submodule.smul_mem N' (Localization.mk 1 s)
    exact hm

noncomputable def LocalizationIdeal : Ideal (Localization S) :=
  I.map (algebraMap R (Localization S))

theorem localization_of_ideal_localization : ∃ I, I' = LocalizationIdeal S I := by
  let I : Ideal R := {
      carrier := {r | algebraMap R (Localization S) r ∈ I'}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero]
        exact I'.zero_mem
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add]
        exact I'.add_mem ha hb
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [smul_eq_mul, map_mul]
        exact I'.mul_mem_left (algebraMap R (Localization S) c) ha
    }
  let N' := I' • (⊤ : Submodule (Localization S) ((LocalizedModule S R)))
  let N := I • (⊤ : Submodule R R);
  have ha (x : R) : (algebraMap R (Localization S)) x = Localization.mk x 1 := by rfl
  have : N' = Submodule.localized S N := by
    apply eq_localization_primage
    apply le_antisymm
    · intro x hx
      simp_all only [Set.mem_setOf_eq, SetLike.mem_coe]
      simp[N, I, ha] at hx; simp[N'];
      sorry
    · intro x hx
      simp_all only [Set.mem_setOf_eq, SetLike.mem_coe]
      simp[N'] at hx; simp[N, I, ha];
      sorry
  use I; suffices h :
    I' • (⊤ : Submodule (Localization S) ((LocalizedModule S R))) = (LocalizationIdeal S I) • ⊤
  · sorry
  · suffices : Submodule.localized S N = (LocalizationIdeal S I) • ⊤
    · simp_all only [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top, N', N, I]
    · dsimp[N]
      sorry
-/

end LocalizationSubmodule
