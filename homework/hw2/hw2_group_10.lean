import Mathlib
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
open PrimeSpectrum Topology

/-!
# Prime Spectrum 素谱

本文件主要内容为交换环上的谱理论基础，包含素谱的基本性质、Zariski 拓扑、同胚以及其他拓扑性质。

## 重要定义

* `V T`: zeroLocus，也即包含集合 T 的所有素理想组成的集合
* `D f`: baiscOpen f 作为集合
* `localization_spec_homeomorph`: 对乘闭子集局部化后的素谱与原环的和该子集不交的所有素理想的同胚
* `localization_spec_homeomorph'`: 上述定义的特例，乘闭子集由 f 生成
* `spec_quotient_homeomorph`: 商环的素谱与原环的包含该理想的所有素理想的同胚

## 主要定理

* `comap_continuous_and_preimage_basicOpen`: 环同态 `φ` 诱导一个 Zariski 连续映射，且该映射下 `D f` 的原像是 `D (φ f)`
* `spec_is_quasi_compact`: 素谱是拟紧的
* `primeSpectrum_topology_properties`: 关于素谱的三个拓扑性质，详见定理处注释

-/

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Spec R: 也即 PrimeSpectrum R，为 R 的所有素理想组成的类型 -/
abbrev Spec (R : Type*) [CommRing R] := PrimeSpectrum R
/-- V T: 也即 zeroLucus T，为包含 T 的所有素理想组成的集合 -/
def V (T : Set R) : Set (Spec R) := zeroLocus T
/-- D(f): basicOpen f 作为集合，也即不包含 f 的所有素理想组成的集合 -/
def D (f : R) : Set (Spec R) := (basicOpen f).carrier

example (f : R) (p : Spec R) : p ∈ D f → f ∉ p.asIdeal := by
  simp [D]

-- Lemma 3.2 中的大部分引理在 Mathlib 中有几乎 exact 的引理

#check PrimeSpectrum.isEmpty_iff_subsingleton -- 3.2.1
#check Ideal.exists_maximal
#check Ideal.nonempty_minimalPrimes
#check Ideal.exists_minimalPrimes_le
#check PrimeSpectrum.zeroLocus_span
#check PrimeSpectrum.zeroLocus_radical
#check Ideal.radical_eq_sInf
#check PrimeSpectrum.zeroLocus_empty_iff_eq_top
#check PrimeSpectrum.zeroLocus_inf
#check PrimeSpectrum.zeroLocus_iUnion
#check PrimeSpectrum.basicOpen_eq_zeroLocus_compl
#check PrimeSpectrum.basicOpen_eq_bot_iff -- 3.2.12
#check PrimeSpectrum.basicOpen_mul -- 3.2.15

-- 除了以下四个：

/-- Lemma 3.2.13: 乘以单位保 `basicOpen` -/
lemma lem_3_2_13 {f : R} {u : R} {f' : R} (hu : IsUnit u) (h : f' = u * f) : D f = D f' := by
  ext p
  repeat rw [D]
  -- 现在目标化为 p ∈ (basicOpen f).carrier ↔ p ∈ (basicOpen f').carrier
  aesop /- simp_all only [TopologicalSpace.Opens.carrier_eq_coe, basicOpen_eq_zeroLocus_compl,
  Set.mem_compl_iff, mem_zeroLocus,
  Set.singleton_subset_iff, SetLike.mem_coe, Ideal.unit_mul_mem_iff_mem] -/

/-- Lemma 3.2.14: 一点外的闭集可以与一个包含该点的基本开集不交（或者等价的也可以说，对开集中的每一个点，该点有一个基本开集“邻域”包含在原集合里面） -/
lemma lem_3_2_14 {I : Ideal R} {p : Spec R} (hnin : p ∉ V I) :
  ∃ f : R, p ∈ D f ∧ ((D f) ∩ (V I)) = ∅ := by
  /-
  因为 hnin，所以 I 不完全在 p 里面。我们要找到一个在 I 不在 p 里的元素
  -/
  have hdiff : ∃ f : R, f ∈ I ∧ f ∉ p.asIdeal := by
    rw [V] at hnin
    simp_all only [mem_zeroLocus, SetLike.coe_subset_coe]
    by_contra h -- 反证法
    push_neg at h -- 变成 ∀ f ∈ I, f ∈ p.asIdeal
    have hin : I ≤ p.asIdeal := fun x => h x
    exact hnin hin
  rcases hdiff with ⟨f, hf⟩
  use f
  aesop

/-- Lemma 3.2.16: `f_i` 是一些 R 中的元素，则 `D f_i` 的并就是 `V {f_i}` 的补集 -/
lemma lem_3_2_16 (I : Type*) (f : I → R) :
  Set.iUnion (D.comp f) = (V (Set.range f))ᶜ := by
  symm
  rw [compl_eq_comm]
  simp_all only [Set.compl_iUnion, Function.comp_apply, D, TopologicalSpace.Opens.carrier_eq_coe,
  basicOpen_eq_zeroLocus_compl, compl_compl, ←PrimeSpectrum.zeroLocus_iUnion,
  V, Set.iUnion_singleton_eq_range]

/-- Lemma 3.2.17: `D f = Spec R`，则 `f` 是单位 -/
lemma lem_3_2_17 (f : R) : (D f = (Set.univ : Set (Spec R))) → IsUnit f := by
  intro h
  have h1 : V {f} = ∅ := by
    have := lem_3_2_16 ({0} : Set ℕ) (fun (x : ({0} : Set ℕ)) ↦ (f : R))
    simp only [Set.iUnion_coe_set, Set.mem_singleton_iff, Function.comp_apply,
      Set.iUnion_iUnion_eq_left, Set.range_const] at this
    simp_all only [Set.compl_univ_iff, Set.compl_empty]
  have h2 : Ideal.span {f} = ⊤ := by
    have := @PrimeSpectrum.zeroLocus_empty_iff_eq_top (I := Ideal.span {f})
    rw [PrimeSpectrum.zeroLocus_span {f}] at this
    have := this.mp
    exact this h1
  simp_all only [Ideal.span_singleton_eq_top]

example (T : Set R) : IsClosed (zeroLocus T) :=
isClosed_zeroLocus T
example (s : Set (PrimeSpectrum R)) (h : IsClosed s) :
s = zeroLocus (vanishingIdeal s) := by
rw [zeroLocus_vanishingIdeal_eq_closure, h.closure_eq]
example (f : R) : IsOpen (basicOpen f).carrier :=
(basicOpen f).isOpen
#check isBasis_basic_opens

/-- 素谱的函子性。
对于一个环同态 `φ : R →+* S`，诱导在谱上的映射是连续的，而且对任意元素 `r : R`，有开集 `D(r)` 的原像就是 `D(φ r)`. -/
theorem comap_continuous_and_preimage_basicOpen (φ : R →+* S) (r : R) :
Continuous (comap φ) ∧ (comap φ)⁻¹' PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen (φ r):= by
  constructor
  · -- 连续性内涵在 `comap` 的定义中（作为一个 `ContinuousMap`）
    exact (comap φ).continuous
  · -- 基本开集的原像性质由 `comap_basicOpen` 提供
  -- 我们用这个引理 rewrite
  -- `Opens` 对象相等蕴含着其隐含的集合是相等的。
    rw [← comap_basicOpen φ r]
    rfl

/--
For a commutative ring `R` and a multiplicative subset `M  R` (given as a `Submonoid`),
the canonical map `R → Localization M` induces a homeomorphism between the prime spectrum
of the localization and the set of primes of `R` which do not meet `M`.
对交换环 `R` 和乘闭子集 `M ⊆ R` (由 `Submonoid` 给出)，
自然映射 `R → Localization M` 诱导出局部化后的素谱与所有 `R` 中与 `M` 无交的素理想之间的同胚.
-/
noncomputable def localization_spec_homeomorph (R : Type*) [CommRing R] (M : Submonoid R) :
PrimeSpectrum (Localization M)
≃ₜ { p : PrimeSpectrum R // Disjoint (M : Set R) (p.asIdeal : Set R) }
:=
  let S := Localization M
  let h_emb := localization_comap_isEmbedding S M
  let h_range := localization_comap_range S M
  h_emb.toHomeomorph.trans (Homeomorph.setCongr h_range)

/--
The canonical map `R →+* Localization.Away f` induces a homeomorphism
`Spec (Localization.Away f) ≃ₜ D(f)` where `D(f)` is the standard open
(`basicOpen f`) in `Spec R`.
自然映射 `R →+* Localization.Away f` 诱导出同胚 `Spec (Localization.Away f) ≃ₜ D(f)`
其中 `D(f)` 是 `Spec R` 中的基本开集 (`basicOpen f`)
-/
noncomputable def localization_spec_homeomorph' (f : R) :
PrimeSpectrum (Localization.Away f) ≃ₜ
{ p : PrimeSpectrum R // p ∈ (PrimeSpectrum.basicOpen f).1 } :=
let S := Localization.Away f
-- The map Spec(R_f) -> Spec(R) is an open embedding
let h_emb := PrimeSpectrum.localization_away_isOpenEmbedding S f
-- The range of this map is exactly D(f)
let h_range := PrimeSpectrum.localization_away_comap_range S f
-- Construct the homeomorphism from the embedding and the range equality
h_emb.toIsEmbedding.toHomeomorph.trans (Homeomorph.setCongr h_range)

/-- The canonical surjection `R →+* R ⧸ I` induces, via the functoriality of `Spec`,
a homeomorphism between
* the prime spectrum of the quotient ring `R ⧸ I`, and
* the closed subset `V(I) = { p ∈ Spec R | I ⊆ p }` of `Spec R`. -/
noncomputable def spec_quotient_homeomorph (I : Ideal R) :
(PrimeSpectrum (R ⧸ I)) ≃ₜ {p : PrimeSpectrum R // I ≤ p.asIdeal} := by
-- Define the map f as the comap of the quotient homomorphism
  let f := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  -- f is a closed embedding because the quotient map is surjective
  have h_emb : IsClosedEmbedding f :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk
    I) Ideal.Quotient.mk_surjective
  -- The range of f is exactly V(I) = {p | I  p}
  have h_range : Set.range f = {p | I ≤ p.asIdeal} := by
    rw [PrimeSpectrum.range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk
    I) Ideal.Quotient.mk_surjective]
    -- Ideal.mk_ker is the lemma stating ker (mk I) = I
    rw [Ideal.mk_ker]
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus]
    rfl
    -- Construct the homeomorphism from the embedding and the range equality
    -- Use IsEmbedding.toHomeomorph which creates a homeomorphism onto the range
  exact h_emb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr h_range)

/-- Prime Spectrum is quasi compact -/
theorem spec_is_quasi_compact : CompactSpace (Spec R) :=
  inferInstance


/--
The Zariski topology on `Spec(R)` satisfies the usual compactness properties:
1  `Spec(R)` is quasi‑compact.
2  It has a basis consisting of quasi‑compact standard opens (`basicOpen f`).
3  The intersection of any two quasi‑compact opens is again quasi‑compact.
  原 pdf 的 lean 代码中定理陈述有误, 缺少 IsOpen 条件.
-/
theorem primeSpectrum_topology_properties : IsCompact (Set.univ : Set (PrimeSpectrum R))
∧ (∃ B : Set (Set (PrimeSpectrum R)),
  (∀ U ∈ B, IsCompact U) ∧ TopologicalSpace.IsTopologicalBasis B)
∧ (∀ U V : Set (PrimeSpectrum R),
  IsOpen U → IsCompact U → IsOpen V → IsCompact V → IsCompact (U ∩ V)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact spec_is_quasi_compact.isCompact_univ
  · use Set.range (fun (f : R) ↦ (PrimeSpectrum.basicOpen f))
    constructor
    · rintro _ ⟨r, rfl⟩
      exact PrimeSpectrum.isCompact_basicOpen r
    · exact PrimeSpectrum.isTopologicalBasis_basic_opens
  · exact QuasiSeparatedSpace.inter_isCompact
