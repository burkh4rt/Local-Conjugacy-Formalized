module

public import LocalConjugacy.AbelianInclusion
public import LocalConjugacy.NormalIntersectionCompactness

@[expose] public section

/-! The finite-normal-subgroup stage of Proposition 4.1. The ambient group
remains profinite. The complement case is reduced to a finite quotient in
which the complement survives, so the proved abelian cocycle argument supplies
the role of the conjugacy theorem cited in the manuscript. -/

namespace LocalConjugacy

theorem abelian_complement_inclusion_finite_kernel
    {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal] [Finite N]
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hcomm : ∀ n m : N, n * m = m * n)
    (hs : Supplements N H) (hd : N ⊓ H = ⊥)
    (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  letI := finiteIndex_of_finite_supplement N H hs
  obtain ⟨U, hUH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (H.isOpen_of_isClosed_of_finiteIndex hH) H.one_mem
  let π := QuotientGroup.mk' U.toSubgroup
  have hdis : N.map π ⊓ H.map π = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨⟨n, hn, rfl⟩, hh⟩
    obtain ⟨h, hh, he⟩ := hh
    have hu : n⁻¹ * h ∈ U := QuotientGroup.eq.mp he.symm
    have hnH : n ∈ H := by
      have hm := H.mul_mem hh (H.inv_mem (hUH hu))
      simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hm
    have hn1 : n = 1 := by
      have hm : n ∈ N ⊓ H := ⟨hn, hnH⟩
      simpa only [hd, Subgroup.mem_bot] using hm
    simpa only [hn1, map_one] using (Subgroup.one_mem (⊥ : Subgroup (G ⧸ U.toSubgroup)))
  have hc := isComplement'_of_supplements_inf (N.map π) (H.map π)
    (supplements_map N H hs π (QuotientGroup.mk'_surjective _)) hdis
  obtain ⟨q, hq⟩ := AbelianComplement.finite_local_inclusion (N.map π) (H.map π) hc
    (commutative_map N hcomm π) (K.map π)
    (locallyContains_map_finite H K hK hlocal π continuous_quotient_mk')
  exact conjugate_le_of_quotient U.toSubgroup H K hUH q hq

theorem quotient_inclusion_conjugator_from_factor
    {G : Type*} [Group G] (A B N H K : Subgroup G) [A.Normal]
    (hs : Supplements N K) (hAB : A ⊔ B = N)
    (hc : ∃ g : G ⧸ A, conjugate g (K.map (QuotientGroup.mk' A)) ≤
      H.map (QuotientGroup.mk' A)) :
    ∃ b : B, conjugate (QuotientGroup.mk' A b) (K.map (QuotientGroup.mk' A)) ≤
      H.map (QuotientGroup.mk' A) := by
  let π := QuotientGroup.mk' A
  have hn : N.map π = B.map π := by
    rw [← hAB, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hs' := supplements_map N K hs π (QuotientGroup.mk'_surjective A)
  rw [hn] at hs'
  obtain ⟨g, hg⟩ := hc
  obtain ⟨n, hn, k, hk, rfl⟩ := hs' g
  rw [← conjugate_comp, conjugate_eq_self_of_mem (K.map π) hk] at hg
  obtain ⟨b, hb, rfl⟩ := hn
  exact ⟨⟨b, hb⟩, hg⟩

universe u

private theorem abelian_inclusion_finite_kernel_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]
      (N H K : Subgroup G) [N.Normal] [Finite N], Nat.card N = n →
      IsClosed (N : Set G) → IsClosed (H : Set G) → IsClosed (K : Set G) →
      (∀ a b : N, a * b = b * a) → Supplements N H → Supplements N K →
      LocallyContains H K → ∃ g : G, conjugate g K ≤ H := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ N H K _ _ hcard hN hH hK hcomm hsH hsK hlocal
    letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hcomm }
    have hquot (D : Subgroup G) [D.Normal] (hDN : D ≤ N) (hD : D ≠ ⊥) :
        ∃ q : G ⧸ D, conjugate q (K.map (QuotientGroup.mk' D)) ≤
          H.map (QuotientGroup.mk' D) := by
      letI : Finite D := Finite.of_injective (Subgroup.inclusion hDN)
        (Subgroup.inclusion_injective hDN)
      have hDc : IsClosed (D : Set G) :=
        (Set.finite_coe_iff.mp (inferInstance : Finite D)).isClosed
      letI := profinite_quotient D hDc
      let π := QuotientGroup.mk' D
      letI : Finite (N.map π) := Finite.of_surjective (subgroupImageHom N π)
        (subgroupImageHom_surjective N π)
      exact ih _ (hcard ▸ card_map_quotient_lt_finite_kernel N D hDN hD)
        (N.map π) (H.map π) (K.map π) rfl
        (hN.isCompact.image continuous_quotient_mk').isClosed
        (hH.isCompact.image continuous_quotient_mk').isClosed
        (hK.isCompact.image continuous_quotient_mk').isClosed
        (commutative_map N hcomm π)
        (supplements_map N H hsH π (QuotientGroup.mk'_surjective D))
        (supplements_map N K hsK π (QuotientGroup.mk'_surjective D))
        (locallyContains_map H K hK hlocal π continuous_quotient_mk')
    by_cases hpgroup : ∃ p : ℕ, p.Prime ∧ IsPGroup p N
    · obtain ⟨p, hp, hNp⟩ := hpgroup
      letI : Fact p.Prime := ⟨hp⟩
      let D := N ⊓ H
      letI : D.Normal := inf_normal_of_stabNormal N H
        (sup_eq_top_of_supplements N H hsH) (intersectionNormal_of_commutative N H hcomm)
      by_cases hD : D = ⊥
      · have hNK : N ⊓ K = ⊥ := by
          obtain ⟨P, hP, g, hg⟩ := hlocal p hp
          have he := inf_eq_inf_sylowPro_profinite N K P hK hNp hP
          apply eq_bot_iff.mpr
          intro x hx
          have hxP : x ∈ P := (show x ∈ N ⊓ P from he ▸ hx).2
          have hm : g * x * g⁻¹ ∈ D :=
            ⟨(inferInstance : N.Normal).conj_mem x hx.1 g,
              hg (Subgroup.mem_map_of_mem _ hxP)⟩
          have hx1 : g * x * g⁻¹ = 1 := by simpa only [hD, Subgroup.mem_bot] using hm
          change x = 1
          have hc := congrArg (fun z => g⁻¹ * z * g) hx1
          simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
            inv_mul_cancel, mul_one, one_mul] using hc
        -- Both supplements are now complements, exactly as in the paper.
        have hcK := isComplement'_of_supplements_inf N K hsK hNK
        have hcH := isComplement'_of_supplements_inf N H hsH hD
        obtain ⟨g, hg⟩ := abelian_complement_inclusion_finite_kernel N H K hH hK hcomm hsH
          hcH.disjoint.eq_bot hlocal
        have hsK' : Supplements N K := by
          intro x
          obtain ⟨⟨n, k⟩, he⟩ := hcK.surjective x
          exact ⟨n, n.property, k, k.property, he⟩
        have he := eq_of_supplements_le N H (conjugate g K)
          (supplements_conjugate N K hsK' g) hcH.disjoint.eq_bot hg
        exact ⟨g, he.le⟩
      · obtain ⟨q, hq⟩ := hquot D inf_le_left hD
        exact conjugate_le_of_quotient D H K inf_le_right q hq
    · obtain ⟨A₀, B₀, hAc, hBc, hc, hcop, hA₀, hB₀⟩ := nilpotent_coprime_split hpgroup
      letI := hAc
      letI := hBc
      let A := A₀.map N.subtype
      let B := B₀.map N.subtype
      letI : A.Normal := inferInstance
      letI : B.Normal := inferInstance
      have hAN : A ≤ N := by
        simpa only [N.range_subtype] using A₀.map_le_range N.subtype
      have hBN : B ≤ N := by
        simpa only [N.range_subtype] using B₀.map_le_range N.subtype
      have hAB : A ⊔ B = N := by
        change A₀.map N.subtype ⊔ B₀.map N.subtype = N
        rw [← Subgroup.map_sup, hc.sup_eq_top, ← MonoidHom.range_eq_map, N.range_subtype]
      have hA : A ≠ ⊥ := by
        intro h
        apply hA₀
        apply Subgroup.map_injective N.subtype_injective
        simpa only [Subgroup.map_bot] using h
      have hB : B ≠ ⊥ := by
        intro h
        apply hB₀
        apply Subgroup.map_injective N.subtype_injective
        simpa only [Subgroup.map_bot] using h
      have hcop' : (Nat.card A).Coprime (Nat.card B) := by
        simpa only [A, B, Subgroup.card_map_of_injective N.subtype_injective] using hcop
      obtain ⟨b, hb⟩ := quotient_inclusion_conjugator_from_factor A B N H K hsK hAB
        (hquot A hAN hA)
      obtain ⟨a, ha⟩ := quotient_inclusion_conjugator_from_factor B A N H K hsK
        ((sup_comm B A).trans hAB) (hquot B hBN hB)
      exact ⟨(a : G) * b, merge_coprime_conjugators_profinite A B K H hH hcop'
        (Subgroup.disjoint_of_coprime_natCard hcop') a b
        (conjugate_le_sup_of_quotient A K H b hb)
        (conjugate_le_sup_of_quotient B K H a ha)⟩

/-- Proposition 4.1 for finite abelian `N`, proved by induction on `|N|`
while the ambient group remains profinite. -/
theorem abelian_inclusion_finite_kernel
    {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hcomm : ∀ n m : N, n * m = m * n)
    (hsH : Supplements N H) (hsK : Supplements N K) (hlocal : LocallyContains H K) :
    ∃ g : G, conjugate g K ≤ H :=
  abelian_inclusion_finite_kernel_aux (Nat.card N) N H K rfl hN hH hK hcomm hsH hsK hlocal

end LocalConjugacy
