module

public import LocalConjugacy.Supplements

@[expose] public section

namespace LocalConjugacy
open scoped Pointwise

theorem finite_eq_top_of_locallyContains {G : Type*} [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (H : Subgroup G)
    (hloc : LocallyContains H ⊤) : H = ⊤ := by
  apply H.index_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hloc p hp
  obtain ⟨S, hS⟩ := sylow_of_isSylowPro P hP
  have he : (g • S).toSubgroup ≤ H := by
    rw [sylow_smul_toSubgroup, hS]
    exact hg
  exact (g • S).not_dvd_index (hd.trans (Subgroup.index_dvd_of_le he))

theorem finite_supplements_of_locallyContains {G : Type*} [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (N H J : Subgroup G) [N.Normal]
    (hNJ : Supplements N J) (hloc : LocallyContains H J) : Supplements N H := by
  letI : Profinite G := ⟨⟩
  let π := QuotientGroup.mk' N
  have hj : J.map π = ⊤ := by
    apply top_unique
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨n, hn, j, hj, rfl⟩ := hNJ x
    refine ⟨j, hj, ?_⟩
    have hn' : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    change π j = π (n * j)
    simp only [map_mul, hn', one_mul]
  have hl : LocallyContains (H.map π) ⊤ := by
    rw [← hj]
    exact locallyContains_map_finite H J (isClosed_discrete _) hloc π continuous_quotient_mk'
  have he := congrArg (fun L : Subgroup (G ⧸ N) => L.comap π)
    (finite_eq_top_of_locallyContains (H.map π) hl)
  apply supplements_of_sup_eq_top N H
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk', Subgroup.comap_top,
    sup_comm H N] using he

/-- The supplementary-subgroup assertion used implicitly in the paper's
proofs of Corollary 1.3 and the fixed-point results. -/
theorem supplements_of_locallyContains {G : Type*} [Group G] [TopologicalSpace G]
    [Profinite G] (N H J : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hJ : IsClosed (J : Set G)) (hNJ : Supplements N J)
    (hloc : LocallyContains H J) : Supplements N H := by
  have hc : IsClosed ((N ⊔ H : Subgroup G) : Set G) := by
    rw [Subgroup.normal_mul]
    exact (hN.isCompact.mul hH.isCompact).isClosed
  apply supplements_of_sup_eq_top N H
  apply top_unique
  intro x _
  apply mem_of_mem_sup_openNormal (N ⊔ H) hc x
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  have hf := finite_supplements_of_locallyContains (N.map π) (H.map π) (J.map π)
    (supplements_map N J hNJ π (QuotientGroup.mk'_surjective _))
    (locallyContains_map_finite H J hJ hloc π continuous_quotient_mk')
  have he : (N ⊔ H).map π = ⊤ := by
    rw [Subgroup.map_sup]
    exact sup_eq_top_of_supplements _ _ hf
  have hm : π x ∈ (N ⊔ H).map π := by rw [he]; trivial
  change x ∈ ((N ⊔ H).map π).comap π at hm
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using hm

end LocalConjugacy
