module

public import LocalConjugacy.SupplementConjugacy
public import LocalConjugacy.LocalSupplement

@[expose] public section

namespace LocalConjugacy

variable {G : Type*} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]

theorem sylowPro_card_eq {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    (hP : IsSylowPro p H P) : Nat.card P = p ^ (Nat.card H).factorization p := by
  letI : Profinite G := ⟨⟩
  obtain ⟨S, hS⟩ := sylow_of_isSylowPro (P.subgroupOf H)
    (isSylowPro_subgroupOf H P (isClosed_discrete _) hP)
  have hc := S.card_eq_multiplicity
  rw [hS] at hc
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv] at hc

theorem card_dvd_of_locallyContains (H K : Subgroup G) (h : LocallyContains H K) :
    Nat.card K ∣ Nat.card H := by
  apply (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp
  intro p
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP, g, hg⟩ := h p hp
    apply (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
    have hd := Subgroup.card_dvd_of_le hg
    have hc : Nat.card (conjugate g P) = Nat.card P :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rwa [hc, sylowPro_card_eq hP] at hd
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact le_rfl

theorem isSylowPro_of_card {p : ℕ} [Fact p.Prime] (H P : Subgroup G) (hPH : P ≤ H)
    (hc : Nat.card P = p ^ (Nat.card H).factorization p) : IsSylowPro p H P := by
  letI : Profinite G := ⟨⟩
  have hc' : Nat.card (P.subgroupOf H) = p ^ (Nat.card H).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv).trans hc
  let S : Sylow p H := Sylow.ofCard (P.subgroupOf H) hc'
  have hs := isSylowPro_map_subtype H (isClosed_discrete _) S.toSubgroup (sylow_isSylowPro S)
  change IsSylowPro p H ((P.subgroupOf H).map H.subtype) at hs
  rwa [Subgroup.map_subgroupOf_eq_of_le hPH] at hs

theorem locallyConjugate_of_locallyContains_card (H K : Subgroup G)
    (h : LocallyContains H K) (hc : Nat.card K = Nat.card H) : LocallyConjugate K H := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := h p hp
  refine ⟨P, conjugate g P, hP, isSylowPro_of_card H (conjugate g P) hg ?_, g, rfl⟩
  have hcard : Nat.card (conjugate g P) = Nat.card P :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [hcard, sylowPro_card_eq hP, hc]

theorem card_complement_dvd_supplement (N H K : Subgroup G) [N.Normal]
    (hc : N.IsComplement' H) (hs : Supplements N K) : Nat.card H ∣ Nat.card K := by
  have he : Nat.card H = N.index := hc.card_right
  rw [he, ← Subgroup.relIndex_top_right N,
    ← sup_eq_top_of_supplements N K hs, Subgroup.relIndex_sup_left]
  exact N.relIndex_dvd_card K

/-- Finite local inclusion after quotienting by the normal intersection.
The included subgroup may intersect N, as happens in finite quotient images. -/
theorem finite_nilpotent_local_inclusion (N H K : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] (hcase : Supersolvable G ∨ Group.IsNilpotent (G ⧸ N))
    (hsH : Supplements N H) (hsK : Supplements N K)
    (hnormal : IntersectionNormal N H) (hloc : LocallyContains H K) :
    ∃ g : G, conjugate g K ≤ H := by
  letI : Profinite G := ⟨⟩
  letI := inf_normal_of_stabNormal N H (sup_eq_top_of_supplements N H hsH) hnormal
  let D := N ⊓ H
  let π := QuotientGroup.mk' D
  letI := nilpotent_subgroup_map N π
  have hHq := supplements_map N H hsH π (QuotientGroup.mk'_surjective D)
  have hKq := supplements_map N K hsK π (QuotientGroup.mk'_surjective D)
  have hc : (N.map π).IsComplement' (H.map π) :=
    isComplement'_map_mk' N H (sup_eq_top_of_supplements N H hsH)
  have hl := locallyContains_map_finite H K (isClosed_discrete _) hloc π continuous_quotient_mk'
  have hcard : Nat.card (K.map π) = Nat.card (H.map π) :=
    Nat.dvd_antisymm (card_dvd_of_locallyContains _ _ hl) (card_complement_dvd_supplement _ _ _ hc hKq)
  have hconj := (finite_nilpotent_supplement_conjugacy (N.map π) (K.map π) (H.map π)
    (conjugacy_case_map N π (QuotientGroup.mk'_surjective D) hcase) hKq hHq).mpr
      (locallyConjugate_of_locallyContains_card _ _ hl hcard)
  obtain ⟨q, hq⟩ := hconj
  exact conjugate_le_of_quotient D H K inf_le_right q hq.le

end LocalConjugacy
