module

public import LocalConjugacy.StructuralQuotients
public import LocalConjugacy.FiniteLocalInclusion

@[expose] public section

namespace LocalConjugacy


section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Local containment in a complement is local conjugacy: the quotient by
N maps a Sylow of the supplement onto a Sylow, and is injective on H. -/
theorem locallyConjugate_of_locallyContains_complement (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hc : N.IsComplement' H) (hsK : Supplements N K) (hloc : LocallyContains H K) :
    LocallyConjugate K H := by
  letI := profinite_quotient N hN
  letI := profinite_closed_subgroup H hH
  let π := QuotientGroup.mk' N
  let φ := π.comp H.subtype
  have hsH : Supplements N H := fun g => by
    obtain ⟨⟨n, h⟩, he⟩ := hc.surjective g
    exact ⟨n, n.property, h, h.property, he⟩
  have hφ := (complement_quotient_bijective N H hsH hc.disjoint.eq_bot).1
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hloc p hp
  let Q := conjugate g P
  have hQ := isSylowPro_conjugate g K P hP
  have himage := sylowPro_map (conjugate g K) Q (conjugate_closed g K hK) hQ
    π continuous_quotient_mk'
  rw [supplement_image_quotient_eq_top N (conjugate g K) (supplements_conjugate N K hsK g)] at himage
  have he : (Q.subgroupOf H).map φ = Q.map π := by
    rw [show φ = π.comp H.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hg]
  rw [← he] at himage
  have hs := sylowPro_of_injective_map (Q.subgroupOf H)
    (hQ.2.1.preimage continuous_subtype_val) (isProP_subgroupOf hQ.2.2.1 hg)
    φ (continuous_quotient_mk'.comp continuous_subtype_val) hφ himage
  have hQH := isSylowPro_map_subtype H hH _ hs
  rw [Subgroup.map_subgroupOf_eq_of_le hg] at hQH
  exact ⟨P, Q, hP, hQH, g, rfl⟩

/-- The normal-intersection quotient reduction, using images throughout.
This permits arbitrary closed supplements before passing to the quotient. -/
theorem pronilpotent_local_inclusion (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hpron : Pronilpotent N) (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hsH : Supplements N H) (hsK : Supplements N K)
    (hnormal : IntersectionNormal N H) (hloc : LocallyContains H K) :
    ∃ g : G, conjugate g K ≤ H := by
  letI := inf_normal_of_stabNormal N H (sup_eq_top_of_supplements N H hsH) hnormal
  let D := N ⊓ H
  have hD : IsClosed (D : Set G) := hN.inter hH
  letI := profinite_quotient D hD
  let π := QuotientGroup.mk' D
  have hNq : IsClosed (N.map π : Set (G ⧸ D)) := (hN.isCompact.image continuous_quotient_mk').isClosed
  have hHq : IsClosed (H.map π : Set (G ⧸ D)) := (hH.isCompact.image continuous_quotient_mk').isClosed
  have hKq : IsClosed (K.map π : Set (G ⧸ D)) := (hK.isCompact.image continuous_quotient_mk').isClosed
  have hsHq := supplements_map N H hsH π (QuotientGroup.mk'_surjective D)
  have hsKq := supplements_map N K hsK π (QuotientGroup.mk'_surjective D)
  have hc := isComplement'_map_mk' N H (sup_eq_top_of_supplements N H hsH)
  have hl := locallyContains_map H K hK hloc π continuous_quotient_mk'
  have hcaseq : Prosupersolvable (G ⧸ D) ∨ Pronilpotent ((G ⧸ D) ⧸ N.map π) := by
    rcases hcase with h | h
    · exact Or.inl (prosupersolvable_of_continuous_surjective h π continuous_quotient_mk'
        (QuotientGroup.mk'_surjective D))
    · exact Or.inr (pronilpotent_quotient_image N π continuous_quotient_mk'
        (QuotientGroup.mk'_surjective D) h)
  have hconj := (theorem_1_1 (N.map π) (K.map π) (H.map π) hNq hKq hHq
    (pronilpotent_subgroup_image N hpron π continuous_quotient_mk') hcaseq hsKq hsHq).mpr
      (locallyConjugate_of_locallyContains_complement _ _ _ hNq hHq hKq hc hsKq hl)
  obtain ⟨q, hq⟩ := hconj
  exact conjugate_le_of_quotient D H K inf_le_right q hq.le

/-- Corollary 1.3, with the unchanged normal-intersection hypothesis. -/
theorem corollary_1_3 (N J H : Subgroup G)
    (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hH : IsClosed (H : Set G)) (hsplit : Splits N J)
    (hpron : Pronilpotent N) (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (hnormal : IntersectionNormal N H) (hlocal : LocallyContains H J) :
    ∃ g : G, conjugate g J ≤ H := by
  letI := hsplit.1
  have hsH := supplements_of_locallyContains N H J hN hH hJ hsplit.2.1 hlocal
  have hcase' : Prosupersolvable G ∨ Pronilpotent (G ⧸ N) := by
    rcases hcase with h | h
    · exact Or.inl h
    · exact Or.inr (pronilpotent_quotient_of_supplement N J hsplit.2.1 h)
  exact pronilpotent_local_inclusion N H J hN hH hJ hpron hcase' hsH hsplit.2.1 hnormal hlocal

end Profinite
end LocalConjugacy
