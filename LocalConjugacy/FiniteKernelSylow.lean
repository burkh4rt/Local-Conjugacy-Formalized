module

public import LocalConjugacy.FiniteKernelTools

@[expose] public section

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

theorem normal_proP_le_sylowPro (D P : Subgroup G) [D.Normal]
    {p : ℕ} [Fact p.Prime] (hD : IsProP p D) (hP : IsSylowPro p ⊤ P) : D ≤ P := by
  apply subgroup_le_of_finite_images D P hP.2.1
  intro U
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  rw [hS]
  exact (isPGroup_quotient_image D hD U).le_sylow_of_normal S

theorem inf_eq_inf_sylowPro_profinite (N H P : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (hP : IsSylowPro p H P) : N ⊓ P = N ⊓ H := by
  letI := profinite_closed_subgroup H hH
  have hle := normal_proP_le_sylowPro (N.subgroupOf H) (P.subgroupOf H)
    (proP_of_isPGroup hN.comap_subtype) (isSylowPro_subgroupOf H P hH hP)
  apply le_antisymm (inf_le_inf_left N hP.1)
  intro x hx
  exact ⟨hx.1, hle (show (⟨x, hx.2⟩ : H) ∈ N.subgroupOf H from hx.1)⟩

theorem normal_inf_of_common_sylow_profinite (N H K P : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    (hPH : IsSylowPro p H P) (hPK : IsSylowPro p K P) (hgen : H ⊔ K = ⊤) :
    N ⊓ H = N ⊓ K ∧ (N ⊓ H).Normal := by
  have he : N ⊓ H = N ⊓ K :=
    (inf_eq_inf_sylowPro_profinite N H P hH hN hPH).symm.trans
      (inf_eq_inf_sylowPro_profinite N K P hK hN hPK)
  refine ⟨he, Subgroup.normalizer_eq_top_iff.mp ?_⟩
  apply top_unique
  rw [← hgen]
  apply sup_le
  · apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mp
    simpa only [Subgroup.inf_subgroupOf_right] using
      (inferInstance : (N.subgroupOf H).Normal)
  · rw [he]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mp
    simpa only [Subgroup.inf_subgroupOf_right] using
      (inferInstance : (N.subgroupOf K).Normal)

theorem sylowPro_top_of_pGroup_supplement_profinite (N H P : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p)
    (hN : IsPGroup p N) (hs : Supplements N H) (hP : IsSylowPro q H P) :
    IsSylowPro q ⊤ P := by
  apply isSylowPro_of_full_images P hP.2.1
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  have hNu : IsPGroup p (N.map π) :=
    hN.of_surjective (subgroupImageHom N π) (subgroupImageHom_surjective N π)
  obtain ⟨S, hS⟩ := sylow_of_isSylowPro (P.map π)
    (sylowPro_top_of_pGroup_supplement (N.map π) (H.map π) (P.map π) hne hNu
      (supplements_map N H hs π (QuotientGroup.mk'_surjective U.toSubgroup))
      (sylowPro_map_finite H P hH hP π continuous_quotient_mk'))
  exact ⟨S, hS.symm⟩

theorem isSylowPro_in_closed_subgroup {p : ℕ} {H P L : Subgroup G}
    (hL : IsClosed (L : Set G)) (hP : IsSylowPro p H P) (hHL : H ≤ L) :
    IsSylowPro p (H.subgroupOf L) (P.subgroupOf L) := by
  letI := profinite_closed_subgroup L hL
  refine ⟨fun _ hx => hP.1 hx, hP.2.1.preimage continuous_subtype_val,
    isProP_subgroupOf hP.2.2.1 (hP.1.trans hHL), ?_⟩
  intro Q hQH hQc hQp hPQ
  have he : Q.map L.subtype = P := hP.2.2.2 _
    (by rintro _ ⟨x, hx, rfl⟩; exact hQH hx)
    (hQc.isCompact.image continuous_subtype_val).isClosed
    (isProP_map Q hQp L.subtype continuous_subtype_val)
    (by simpa only [Subgroup.map_subgroupOf_eq_of_le (hP.1.trans hHL)] using
      (Subgroup.map_mono hPQ : (P.subgroupOf L).map L.subtype ≤ Q.map L.subtype))
  apply Subgroup.map_injective L.subtype_injective
  rwa [Subgroup.map_subgroupOf_eq_of_le (hP.1.trans hHL)]

/-- Once the p-Sylows coincide, local conjugacy holds inside the generated
subgroup: the other Sylows are already Sylows of the ambient group. -/
theorem locallyConjugate_generated_profinite (N H K P : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hL : IsClosed ((H ⊔ K : Subgroup G) : Set G))
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    (hsH : Supplements N H) (hsK : Supplements N K)
    (hPH : IsSylowPro p H P) (hPK : IsSylowPro p K P) :
    LocallyConjugate (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K)) := by
  let L := H ⊔ K
  letI := profinite_closed_subgroup L hL
  intro q hq
  letI : Fact q.Prime := ⟨hq⟩
  by_cases he : q = p
  · subst q
    exact ⟨P.subgroupOf L, P.subgroupOf L,
      isSylowPro_in_closed_subgroup hL hPH le_sup_left,
      isSylowPro_in_closed_subgroup hL hPK le_sup_right, 1, conjugate_one _⟩
  · obtain ⟨A, hA⟩ := exists_sylowPro_subgroup q H hH
    obtain ⟨B, hB⟩ := exists_sylowPro_subgroup q K hK
    have hAG := sylowPro_top_of_pGroup_supplement_profinite N H A hH he hN hsH hA
    have hBG := sylowPro_top_of_pGroup_supplement_profinite N K B hK he hN hsK hB
    have hAL := isSylowPro_subgroupOf L A hL
      (isSylowPro_of_intermediate hAG (hA.1.trans le_sup_left) le_top)
    have hBL := isSylowPro_subgroupOf L B hL
      (isSylowPro_of_intermediate hBG (hB.1.trans le_sup_right) le_top)
    exact ⟨A.subgroupOf L, B.subgroupOf L,
      isSylowPro_in_closed_subgroup hL hA le_sup_left,
      isSylowPro_in_closed_subgroup hL hB le_sup_right, sylowPro_conjugate _ _ hAL hBL⟩

end LocalConjugacy
