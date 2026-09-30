module

public import LocalConjugacy.FiniteConjugacyTools

@[expose] public section

namespace LocalConjugacy
open Topology

theorem profinite_quotient {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G)) : Profinite (G ⧸ D) := by
  letI : IsClosed (D : Set G) := hD
  letI : NonarchimedeanGroup (G ⧸ D) :=
    { is_nonarchimedean := by
        intro V hV
        obtain ⟨O, hOV, hO, h1⟩ := mem_nhds_iff.mp hV
        obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
          (hO.preimage (show Continuous (QuotientGroup.mk' D) from continuous_quotient_mk'))
          (by change QuotientGroup.mk' D (1 : G) ∈ O; simpa only [map_one] using h1)
        refine ⟨{ toSubgroup := U.toSubgroup.map (QuotientGroup.mk' D)
                  isOpen' := QuotientGroup.isOpenMap_coe _ U.isOpen }, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        exact hOV (hU hx) }
  exact ⟨⟩

section Images
variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
  [Profinite G] [Profinite F]

/-- Continuous epimorphisms of profinite groups preserve Sylow subgroups. -/
theorem sylowPro_map_surjective {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsSylowPro p ⊤ P) (f : G →* F)
    (hf : Continuous f) (hs : Function.Surjective f) : IsSylowPro p ⊤ (P.map f) := by
  apply isSylowPro_of_full_images _ (hP.2.1.isCompact.image hf).isClosed
  intro U
  obtain ⟨S, hS⟩ := sylowPro_map_surjective_finite P hP
    ((QuotientGroup.mk' U.toSubgroup).comp f) (continuous_quotient_mk'.comp hf)
    ((QuotientGroup.mk'_surjective U.toSubgroup).comp hs)
  exact ⟨S, by simpa only [Subgroup.map_map] using hS⟩

theorem sylowPro_map {p : ℕ} [Fact p.Prime]
    (H P : Subgroup G) (hH : IsClosed (H : Set G)) (hP : IsSylowPro p H P)
    (f : G →* F) (hf : Continuous f) : IsSylowPro p (H.map f) (P.map f) := by
  letI := profinite_closed_subgroup H hH
  have himage : IsClosed (H.map f : Set F) := (hH.isCompact.image hf).isClosed
  letI := profinite_closed_subgroup (H.map f) himage
  let φ := subgroupImageHom H f
  have hφ : Continuous φ := (hf.comp continuous_subtype_val).subtype_mk _
  have hs := sylowPro_map_surjective (P.subgroupOf H)
    (isSylowPro_subgroupOf H P hH hP) φ hφ (subgroupImageHom_surjective H f)
  have hm := isSylowPro_map_subtype (H.map f) himage _ hs
  rw [Subgroup.map_map] at hm
  change IsSylowPro p (H.map f) ((P.subgroupOf H).map (f.comp H.subtype)) at hm
  rwa [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hP.1] at hm

theorem locallyContains_map (H K : Subgroup G) (hK : IsClosed (K : Set G))
    (hlocal : LocallyContains H K) (f : G →* F) (hf : Continuous f) :
    LocallyContains (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hlocal p hp
  refine ⟨P.map f, sylowPro_map K P hK hP f hf, f g, ?_⟩
  rw [← conjugate_map]
  exact Subgroup.map_mono hg

theorem sylowPro_of_injective_map {p : ℕ} (P : Subgroup G)
    (hP : IsClosed (P : Set G)) (hp : IsProP p P)
    (f : G →* F) (hf : Continuous f) (hi : Function.Injective f)
    (hmap : IsSylowPro p ⊤ (P.map f)) : IsSylowPro p ⊤ P := by
  refine ⟨le_top, hP, hp, ?_⟩
  intro Q _ hQ hQp hPQ
  apply Subgroup.map_injective hi
  exact hmap.2.2.2 _ le_top (hQ.isCompact.image hf).isClosed
    (isProP_map Q hQp f hf) (Subgroup.map_mono hPQ)

end Images
end LocalConjugacy
