module

public import LocalConjugacy.ProfiniteQuotients

@[expose] public section

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
  [IsTopologicalGroup G] [IsTopologicalGroup F]

theorem pronilpotent_subgroup_image (N : Subgroup G) (hN : Pronilpotent N)
    (f : G →* F) (hf : Continuous f) : Pronilpotent (N.map f) :=
  pronilpotent_of_continuous_surjective hN (subgroupImageHom N f)
    ((hf.comp continuous_subtype_val).subtype_mk _) (subgroupImageHom_surjective N f)

theorem supplement_quotient_surjective (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨n, hn, h, hh, rfl⟩ := hs x
  refine ⟨⟨h, hh⟩, ?_⟩
  change QuotientGroup.mk' N h = QuotientGroup.mk' N (n * h)
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [map_mul, hn1, one_mul]

theorem supplement_image_quotient_eq_top (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : H.map (QuotientGroup.mk' N) = ⊤ := by
  rw [← H.range_subtype, ← MonoidHom.range_comp]
  exact MonoidHom.range_eq_top_of_surjective _ (supplement_quotient_surjective N H hs)

theorem pronilpotent_quotient_of_supplement (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) (hH : Pronilpotent H) : Pronilpotent (G ⧸ N) :=
  pronilpotent_of_continuous_surjective hH ((QuotientGroup.mk' N).comp H.subtype)
    (continuous_quotient_mk'.comp continuous_subtype_val) (supplement_quotient_surjective N H hs)

theorem pronilpotent_quotient_image (N : Subgroup G) [N.Normal]
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) [(N.map f).Normal]
    (h : Pronilpotent (G ⧸ N)) : Pronilpotent (F ⧸ N.map f) := by
  let φ := QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N)
  apply pronilpotent_of_continuous_surjective h φ
  · apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact continuous_quotient_mk'.comp hf
  · intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (N.map f) y
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨QuotientGroup.mk' N x, rfl⟩

end Maps

end LocalConjugacy
