module

public import LocalConjugacy.ProfiniteSylow
public import LocalConjugacy.FiniteSylow

@[expose] public section

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G]
  [TopologicalSpace F] [Profinite G] [Finite F] [DiscreteTopology F]

theorem sylowPro_map_surjective_finite {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsSylowPro p ⊤ P) (f : G →* F)
    (hf : Continuous f) (hs : Function.Surjective f) :
    ∃ S : Sylow p F, P.map f = S.toSubgroup := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  let φ : G ⧸ U.toSubgroup →* F := QuotientGroup.kerLift f
  have hφ : Function.Surjective φ := QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl
  refine ⟨S.mapSurjective hφ, ?_⟩
  change P.map f = (S.toSubgroup).map φ
  rw [← hS, Subgroup.map_map]
  rfl

theorem sylowPro_map_finite {p : ℕ} [Fact p.Prime]
    (H P : Subgroup G) (hH : IsClosed (H : Set G)) (hP : IsSylowPro p H P)
    (f : G →* F) (hf : Continuous f) : IsSylowPro p (H.map f) (P.map f) := by
  letI := profinite_closed_subgroup H hH
  letI : Profinite F := ⟨⟩
  let φ : H →* H.map f := (f.comp H.subtype).codRestrict (H.map f)
    (fun x => Subgroup.mem_map_of_mem f x.property)
  have hφ : Continuous φ := (hf.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective φ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨S, hS⟩ := sylowPro_map_surjective_finite (P.subgroupOf H)
    (isSylowPro_subgroupOf H P hH hP) φ hφ hs
  have he : S.toSubgroup.map (H.map f).subtype = P.map f := by
    rw [← hS, Subgroup.map_map]
    change (P.subgroupOf H).map (f.comp H.subtype) = P.map f
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hP.1]
  rw [← he]
  exact isSylowPro_map_subtype (H.map f) (isClosed_discrete _) S.toSubgroup
    (sylow_isSylowPro S)

theorem locallyContains_map_finite (H K : Subgroup G)
    (hK : IsClosed (K : Set G)) (hlocal : LocallyContains H K)
    (f : G →* F) (hf : Continuous f) : LocallyContains (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hlocal p hp
  refine ⟨P.map f, sylowPro_map_finite K P hK hP f hf, f g, ?_⟩
  rw [← conjugate_map]
  exact Subgroup.map_mono hg

end LocalConjugacy
