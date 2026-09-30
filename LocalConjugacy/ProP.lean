module

public import LocalConjugacy.Definitions

@[expose] public section

namespace LocalConjugacy

theorem proP_of_isPGroup {G : Type*} [Group G] [TopologicalSpace G]
    {p : ℕ} (h : IsPGroup p G) : IsProP p G :=
  fun U => h.to_quotient U.toSubgroup

/-- A continuous homomorphism into a discrete group sends pro-`p` elements
to elements of finite `p`-power order. No finiteness of the codomain is needed. -/
theorem image_pow {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {p : ℕ} (h : IsProP p G) (f : G →* F) (hf : Continuous f) (x : G) :
    ∃ k : ℕ, f x ^ p ^ k = 1 := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  obtain ⟨k, hk⟩ := h U (QuotientGroup.mk' U.toSubgroup x)
  refine ⟨k, ?_⟩
  have he := congrArg (QuotientGroup.lift U.toSubgroup f (by rfl)) hk
  simpa using he

/-- The continuity argument needed at the end of Proposition 2.1, valid
even for an infinite discrete coefficient `p`-group. -/
theorem continuous_hom_eq_one_of_coprime {G N : Type*} [Group G] [Group N]
    [TopologicalSpace G] [TopologicalSpace N] [DiscreteTopology N]
    {p q : ℕ} (hG : IsProP q G) (hN : IsPGroup p N) (hpq : p.Coprime q)
    (f : G →* N) (hf : Continuous f) (x : G) : f x = 1 := by
  obtain ⟨a, ha⟩ := hN (f x)
  obtain ⟨b, hb⟩ := image_pow hG f hf x
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hpq.pow a b)
    (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb)

theorem isPGroup_map_of_continuous {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {p : ℕ} (H : Subgroup G) (hH : IsProP p H) (f : G →* F) (hf : Continuous f) :
    IsPGroup p (H.map f) := by
  intro z
  obtain ⟨x, hx, he⟩ := z.property
  obtain ⟨k, hk⟩ := image_pow hH (f.comp H.subtype)
    (hf.comp continuous_subtype_val) ⟨x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  change z.val ^ p ^ k = 1
  change f x ^ p ^ k = 1 at hk
  rwa [he] at hk

/-- Continuous surjective homomorphisms preserve the pro-`p` property. -/
theorem isProP_of_continuous_surjective {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]
    {p : ℕ} (hG : IsProP p G) (f : G →* F) (hf : Continuous f)
    (hs : Function.Surjective f) : IsProP p F := by
  intro U z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup z
  obtain ⟨x, rfl⟩ := hs y
  exact image_pow hG ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) x

theorem isProP_subgroupOf {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {p : ℕ} {P H : Subgroup G}
    (hP : IsProP p P) (hPH : P ≤ H) : IsProP p (P.subgroupOf H) := by
  let e := (Subgroup.subgroupOfEquivOfLe hPH).symm
  apply isProP_of_continuous_surjective hP e.toMonoidHom _ e.surjective
  exact (continuous_subtype_val.subtype_mk (fun x => hPH x.property)).subtype_mk
    (fun x => x.property)

end LocalConjugacy
