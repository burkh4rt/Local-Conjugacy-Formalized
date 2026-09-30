module

public import LocalConjugacy.SupersolvableEmbeddings
public import LocalConjugacy.ZornRestriction
public import LocalConjugacy.CocycleRebase

@[expose] public section

namespace LocalConjugacy

section Intermediate
variable {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]

theorem closed_intermediate_image (P L : Subgroup J) (hL : IsClosed (L : Set J))
    (hPL : P ≤ L) (K : Subgroup L) (hK : IsClosed (K : Set L))
    (hPK : P.subgroupOf L ≤ K) (hproper : K < ⊤) :
    IsClosed (K.map L.subtype : Set J) ∧ P ≤ K.map L.subtype ∧ K.map L.subtype < L := by
  letI := profinite_closed_subgroup L hL
  refine ⟨(hK.isCompact.image continuous_subtype_val).isClosed, ?_, ?_⟩
  · simpa only [Subgroup.map_subgroupOf_eq_of_le hPL] using Subgroup.map_mono hPK (f := L.subtype)
  · refine lt_of_le_of_ne ((Subgroup.map_le_range L.subtype K).trans (le_of_eq L.range_subtype)) ?_
    intro he
    have he' : K.map L.subtype = (⊤ : Subgroup L).map L.subtype := by
      rw [← MonoidHom.range_eq_map, L.range_subtype, he]
    exact hproper.ne ((Subgroup.map_injective L.subtype_injective) he')

theorem openNormal_lt_top_of_prime_index {L : Type*} [Group L] [TopologicalSpace L]
    (K : OpenNormalSubgroup L) (hq : K.toSubgroup.index.Prime) : K.toSubgroup < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  exact hq.ne_one (by rw [he, Subgroup.index_top])

end Intermediate

section Rebase
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

def Cocycle.fromMappedSubgroup {L : Subgroup J} (K : Subgroup L)
    (f : Cocycle (N := N) (K.map L.subtype)) : Cocycle (J := L) (N := N) K where
  toFun x := f.toFun ⟨x, Subgroup.mem_map_of_mem L.subtype x.property⟩
  continuous_toFun := f.continuous_toFun.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  map_mul x y := f.map_mul ⟨x, Subgroup.mem_map_of_mem L.subtype x.property⟩
    ⟨y, Subgroup.mem_map_of_mem L.subtype y.property⟩

theorem Cocycle.ExtendsTo.on_mapped_subgroup {P L : Subgroup J}
    {f : Cocycle (N := N) P} (K : Subgroup L) (hPK : P.subgroupOf L ≤ K)
    (h : f.ExtendsTo (K.map L.subtype)) :
    (f.onSubgroup (L := L)).ExtendsTo K := by
  obtain ⟨_, F, n, hn⟩ := h
  exact ⟨hPK, F.fromMappedSubgroup K, n, fun x => hn ⟨x, x.property⟩⟩

theorem Cocycle.ExtendsTo.of_subgroup_top {P L : Subgroup J}
    {f : Cocycle (N := N) P} (hPL : P ≤ L)
    (h : (f.onSubgroup (L := L)).ExtendsTo ⊤) : f.ExtendsTo L := by
  obtain ⟨_, F, n, hn⟩ := h
  exact ⟨hPL, F.ofSubgroupTop, n, fun x => hn ⟨⟨x, hPL x.property⟩, x.property⟩⟩

end Rebase

section Restriction
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Injectivity in the supersolvable branch, proved first by Zorn on a fixed pair. -/
theorem supersolvable_sylow_restriction_injective
    (hG : Prosupersolvable (ActionProduct J N)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hfg : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) f) (restrictCocycle le_top g)) :
    Cohomologous f g := by
  apply cohomologous_of_zorn_step P f g hfg
  intro L hL hPL hmin
  letI := profinite_closed_subgroup L hL
  have hGL := prosupersolvable_restricted_action hG L hL
  have hPLs := isSylowPro_subgroupOf L P hL (isSylowPro_of_intermediate hP hPL.le le_top)
  have hproper : P.subgroupOf L ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le hPL.le, ← MonoidHom.range_eq_map, L.range_subtype] at hh
    exact hPL.ne hh
  have hsmall (K : Subgroup L) (hK : IsClosed (K : Set L))
      (hPK : P.subgroupOf L ≤ K) (hproper : K < ⊤) :
      Cohomologous
        (restrictCocycle (show K ≤ ⊤ from le_top) (restrictCocycle le_top f).subgroupTop)
        (restrictCocycle le_top (restrictCocycle le_top g).subgroupTop) := by
    obtain ⟨hclosed, hle, hlt⟩ := closed_intermediate_image P L hL hPL.le K hK hPK hproper
    obtain ⟨n, hn⟩ := hmin _ hclosed hle hlt
    exact ⟨n, fun x => hn ⟨x, Subgroup.mem_map_of_mem L.subtype x.property⟩⟩
  have hfgL : Cohomologous (restrictCocycle (show L ≤ ⊤ from le_top) f).subgroupTop
      (restrictCocycle le_top g).subgroupTop := by
    rcases supersolvable_hall_or_prime_index_reduction hGL hN (P.subgroupOf L) hPLs hproper with
      ⟨M, Q, _, _, hQ, _, hPQ, hQt, hres⟩ | ⟨_, K, hPK, hq, hne⟩
    · exact hres.1 _ _ (hsmall Q hQ.1 hPQ hQt)
    · letI : Fact K.toSubgroup.index.Prime := ⟨hq⟩
      exact (coprime_prime_index_restriction hne hN K.toSubgroup K.isClosed rfl).1 _ _
        (hsmall K.toSubgroup K.isClosed hPK (openNormal_lt_top_of_prime_index K hq))
  obtain ⟨n, hn⟩ := hfgL
  exact ⟨n, fun x => hn ⟨x, trivial⟩⟩

/-- Surjectivity in the supersolvable branch, using minimality only for the
specified stable class and the injectivity theorem already proved above. -/
theorem supersolvable_sylow_extension
    (hG : Prosupersolvable (ActionProduct J N)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (f : Cocycle (N := N) P) (hf : InvariantUnder ⊤ P f) : f.ExtendsTo ⊤ := by
  apply extendsTo_of_zorn_step P f
  intro L hL hPL hmin
  letI := profinite_closed_subgroup L hL
  have hGL := prosupersolvable_restricted_action hG L hL
  have hPLs := isSylowPro_subgroupOf L P hL (isSylowPro_of_intermediate hP hPL.le le_top)
  have hproper : P.subgroupOf L ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le hPL.le, ← MonoidHom.range_eq_map, L.range_subtype] at hh
    exact hPL.ne hh
  have hsmall (K : Subgroup L) (hK : IsClosed (K : Set L))
      (hPK : P.subgroupOf L ≤ K) (hproper : K < ⊤) :
      (f.onSubgroup (L := L)).ExtendsTo K := by
    obtain ⟨hclosed, hle, hlt⟩ := closed_intermediate_image P L hL hPL.le K hK hPK hproper
    exact (hmin _ hclosed hle hlt).on_mapped_subgroup K hPK
  have hfL : InvariantUnder ⊤ (P.subgroupOf L) (f.onSubgroup (L := L)) := by
    intro j _
    obtain ⟨n, hn⟩ := hf j trivial
    exact ⟨n, fun x hx hjx => hn x hx hjx⟩
  apply Cocycle.ExtendsTo.of_subgroup_top hPL.le
  rcases supersolvable_hall_or_prime_index_reduction hGL hN (P.subgroupOf L) hPLs hproper with
    ⟨M, Q, hMn, hM, hQ, hMQ, hPQ, hQt, _⟩ | ⟨hPn, K, hPK, hq, hne⟩
  · letI := hMn
    obtain ⟨_, g, hgf⟩ := hsmall Q hQ.1 hPQ hQt
    obtain ⟨F, hF⟩ := extend_cocycle_across_trivial_factor M Q hM.1 hQ.1 hMQ
      (prosupersolvable_action_trivial_on_high_primes hGL hN M hM.hasProPrimes) g
    refine ⟨le_top, F, ?_⟩
    change Cohomologous (restrictCocycle hPQ (restrictCocycle le_top F)) (f.onSubgroup (L := L))
    rw [hF]
    exact hgf
  · letI := hPn
    letI : Fact K.toSubgroup.index.Prime := ⟨hq⟩
    have hinj : ∀ a b : Cocycle (J := L) (N := N) K.toSubgroup,
        Cohomologous (restrictCocycle hPK a) (restrictCocycle hPK b) → Cohomologous a b := by
      intro a b hab
      letI := profinite_closed_subgroup K.toSubgroup K.isClosed
      have hGK := prosupersolvable_restricted_action hGL K.toSubgroup K.isClosed
      have hPs := isSylowPro_subgroupOf K.toSubgroup (P.subgroupOf L) K.isClosed
        (isSylowPro_of_intermediate hPLs hPK le_top)
      have hh : Cohomologous a.subgroupTop b.subgroupTop := by
        apply supersolvable_sylow_restriction_injective hGK hN _ hPs
        obtain ⟨n, hn⟩ := hab
        exact ⟨n, fun x => hn ⟨x, x.property⟩⟩
      obtain ⟨n, hn⟩ := hh
      exact ⟨n, fun x => hn ⟨x, trivial⟩⟩
    exact extend_stable_class_across_prime_index (locallyFiniteGroup_of_finite N)
      hne hN K.toSubgroup (P.subgroupOf L) hPK K.isClosed rfl hinj
      (f.onSubgroup (L := L)) hfL
      (hsmall K.toSubgroup K.isClosed hPK (openNormal_lt_top_of_prime_index K hq))

/-- The primary restriction isomorphism for prosupersolvable semidirect
products, with a possibly infinite profinite acting group. -/
theorem supersolvable_sylow_restriction
    (hG : Prosupersolvable (ActionProduct J N)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P) :
    RestrictionIsomorphism (N := N) ⊤ P le_top := by
  refine ⟨supersolvable_sylow_restriction_injective hG hN P hP, ?_⟩
  intro f hf
  obtain ⟨_, F, hF⟩ := supersolvable_sylow_extension hG hN P hP f hf
  exact ⟨F, hF⟩

end Restriction
end LocalConjugacy
