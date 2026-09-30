module

public import LocalConjugacy.NonabelianComplement
public import LocalConjugacy.StructuralImages

@[expose] public section

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]

theorem pronilpotent_of_continuous_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Pronilpotent F := by
  intro U
  exact nilpotent_of_pronilpotent_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) ((QuotientGroup.mk'_surjective U.toSubgroup).comp hs)

theorem prosupersolvable_of_continuous_surjective (hG : Prosupersolvable G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Prosupersolvable F := by
  intro U
  exact supersolvable_of_prosupersolvable_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) ((QuotientGroup.mk'_surjective U.toSubgroup).comp hs)

end Maps

section Algebra
variable {G : Type*} [Group G]

theorem isComplement'_of_supplements_inf (N H : Subgroup G)
    (hs : Supplements N H) (hd : N ⊓ H = ⊥) : Subgroup.IsComplement' N H := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hd)
  apply Set.eq_univ_of_forall
  intro g
  exact hs g

theorem supplements_conjugate (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) (g : G) : Supplements N (conjugate g H) := by
  intro x
  obtain ⟨n, hn, h, hh, he⟩ := hs (g⁻¹ * x * g)
  refine ⟨g * n * g⁻¹, (inferInstance : N.Normal).conj_mem n hn g,
    g * h * g⁻¹, Subgroup.mem_map_of_mem _ hh, ?_⟩
  calc
    (g * n * g⁻¹) * (g * h * g⁻¹) = g * (n * h) * g⁻¹ := by group
    _ = x := by rw [he]; group

/-- An inclusion between supplements is equality if the larger subgroup is a complement. -/
theorem eq_of_supplements_le (N H K : Subgroup G)
    (hs : Supplements N K) (hd : N ⊓ H = ⊥) (hle : K ≤ H) : K = H := by
  apply le_antisymm hle
  intro h hh
  obtain ⟨n, hn, k, hk, he⟩ := hs h
  have hnH : n ∈ H := by
    have he' : n = h * k⁻¹ := by rw [← he]; group
    rw [he']
    exact H.mul_mem hh (H.inv_mem (hle hk))
  have hn1 : n = 1 := by
    have hm : n ∈ N ⊓ H := ⟨hn, hnH⟩
    rwa [hd, Subgroup.mem_bot] at hm
  rw [hn1, one_mul] at he
  exact he ▸ hk

theorem complement_quotient_bijective (N K : Subgroup G) [N.Normal]
    (hs : Supplements N K) (hd : N ⊓ K = ⊥) :
    Function.Bijective ((QuotientGroup.mk' N).comp K.subtype) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hm : (x : G)⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have hk : (x : G)⁻¹ * y ∈ K := K.mul_mem (K.inv_mem x.property) y.property
    have he : (x : G)⁻¹ * y = 1 := by
      have h : (x : G)⁻¹ * y ∈ N ⊓ K := ⟨hm, hk⟩
      rwa [hd, Subgroup.mem_bot] at h
    exact inv_mul_eq_one.mp he
  · intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨n, hn, k, hk, rfl⟩ := hs x
    refine ⟨⟨k, hk⟩, ?_⟩
    change QuotientGroup.mk' N k = QuotientGroup.mk' N (n * k)
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, hn1, one_mul]

end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

theorem pronilpotent_complement (N K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hK : IsClosed (K : Set G))
    (hs : Supplements N K) (hd : N ⊓ K = ⊥) (hq : Pronilpotent (G ⧸ N)) :
    Pronilpotent K := by
  letI := profinite_closed_subgroup K hK
  letI : IsClosed (N : Set G) := hN
  let e : K ≃* G ⧸ N := MulEquiv.ofBijective
    ((QuotientGroup.mk' N).comp K.subtype) (complement_quotient_bijective N K hs hd)
  have he : Continuous e := continuous_quotient_mk'.comp continuous_subtype_val
  have hei : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  exact pronilpotent_of_continuous_surjective hq e.symm.toMonoidHom hei e.symm.surjective

theorem locallyContains_of_locallyConjugate (H K : Subgroup G)
    (h : LocallyConjugate H K) : LocallyContains H K := by
  intro p hp
  obtain ⟨P, Q, hP, hQ, g, hg⟩ := h p hp
  refine ⟨Q, hQ, g⁻¹, ?_⟩
  rw [← hg, conjugate_inv_cancel]
  exact hP.1

/-- Proposition 3.1 in its pronilpotent-quotient branch. -/
theorem proposition_3_1_of_pronilpotent_quotient
    (N H K : Subgroup G) [N.Normal] [DiscreteTopology N] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hquot : Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hNH : N ⊓ H = ⊥) (hNK : N ⊓ K = ⊥) :
    Conjugate H K ↔ LocallyConjugate H K := by
  refine ⟨locallyConjugate_of_conjugate H K hH, fun hlocal => ?_⟩
  have hc := isComplement'_of_supplements_inf N H hHN hNH
  obtain ⟨n, hn⟩ := NonabelianComplement.local_inclusion_of_pronilpotent N H hc hN hH
    hpron K hK (pronilpotent_complement N K hN hK hKN hNK hquot)
    (locallyContains_of_locallyConjugate H K hlocal)
  have he := eq_of_supplements_le N H (conjugate (n : G) K)
    (supplements_conjugate N K hKN n) hNH hn
  refine ⟨(n : G)⁻¹, ?_⟩
  rw [← he, conjugate_inv_cancel]

end Topology
end LocalConjugacy
