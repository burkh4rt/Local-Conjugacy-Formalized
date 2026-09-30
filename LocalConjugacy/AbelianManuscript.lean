module

public import LocalConjugacy.AbelianFiniteKernel

@[expose] public section

/-! Proposition 4.1 in the order of the manuscript: induction for finite `N`,
then compactness in the quotients by `N ∩ U`. -/

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- The inclusion form of the manuscript's normal-intersection compactness
argument. The quotients need not be finite. -/
theorem conjugate_le_of_normal_intersection_quotients
    (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hquot : ∀ U : OpenNormalSubgroup G, ∃ q : G ⧸ (N ⊓ U.toSubgroup),
      conjugate q (K.map (QuotientGroup.mk' (N ⊓ U.toSubgroup))) ≤
        H.map (QuotientGroup.mk' (N ⊓ U.toSubgroup))) :
    ∃ g : G, conjugate g K ≤ H := by
  let : Nonempty (OpenNormalSubgroup G) := ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩
  let T : OpenNormalSubgroup G → Set G := fun U => transporter K (H ⊔ (N ⊓ U.toSubgroup))
  have hc : ∀ U, IsClosed (T U) := by
    intro U
    apply transporter_closed
    rw [sup_comm]
    exact closed_sup_normal _ H (hN.inter U.isClosed) hH
  have hd : Directed (· ⊇ ·) T := by
    intro U V
    refine ⟨U ⊓ V, ?_, ?_⟩
    · intro g hg x hx
      exact (sup_le_sup_left (inf_le_inf_left N inf_le_left) H) (hg x hx)
    · intro g hg x hx
      exact (sup_le_sup_left (inf_le_inf_left N inf_le_right) H) (hg x hx)
  have hn : ∀ U, (T U).Nonempty := by
    intro U
    let D := N ⊓ U.toSubgroup
    let π := QuotientGroup.mk' D
    obtain ⟨q, hq⟩ := hquot U
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
    refine ⟨g, fun x hx => ?_⟩
    change (K.map π).map (MulAut.conj (π g)).toMonoidHom ≤ H.map π at hq
    have hm := hq (Subgroup.mem_map_of_mem (MulAut.conj (π g)).toMonoidHom
      (Subgroup.mem_map_of_mem π hx))
    change π g * π x * (π g)⁻¹ ∈ H.map π at hm
    have he : π (g * x * g⁻¹) ∈ H.map π := by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using hm
    change g * x * g⁻¹ ∈ (H.map π).comap π at he
    simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using he
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hd hn (fun U => (hc U).isCompact) hc
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact mem_of_mem_sup_openNormal H hH _ (fun U =>
    (sup_le_sup_left inf_le_right H) ((Set.mem_iInter.mp hg U) x hx))

/-- Proposition 4.1, `thm:loc_inclusion_ab`. -/
theorem proposition_4_1 (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hcomm : ∀ n m : N, n * m = m * n)
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  apply conjugate_le_of_normal_intersection_quotients N H K hN hH
  intro U
  let D := N ⊓ U.toSubgroup
  letI := profinite_quotient D (hN.inter U.isClosed)
  let π := QuotientGroup.mk' D
  letI : Finite (N.map π) := finite_normal_intersection_image N U
  exact abelian_inclusion_finite_kernel (N.map π) (H.map π) (K.map π)
    (hN.isCompact.image continuous_quotient_mk').isClosed
    (hH.isCompact.image continuous_quotient_mk').isClosed
    (hK.isCompact.image continuous_quotient_mk').isClosed
    (commutative_map N hcomm π)
    (supplements_map N H hHN π (QuotientGroup.mk'_surjective D))
    (supplements_map N K hKN π (QuotientGroup.mk'_surjective D))
    (locallyContains_map H K hK hlocal π continuous_quotient_mk')

end LocalConjugacy
