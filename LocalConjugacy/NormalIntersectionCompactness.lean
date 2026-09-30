module

public import LocalConjugacy.FiniteKernelConjugacy

@[expose] public section

/-! The precise compactness system in Theorem 1.1: the quotients are by
`N ∩ U`, and their normal subgroups have finite order, although the quotients
themselves need not be finite. -/

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

theorem finite_normal_intersection_image (N : Subgroup G) [N.Normal]
    (U : OpenNormalSubgroup G) :
    Finite (N.map (QuotientGroup.mk' (N ⊓ U.toSubgroup))) := by
  let D := N ⊓ U.toSubgroup
  let π := QuotientGroup.mk' D
  let ρ : G ⧸ D →* G ⧸ U.toSubgroup :=
    QuotientGroup.map D U.toSubgroup (MonoidHom.id G) inf_le_right
  let f : N.map π → G ⧸ U.toSubgroup := fun x => ρ x
  apply Finite.of_injective f
  rintro ⟨_, n, hn, rfl⟩ ⟨_, m, hm, rfl⟩ he
  apply Subtype.ext
  apply QuotientGroup.eq.mpr
  change QuotientGroup.mk' U.toSubgroup n = QuotientGroup.mk' U.toSubgroup m at he
  exact ⟨N.mul_mem (N.inv_mem hn) hm, QuotientGroup.eq.mp he⟩

/-- Compactness of the conjugating-element sets for `G/(N ∩ U)`. -/
theorem conjugate_of_normal_intersection_quotients (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hquot : ∀ U : OpenNormalSubgroup G,
      Conjugate (H.map (QuotientGroup.mk' (N ⊓ U.toSubgroup)))
        (K.map (QuotientGroup.mk' (N ⊓ U.toSubgroup)))) : Conjugate H K := by
  let : Nonempty (OpenNormalSubgroup G) := ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩
  apply conjugate_of_closed_approximations H K
    (fun U : OpenNormalSubgroup G => H ⊔ (N ⊓ U.toSubgroup))
    (fun U : OpenNormalSubgroup G => K ⊔ (N ⊓ U.toSubgroup))
  · intro U
    rw [sup_comm]
    exact closed_sup_normal _ H (hN.inter U.isClosed) hH
  · intro U
    rw [sup_comm]
    exact closed_sup_normal _ K (hN.inter U.isClosed) hK
  · intro x hx
    exact mem_of_mem_sup_openNormal H hH x
      (fun U => (sup_le_sup_left inf_le_right H) (hx U))
  · intro x hx
    exact mem_of_mem_sup_openNormal K hK x
      (fun U => (sup_le_sup_left inf_le_right K) (hx U))
  · intro U V
    exact ⟨U ⊓ V, sup_le_sup_left (inf_le_inf_left N inf_le_left) H,
      sup_le_sup_left (inf_le_inf_left N inf_le_right) H,
      sup_le_sup_left (inf_le_inf_left N inf_le_left) K,
      sup_le_sup_left (inf_le_inf_left N inf_le_right) K⟩
  · intro U
    let D := N ⊓ U.toSubgroup
    let π := QuotientGroup.mk' D
    obtain ⟨q, hq⟩ := hquot U
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
    have hmem (L : Subgroup G) (x : G) : π x ∈ L.map π ↔ x ∈ L ⊔ D := by
      change x ∈ (L.map π).comap π ↔ _
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    refine ⟨g, ?_, ?_⟩
    · intro x hx
      apply (hmem K _).mp
      rw [← hq]
      exact Subgroup.mem_map.mpr ⟨π x, Subgroup.mem_map_of_mem π hx, by
        simp [π, MulAut.conj_apply]⟩
    · intro y hy
      apply (hmem H _).mp
      have hyq : π y ∈ K.map π := Subgroup.mem_map_of_mem π hy
      rw [← hq] at hyq
      obtain ⟨z, hz, he⟩ := hyq
      have he' : π g * z * (π g)⁻¹ = π y := he
      have hz' : π (g⁻¹ * y * (g⁻¹)⁻¹) = z := by
        simp only [map_mul, map_inv, inv_inv]
        rw [← he']
        group
      rwa [hz']

/-- Theorem 1.1 (`thm:loc_conj`), using Proposition 3.2 in each quotient by
`N ∩ U`, followed by the manuscript's compactness argument. -/
theorem theorem_1_1 (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by
  refine ⟨locallyConjugate_of_conjugate H K hH, fun hlocal => ?_⟩
  apply conjugate_of_normal_intersection_quotients N H K hN hH hK
  intro U
  let D := N ⊓ U.toSubgroup
  letI := profinite_quotient D (hN.inter U.isClosed)
  let π := QuotientGroup.mk' D
  letI : Finite (N.map π) := finite_normal_intersection_image N U
  exact (proposition_3_2 (N.map π) (H.map π) (K.map π)
    (hN.isCompact.image continuous_quotient_mk').isClosed
    (hH.isCompact.image continuous_quotient_mk').isClosed
    (hK.isCompact.image continuous_quotient_mk').isClosed
    (pronilpotent_subgroup_image N hpron π continuous_quotient_mk')
    (profinite_conjugacy_case_map N π continuous_quotient_mk'
      (QuotientGroup.mk'_surjective D) hcase)
    (supplements_map N H hHN π (QuotientGroup.mk'_surjective D))
    (supplements_map N K hKN π (QuotientGroup.mk'_surjective D))).mpr
      (locallyConjugate_map H K hH hK hlocal π continuous_quotient_mk')

end LocalConjugacy
