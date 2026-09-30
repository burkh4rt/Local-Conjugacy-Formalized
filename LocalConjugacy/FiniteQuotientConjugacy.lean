module

public import LocalConjugacy.Compactness

@[expose] public section

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Closed subgroups are separated by their images in finite continuous
quotients. This supplies the separation step of the compactness argument. -/
theorem mem_of_mem_sup_openNormal (H : Subgroup G) (hH : IsClosed (H : Set G))
    (x : G) (hx : ∀ U : OpenNormalSubgroup G, x ∈ H ⊔ U.toSubgroup) : x ∈ H := by
  let HC : ClosedSubgroup G := { toSubgroup := H, isClosed' := hH }
  change x ∈ HC.toSubgroup
  rw [ProfiniteGrp.closedSubgroup_eq_sInf_open HC]
  apply Subgroup.mem_sInf.mpr
  intro V hV
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hV.1 V.one_mem
  exact (sup_le hV.2 hU) (hx U)

/-- Conjugacy can be tested in all continuous finite quotients. This is a
proved general compactness reduction, without the paper's local-conjugacy
or pronilpotence assumptions. It does not assert the finite conjugacy theorem. -/
theorem conjugate_of_conjugate_finite_quotients (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hquot : ∀ U : OpenNormalSubgroup G,
      Conjugate (H.map (QuotientGroup.mk' U.toSubgroup))
        (K.map (QuotientGroup.mk' U.toSubgroup))) : Conjugate H K := by
  let : Nonempty (OpenNormalSubgroup G) := ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩
  apply conjugate_of_closed_approximations H K
    (fun U : OpenNormalSubgroup G => H ⊔ U.toSubgroup)
    (fun U : OpenNormalSubgroup G => K ⊔ U.toSubgroup)
  · intro U
    exact Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right U.isOpen)
  · intro U
    exact Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right U.isOpen)
  · exact mem_of_mem_sup_openNormal H hH
  · exact mem_of_mem_sup_openNormal K hK
  · intro U V
    exact ⟨U ⊓ V, sup_le_sup_left inf_le_left H, sup_le_sup_left inf_le_right H,
      sup_le_sup_left inf_le_left K, sup_le_sup_left inf_le_right K⟩
  · intro U
    let π := QuotientGroup.mk' U.toSubgroup
    obtain ⟨q, hq⟩ := hquot U
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup q
    have hmem (L : Subgroup G) (x : G) : π x ∈ L.map π ↔ x ∈ L ⊔ U.toSubgroup := by
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

/-- The inclusion version of the compactness reduction. -/
theorem conjugate_le_of_finite_quotient_inclusions (H K : Subgroup G)
    (hK : IsClosed (K : Set G))
    (hquot : ∀ U : OpenNormalSubgroup G, ∃ q : G ⧸ U.toSubgroup,
      conjugate q (H.map (QuotientGroup.mk' U.toSubgroup)) ≤
        K.map (QuotientGroup.mk' U.toSubgroup)) : ∃ g : G, conjugate g H ≤ K := by
  let : Nonempty (OpenNormalSubgroup G) := ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩
  let T : OpenNormalSubgroup G → Set G := fun U => transporter H (K ⊔ U.toSubgroup)
  have hc : ∀ U, IsClosed (T U) := fun U => transporter_closed _ _
    (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right U.isOpen))
  have hd : Directed (· ⊇ ·) T := by
    intro U V
    refine ⟨U ⊓ V, ?_, ?_⟩
    · intro g hg x hx
      exact (sup_le_sup_left inf_le_left K) (hg x hx)
    · intro g hg x hx
      exact (sup_le_sup_left inf_le_right K) (hg x hx)
  have hn : ∀ U, (T U).Nonempty := by
    intro U
    let π := QuotientGroup.mk' U.toSubgroup
    obtain ⟨q, hq⟩ := hquot U
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup q
    refine ⟨g, fun x hx => ?_⟩
    change (H.map π).map (MulAut.conj (π g)).toMonoidHom ≤ K.map π at hq
    have hm := hq (Subgroup.mem_map_of_mem (MulAut.conj (π g)).toMonoidHom
      (Subgroup.mem_map_of_mem π hx))
    change π g * π x * (π g)⁻¹ ∈ K.map π at hm
    have he : π (g * x * g⁻¹) ∈ K.map π := by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using hm
    change g * x * g⁻¹ ∈ (K.map π).comap π at he
    simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using he
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hd hn (fun U => (hc U).isCompact) hc
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact mem_of_mem_sup_openNormal K hK _ (fun U => (Set.mem_iInter.mp hg U) x hx)

end LocalConjugacy
