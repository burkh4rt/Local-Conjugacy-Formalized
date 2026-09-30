module

public import LocalConjugacy.ProP

@[expose] public section

namespace LocalConjugacy

/-- In a discrete group, the profinite condition reduces to the ordinary
torsion definition of a `p`-group. -/
theorem isProP_iff_isPGroup {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (p : ℕ) : IsProP p G ↔ IsPGroup p G :=
  ⟨fun h x => image_pow h (MonoidHom.id G) continuous_id x,
   proP_of_isPGroup⟩

/-- A finite Sylow criterion for the ambient-subgroup presentation. -/
theorem isSylowPro_of_index {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] {p : ℕ} [Fact p.Prime]
    (J P : Subgroup G) (hPJ : P ≤ J) (hP : IsPGroup p P)
    (hindex : ¬ p ∣ (P.subgroupOf J).index) : IsSylowPro p J P := by
  refine ⟨hPJ, isClosed_discrete _, proP_of_isPGroup hP, ?_⟩
  intro Q hQJ _ hQ hPQ
  have hPJp := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPJ).symm
  have hQp := (isProP_iff_isPGroup p).mp hQ
  have hQJp := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQJ).symm
  have heq : Q.subgroupOf J = P.subgroupOf J :=
    (hPJp.toSylow hindex).is_maximal' hQJp (fun _ hx => hPQ hx)
  apply le_antisymm _ hPQ
  intro x hx
  have hmem : (⟨x, hQJ hx⟩ : J) ∈ Q.subgroupOf J := hx
  rw [heq] at hmem
  exact hmem

theorem sylow_isSylowPro {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] {p : ℕ} (P : Sylow p G) : IsSylowPro p ⊤ P.toSubgroup := by
  refine ⟨le_top, isClosed_discrete _, proP_of_isPGroup P.isPGroup', ?_⟩
  intro Q _ _ hQ hPQ
  exact P.is_maximal' ((isProP_iff_isPGroup p).mp hQ) hPQ

theorem sylow_of_isSylowPro {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] {p : ℕ} (P : Subgroup G) (hP : IsSylowPro p ⊤ P) :
    ∃ S : Sylow p G, S.toSubgroup = P := by
  exact ⟨⟨P, (isProP_iff_isPGroup p).mp hP.2.2.1,
    fun hQ hPQ => hP.2.2.2 _ le_top (isClosed_discrete _) (proP_of_isPGroup hQ) hPQ⟩, rfl⟩

end LocalConjugacy
