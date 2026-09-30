module

public import LocalConjugacy.AbelianComplement
public import LocalConjugacy.Supplements

@[expose] public section

namespace LocalConjugacy

theorem finite_abelian_local_inclusion {G : Type*} [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (N H K : Subgroup G) [N.Normal]
    (hcomm : ∀ n m : N, n * m = m * n) (hsup : Supplements N H)
    (hloc : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  letI : Profinite G := ⟨⟩
  have hsup' := sup_eq_top_of_supplements N H hsup
  letI := inf_normal_of_stabNormal N H hsup' (intersectionNormal_of_commutative N H hcomm)
  let π := QuotientGroup.mk' (N ⊓ H)
  have hc : Subgroup.IsComplement' (N.map π) (H.map π) := isComplement'_map_mk' N H hsup'
  obtain ⟨q, hq⟩ := AbelianComplement.finite_local_inclusion (N.map π) (H.map π) hc
    (commutative_map N hcomm π) (K.map π)
    (locallyContains_map_finite H K (isClosed_discrete _) hloc π continuous_quotient_mk')
  exact conjugate_le_of_quotient (N ⊓ H) H K inf_le_right q hq

/-- The abelian local-inclusion theorem, obtained from the finite result
by closed transporters and compactness. The contained subgroup need not
itself supplement `N`. -/
theorem abelian_local_inclusion {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal] (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hcomm : ∀ n m : N, n * m = m * n)
    (hsup : Supplements N H) (hloc : LocallyContains H K) :
    ∃ g : G, conjugate g K ≤ H := by
  apply conjugate_le_of_finite_quotient_inclusions K H hH
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  exact finite_abelian_local_inclusion (N.map π) (H.map π) (K.map π)
    (commutative_map N hcomm π) (supplements_map N H hsup π (QuotientGroup.mk'_surjective _))
    (locallyContains_map_finite H K hK hloc π continuous_quotient_mk')

/-- An alternative proof of Proposition 4.1 through finite ambient quotients.
The manuscript's finite-normal-subgroup proof is in `AbelianManuscript`. -/
theorem proposition_4_1_via_finite_quotients {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hcomm : ∀ n m : N, n * m = m * n)
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H :=
  abelian_local_inclusion N H K hH hK hcomm hHN hlocal

end LocalConjugacy
