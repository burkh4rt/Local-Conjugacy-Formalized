module

public import LocalConjugacy.FiniteSupplementConjugacy
public import LocalConjugacy.NormalIntersectionCompactness

@[expose] public section

namespace LocalConjugacy

theorem nilpotent_quotient_image_of_pronilpotent
    {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
    [IsTopologicalGroup F] [DiscreteTopology F]
    (N : Subgroup G) [N.Normal] (f : G →* F) (hf : Continuous f)
    (hs : Function.Surjective f) [(N.map f).Normal]
    (h : Pronilpotent (G ⧸ N)) : Group.IsNilpotent (F ⧸ N.map f) := by
  letI : DiscreteTopology (F ⧸ N.map f) :=
    QuotientGroup.discreteTopology_iff.mpr (isOpen_discrete _)
  let φ := QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N)
  apply nilpotent_of_pronilpotent_surjective h φ
  · apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact continuous_quotient_mk'.comp hf
  · intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (N.map f) y
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨QuotientGroup.mk' N x, rfl⟩

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- An alternative proof through finite ambient quotients and compactness.
The numbered results use the manuscript's finite-`N` induction and quotients
by `N ∩ U` in `FiniteKernelConjugacy` and `NormalIntersectionCompactness`. -/
theorem pronilpotent_supplement_conjugacy (N H K : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by
  refine ⟨locallyConjugate_of_conjugate H K hH, fun hlocal => ?_⟩
  apply conjugate_of_conjugate_finite_quotients H K hH hK
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  letI := nilpotent_map N hpron π continuous_quotient_mk'
  have hfinite : Supersolvable (G ⧸ U.toSubgroup) ∨
      Group.IsNilpotent ((G ⧸ U.toSubgroup) ⧸ N.map π) := by
    rcases hcase with h | h
    · exact Or.inl (h U)
    · exact Or.inr (nilpotent_quotient_image_of_pronilpotent N π continuous_quotient_mk'
        (QuotientGroup.mk'_surjective U.toSubgroup) h)
  exact (finite_nilpotent_supplement_conjugacy (N.map π) (H.map π) (K.map π) hfinite
    (supplements_map N H hHN π (QuotientGroup.mk'_surjective U.toSubgroup))
    (supplements_map N K hKN π (QuotientGroup.mk'_surjective U.toSubgroup))).mpr
    (locallyConjugate_map_finite H K hH hK hlocal π continuous_quotient_mk')

/-- An additional nilpotent case, retained from the finite-quotient proof.
The current Proposition 3.2 is in `FiniteKernelConjugacy`. -/
theorem nilpotent_supplement_conjugacy_via_finite_quotients
    (N H K : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K :=
  pronilpotent_supplement_conjugacy N H K hH hK hpron hcase hHN hKN

/-- An alternative finite-quotient proof, retained as a supporting result.
The manuscript proof of Theorem 1.1 is in `NormalIntersectionCompactness`. -/
theorem theorem_1_1_via_finite_quotients (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K :=
  pronilpotent_supplement_conjugacy N H K hH hK hpron hcase hHN hKN

end Profinite
end LocalConjugacy
