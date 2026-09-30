module

public import LocalConjugacy.CoprimeRestriction
public import LocalConjugacy.CocycleRebase

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N]

theorem restrictionIsomorphism_refl (K : Subgroup J) :
    RestrictionIsomorphism (N := N) K K le_rfl := by
  constructor
  · intro f g h
    exact h
  · intro f _
    exact ⟨f, cohomologous_refl f⟩

/-- Composition of restriction isomorphisms, retaining stability under the
whole ambient group at the intermediate stage. -/
theorem restrictionIsomorphism_comp [IsTopologicalGroup J] [ContinuousSMul J N]
    (K P : Subgroup J) [K.Normal] [P.Normal] (hPK : P ≤ K)
    (hK : RestrictionIsomorphism (N := N) ⊤ K le_top)
    (hP : RestrictionIsomorphism (N := N) K P hPK) :
    RestrictionIsomorphism (N := N) ⊤ P le_top := by
  constructor
  · intro f g h
    apply hK.1 f g
    exact hP.1 (restrictCocycle le_top f) (restrictCocycle le_top g) h
  · intro g hg
    obtain ⟨f, hf, hfg⟩ := (invariant_restriction_isomorphism K P hPK hP).2 g hg
    obtain ⟨F, hF⟩ := hK.2 f hf
    refine ⟨F, ?_⟩
    change Cohomologous (restrictCocycle le_top F) f at hF
    change Cohomologous (restrictCocycle hPK f) g at hfg
    change Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) F) g
    exact cohomologous_trans (restrict_cohomologous hPK hF) hfg

end LocalConjugacy
