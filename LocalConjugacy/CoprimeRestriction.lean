module

public import LocalConjugacy.CocycleExtension
public import LocalConjugacy.CocycleInjectivity

@[expose] public section

namespace LocalConjugacy

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [DiscreteTopology N] [Finite N] [MulDistribMulAction J N] [ContinuousSMul J N]

/-- The prime-index restriction theorem for finite coefficients. Solvability
of the ambient group is not needed for this step. -/
theorem coprime_prime_index_restriction
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) (hN : IsPGroup p N)
    (K : Subgroup J) [K.Normal] (hK : IsClosed (K : Set J)) (hi : K.index = q) :
    RestrictionIsomorphism (N := N) ⊤ K le_top := by
  obtain ⟨Q, hQ, hcyc, hpro, hs⟩ := exists_procyclic_supplement K hK hi
  constructor
  · intro f g hr
    exact restriction_injective_of_coprime_supplement hne hN K Q hpro hs f g hr
  · intro f hf
    have hfQ : InvariantUnder Q K f := fun j _ => hf j trivial
    obtain ⟨g, hfg, hfix⟩ := fixed_cocycle_of_finite_class hne hN Q hpro f hfQ
    have htriv := fixed_cocycle_trivial_on_intersection
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h => hne
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)).mp h).symm))
      hN K Q hcyc hpro g hfix
    obtain ⟨F, hF⟩ := extend_fixed_cocycle K Q hK hQ hs g hfix htriv
    refine ⟨F, ?_⟩
    change Cohomologous (restrictCocycle le_top F) f
    rw [hF]
    exact cohomologous_symm hfg
end

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

set_option linter.unusedVariables false in
/-- Proposition 2.2, with the requested finite discrete coefficient group. -/
theorem proposition_2_2_finite [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
    RestrictionIsomorphism (N := N) ⊤ J₀ le_top := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact p₀.Prime := ⟨hp₀⟩
  exact coprime_prime_index_restriction hne hN J₀ hJ₀ hindex
end

end LocalConjugacy
