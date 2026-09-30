module

public import LocalConjugacy.FiniteCoefficientSubgroup
public import LocalConjugacy.CocycleInvarianceSubgroup
public import LocalConjugacy.CoprimeRestriction

@[expose] public section

namespace LocalConjugacy

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [DiscreteTopology N] [MulDistribMulAction J N] [ContinuousSMul J N]

/-- The finite orbit argument applies in a finite invariant coefficient subgroup,
even when the whole coefficient group and the whole cohomology class are infinite. -/
theorem fixed_cocycle_of_locallyFinite
    (hfinite : LocallyFiniteGroup N)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) (hN : IsPGroup p N)
    {K : Subgroup J} [K.Normal] (hK : IsClosed (K : Set J))
    (Q : Subgroup J) (hcyclic : Procyclic Q) (hQ : IsProP q Q)
    (f : Cocycle (N := N) K) (hinv : InvariantUnder Q K f) :
    ∃ g : Cocycle (N := N) K, Cohomologous f g ∧
      ∀ x : Q, twistCocycle g x = g := by
  letI : Profinite K := profinite_closed_subgroup K hK
  obtain ⟨t, ht⟩ := hcyclic
  obtain ⟨n, hn⟩ := hinv t t.property
  obtain ⟨M, hMf, hMs, hMa⟩ := exists_finite_invariant_coefficient_subgroup
    (J := J) hfinite (Set.range f.toFun ∪ {n})
    ((isCompact_range f.continuous_toFun).finite_of_discrete.union (Set.finite_singleton n))
  letI : Finite M := hMf
  letI := coefficientSubgroupAction M hMa
  letI : ContinuousSMul J M := coefficientSubgroupContinuousSMul M hMa
  have hfM (x : K) : f.toFun x ∈ M := hMs (Or.inl ⟨x, rfl⟩)
  have hnM : n ∈ M := hMs (Or.inr rfl)
  let F := f.corestrictCoefficient M hMa hfM
  have hFt : Cohomologous F (twistCocycle F t) := by
    refine ⟨⟨n, hnM⟩, fun x => Subtype.ext ?_⟩
    exact hn x x.property (conjugateDomain K t x).property
  have hFi := invariantUnder_of_dense_generator Q t ht F hFt
  obtain ⟨g, hFg, hg⟩ := fixed_cocycle_of_finite_class hne
    (hN.to_subgroup M) Q hQ F hFi
  let G := g.mapCoefficient M.subtype continuous_subtype_val (fun _ _ => rfl)
  refine ⟨G, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hFg
    exact ⟨m.val, fun x => congrArg Subtype.val (hm x)⟩
  · intro x
    apply Cocycle.ext
    intro y
    exact congrArg (fun c : Cocycle (N := M) K => (c.toFun y).val) (hg x)

/-- Every fiber of prime-index restriction is detected in finite coefficients. -/
theorem restriction_injective_of_locallyFinite
    (hfinite : LocallyFiniteGroup N)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) (hN : IsPGroup p N)
    (K Q : Subgroup J) [K.Normal] (hQ : IsProP q Q) (hs : Supplements K Q)
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hr : Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g)) : Cohomologous f g := by
  letI : Profinite (⊤ : Subgroup J) := profinite_closed_subgroup ⊤ isClosed_univ
  obtain ⟨n, hn⟩ := hr
  obtain ⟨M, hMf, hMs, hMa⟩ := exists_finite_invariant_coefficient_subgroup
    (J := J) hfinite ((Set.range f.toFun ∪ Set.range g.toFun) ∪ {n})
    (((isCompact_range f.continuous_toFun).finite_of_discrete.union
      (isCompact_range g.continuous_toFun).finite_of_discrete).union (Set.finite_singleton n))
  letI : Finite M := hMf
  letI := coefficientSubgroupAction M hMa
  letI : ContinuousSMul J M := coefficientSubgroupContinuousSMul M hMa
  have hfM (x) : f.toFun x ∈ M := hMs (Or.inl (Or.inl ⟨x, rfl⟩))
  have hgM (x) : g.toFun x ∈ M := hMs (Or.inl (Or.inr ⟨x, rfl⟩))
  have hnM : n ∈ M := hMs (Or.inr rfl)
  let F := f.corestrictCoefficient M hMa hfM
  let G := g.corestrictCoefficient M hMa hgM
  have hrM : Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) F)
      (restrictCocycle le_top G) := ⟨⟨n, hnM⟩, fun x => Subtype.ext (hn x)⟩
  obtain ⟨m, hm⟩ := restriction_injective_of_coprime_supplement hne
    (hN.to_subgroup M) K Q hQ hs F G hrM
  exact ⟨m.val, fun x => congrArg Subtype.val (hm x)⟩

/-- Prime-index restriction for locally finite discrete coefficients. -/
theorem coprime_prime_index_restriction_locallyFinite
    (hfinite : LocallyFiniteGroup N)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) (hN : IsPGroup p N)
    (K : Subgroup J) [K.Normal] (hK : IsClosed (K : Set J)) (hi : K.index = q) :
    RestrictionIsomorphism (N := N) ⊤ K le_top := by
  obtain ⟨Q, hQ, hcyc, hpro, hs⟩ := exists_procyclic_supplement K hK hi
  constructor
  · intro f g hr
    exact restriction_injective_of_locallyFinite hfinite hne hN K Q hpro hs f g hr
  · intro f hf
    obtain ⟨g, hfg, hfix⟩ := fixed_cocycle_of_locallyFinite hfinite hne hN hK Q hcyc hpro f
      (fun j _ => hf j trivial)
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

section Statements
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

set_option linter.unusedVariables false in
/-- Proposition 2.1 for the manuscript's locally finite discrete coefficients. -/
theorem proposition_2_1 [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N)
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hN : IsPGroup p N) (J₀ Q : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hQ : IsClosed (Q : Set J))
    (hcyclic : Procyclic Q) (hpro : IsProP p₀ Q)
    (f : Cocycle (N := N) J₀) (hinv : InvariantUnder Q J₀ f) :
    ∃ g : Cocycle (N := N) J₀, Cohomologous f g ∧
      (∀ (q : J) (hq : q ∈ Q) (x : J) (hx : x ∈ J₀)
        (hqx : q⁻¹ * x * q ∈ J₀),
        q • g.toFun ⟨q⁻¹ * x * q, hqx⟩ = g.toFun ⟨x, hx⟩) ∧
      ∀ (q : J) (hq : q ∈ Q) (hq₀ : q ∈ J₀), g.toFun ⟨q, hq₀⟩ = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨g, hfg, hg⟩ := fixed_cocycle_of_locallyFinite hfinite hne hN hJ₀
    Q hcyclic hpro f hinv
  refine ⟨g, hfg, ?_, ?_⟩
  · intro q hq x hx hqx
    exact congrArg (fun f : Cocycle (N := N) J₀ => f.toFun ⟨x, hx⟩) (hg ⟨q, hq⟩)
  · exact fixed_cocycle_trivial_on_intersection (hp.coprime_iff_not_dvd.mpr
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hp₀).mp h).symm)) hN J₀ Q hcyclic hpro g hg

set_option linter.unusedVariables false in
/-- Proposition 2.2 for the manuscript's locally finite discrete coefficients. -/
theorem coprime_restriction_isomorphism [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N)
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
    RestrictionIsomorphism (N := N) ⊤ J₀ le_top := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact p₀.Prime := ⟨hp₀⟩
  exact coprime_prime_index_restriction_locallyFinite hfinite hne hN J₀ hJ₀ hindex

end Statements
end LocalConjugacy
