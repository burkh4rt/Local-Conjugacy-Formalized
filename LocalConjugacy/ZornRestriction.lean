module

public import LocalConjugacy.CocycleZorn
public import LocalConjugacy.LocallyFiniteCocycles

@[expose] public section

namespace LocalConjugacy

/-- A chosen Sylow subgroup remains Sylow in every intermediate subgroup. -/
theorem isSylowPro_of_intermediate {J : Type*} [Group J] [TopologicalSpace J]
    {p : ℕ} {H L P : Subgroup J} (hP : IsSylowPro p H P)
    (hPL : P ≤ L) (hLH : L ≤ H) : IsSylowPro p L P :=
  ⟨hPL, hP.2.1, hP.2.2.1,
    fun Q hQL hQclosed hQpro hPQ => hP.2.2.2 Q (hQL.trans hLH) hQclosed hQpro hPQ⟩

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- The Zorn counterexample in the exact stable-Sylow setting: the original
Sylow subgroup and ambient stability are retained when the acting group shrinks. -/
theorem exists_minimal_stable_surjectivity_counterexample
    {p : ℕ} (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (f : Cocycle (N := N) P) (hf : InvariantUnder ⊤ P f)
    (hbad : ¬ f.ExtendsTo ⊤) :
    ∃ L : Subgroup J, IsClosed (L : Set J) ∧ P < L ∧ IsSylowPro p L P ∧
      InvariantUnder L P f ∧ ¬ f.ExtendsTo L ∧
      ∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L → f.ExtendsTo K := by
  obtain ⟨L, hL, hPL, hbadL, hmin⟩ := exists_minimal_surjectivity_counterexample P f hbad
  exact ⟨L, hL, hPL, isSylowPro_of_intermediate hP hPL.le le_top,
    fun j _ => hf j trivial, hbadL, hmin⟩

/-- The last step in the Zorn proof of surjectivity: a lift to a normal
prime-index subgroup is ambient-invariant by the already proved injectivity,
and Proposition 2.2 then lifts it to the whole group. Full surjectivity on the
intermediate subgroup is not assumed. -/
theorem extend_stable_class_across_prime_index [IsTopologicalGroup N]
    (hfinite : LocallyFiniteGroup N)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) (hN : IsPGroup p N)
    (K P : Subgroup J) [K.Normal] [P.Normal] (hPK : P ≤ K)
    (hK : IsClosed (K : Set J)) (hindex : K.index = q)
    (hinj : ∀ f g : Cocycle (N := N) K,
      Cohomologous (restrictCocycle hPK f) (restrictCocycle hPK g) → Cohomologous f g)
    (f : Cocycle (N := N) P) (hf : InvariantUnder ⊤ P f)
    (hext : f.ExtendsTo K) : f.ExtendsTo ⊤ := by
  obtain ⟨_, g, hg⟩ := hext
  have hginv := invariant_lift_of_injective_restriction K P hPK hinj g f hf hg
  obtain ⟨F, hF⟩ := (coprime_prime_index_restriction_locallyFinite
    hfinite hne hN K hK hindex).2 g hginv
  refine ⟨le_top, F, ?_⟩
  have hFg : Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) F) g := hF
  have hgf : Cohomologous (restrictCocycle hPK g) f := hg
  exact cohomologous_trans (restrict_cohomologous hPK hFg) hgf

end LocalConjugacy
