module

public import LocalConjugacy.PronilpotentRestriction
public import LocalConjugacy.CoprimeCohomology
public import LocalConjugacy.StableCocycles

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [Finite N] [MulDistribMulAction J N] [ContinuousSMul J N]

/-- A cocycle on the trivial subgroup is the distinguished cocycle. -/
theorem cohomologous_on_bot (f g : Cocycle (N := N) (⊥ : Subgroup J)) : Cohomologous f g := by
  refine ⟨1, fun x => ?_⟩
  have hx : x = 1 := Subsingleton.elim _ _
  rw [hx, cocycle_one, cocycle_one]
  simp

/-- Assemble the primary decomposition of a p-group of coefficients from
its Sylow restriction theorem and coprime cohomology vanishing. -/
theorem primaryDecomposition_pGroup_of_restriction
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    (hres : ∀ Q : Subgroup J, IsSylowPro p ⊤ Q →
      RestrictionIsomorphism (N := N) ⊤ Q le_top)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ q, IsSylowPro q.val.val ⊤ (P q)) :
    PrimaryDecomposition (N := N) P := by
  classical
  refine ⟨primary_restriction_is_stable P, ?_, ?_⟩
  · intro f g hr
    by_cases hp : ∃ U : OpenNormalSubgroup J, p ∣ Nat.card (J ⧸ U.toSubgroup)
    · let q : PrimeDivisor J := ⟨⟨p, Fact.out⟩, hp⟩
      exact (hres (P q) (hP q)).1 f g (hr q)
    · obtain ⟨Q, hQ⟩ := exists_sylowPro (G := J) p
      have hb : Q = ⊥ := sylowPro_eq_bot_of_not_primeDivisor Q hQ (not_exists.mp hp)
      apply (hres Q hQ).1 f g
      change Cohomologous (restrictCocycle (show Q ≤ ⊤ from le_top) f) (restrictCocycle le_top g)
      subst Q
      exact cohomologous_on_bot _ _
  · intro f hf
    by_cases hp : ∃ U : OpenNormalSubgroup J, p ∣ Nat.card (J ⧸ U.toSubgroup)
    · let q : PrimeDivisor J := ⟨⟨p, Fact.out⟩, hp⟩
      obtain ⟨g, hg⟩ := (hres (P q) (hP q)).2 (f q) (hf q)
      refine ⟨g, fun r => ?_⟩
      by_cases he : r.val.val = p
      · have hrq : r = q := by apply Subtype.ext; apply Subtype.ext; exact he
        subst r
        exact hg
      · letI : Fact r.val.val.Prime := ⟨r.val.property⟩
        have h0 := cohomologous_trivial_of_coprime_proP he hN (P r) (hP r).2.2.1 (f r)
        have h1 := cohomologous_trivial_of_coprime_proP he hN (P r) (hP r).2.2.1
          (restrictCocycle le_top g)
        exact cohomologous_trans h1 (cohomologous_symm h0)
    · refine ⟨trivialCocycle ⊤, fun r => ?_⟩
      have he : r.val.val ≠ p := by
        intro he
        exact hp (he ▸ r.property)
      letI : Fact r.val.val.Prime := ⟨r.val.property⟩
      exact cohomologous_symm
        (cohomologous_trivial_of_coprime_proP he hN (P r) (hP r).2.2.1 (f r))

/-- The full primary-decomposition assertion for a single finite primary
coefficient group and a pronilpotent acting group. -/
theorem primaryDecomposition_pGroup_of_pronilpotent
    {p : ℕ} [Fact p.Prime] (hJ : Pronilpotent J) (hN : IsPGroup p N)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ q, IsSylowPro q.val.val ⊤ (P q)) :
    PrimaryDecomposition (N := N) P :=
  primaryDecomposition_pGroup_of_restriction hN (pronilpotent_sylow_restriction hJ hN) P hP

end LocalConjugacy
