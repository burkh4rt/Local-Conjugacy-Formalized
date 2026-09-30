module

public import LocalConjugacy.SupersolvableCoefficients
public import LocalConjugacy.HallRestriction

@[expose] public section

/-! The numbered cohomology statements, expressed on the actual quotient `H¹`.
The representative-level arguments supply the proofs, without changing the
restriction maps or weakening surjectivity to separate local extension claims. -/

namespace LocalConjugacy

section QuotientMaps
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

theorem stableRestriction_bijective (K : Subgroup J)
    (h : RestrictionIsomorphism (N := N) ⊤ K le_top) :
    Function.Bijective (stableRestriction (N := N) K) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h f =>
      induction b using Quotient.inductionOn with
      | h g =>
        exact Quotient.sound (h.1 f g (Quotient.exact (congrArg Subtype.val hab)))
  · rintro ⟨a, f, rfl, hf⟩
    obtain ⟨g, hg⟩ := h.2 f hf
    exact ⟨Quotient.mk _ g, Subtype.ext (Quotient.sound hg)⟩

theorem primaryRestriction_bijective (P : PrimeDivisor J → Subgroup J)
    (h : PrimaryDecomposition (N := N) P) :
    Function.Bijective (primaryRestriction (N := N) P) := by
  classical
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h f =>
      induction b using Quotient.inductionOn with
      | h g =>
        apply Quotient.sound
        apply h.2.1 f g
        intro p
        exact Quotient.exact (congrArg Subtype.val (congrFun hab p))
  · intro a
    let f (p : PrimeDivisor J) := (a p).property.choose
    have hf (p : PrimeDivisor J) : InvariantUnder ⊤ (P p) (f p) :=
      (a p).property.choose_spec.2
    obtain ⟨g, hg⟩ := h.2.2 f hf
    refine ⟨Quotient.mk _ g, funext (fun p => Subtype.ext ?_)⟩
    exact (Quotient.sound (hg p)).trans (a p).property.choose_spec.1

end QuotientMaps

section Numbered
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- Lemma 1.2 (`lem:loc_conj`). For finite nilpotent coefficients, simultaneous
restriction bijects `H¹(J,N)` with the product of the stable Sylow classes.
The canonical restrictions preserve the distinguished class. -/
theorem lemma_1_2 [Profinite J] [DiscreteTopology N] [Finite N] [Group.IsNilpotent N]
    [ContinuousSMul J N]
    (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    Function.Bijective (primaryRestriction (N := N) P) ∧
      primaryRestriction (N := N) P default = default := by
  refine ⟨?_, primaryRestriction_distinguished P⟩
  letI : Profinite N := ⟨⟩
  exact primaryRestriction_bijective P
    (primary_decomposition (pronilpotent_iff_nilpotent.mpr inferInstance) hcase P hP)

/-- Proposition 2.2 (`prop:coprime_iso`), with possibly infinite locally finite
discrete coefficients and the actual restriction map on cohomology classes. -/
theorem proposition_2_2 [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N)
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
    Function.Bijective (stableRestriction (N := N) J₀) :=
  stableRestriction_bijective J₀
    (coprime_restriction_isomorphism hfinite p p₀ hp hp₀ hne hJ hN J₀ hJ₀ hindex)

end Numbered
end LocalConjugacy
