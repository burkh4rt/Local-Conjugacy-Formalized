module

public import LocalConjugacy.SupersolvableRestriction
public import LocalConjugacy.NilpotentCoefficients

@[expose] public section

namespace LocalConjugacy

/-- Lemma 1.2 in the prosupersolvable semidirect-product case. Each primary
coefficient subgroup inherits prosupersolvability by a continuous embedding. -/
theorem lemma_1_2_of_prosupersolvable
    {J N : Type*} [Group J] [Group N] [TopologicalSpace J] [Profinite J]
    [TopologicalSpace N] [DiscreteTopology N] [Finite N]
    [MulDistribMulAction J N] [ContinuousSMul J N]
    (hN : Pronilpotent N) (hG : Prosupersolvable (ActionProduct J N))
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    PrimaryDecomposition (N := N) P := by
  letI := pronilpotent_iff_nilpotent.mp hN
  letI (p : NilpotentCoefficients.PrimeIndex N) :=
    NilpotentCoefficients.factorAction (J := J) p
  have h (p : NilpotentCoefficients.PrimeIndex N) :
      PrimaryDecomposition (N := NilpotentCoefficients.Factor N p) P := by
    have hGp : Prosupersolvable (ActionProduct J (NilpotentCoefficients.Factor N p)) :=
      prosupersolvable_coefficient_embedding hG (NilpotentCoefficients.Factor N p).subtype
        Subtype.val_injective (fun _ _ => rfl)
    exact primaryDecomposition_pGroup_of_restriction
      (NilpotentCoefficients.primarySylow p).isPGroup'
      (supersolvable_sylow_restriction hGp (NilpotentCoefficients.primarySylow p).isPGroup') P hP
  let e := (NilpotentCoefficients.productEquiv (N := N)).symm
  apply primaryDecomposition_of_equiv P e continuous_of_discreteTopology
    continuous_of_discreteTopology _ (primaryDecomposition_pi P h)
  intro j n
  apply e.symm.injective
  change NilpotentCoefficients.productEquiv (e (j • n)) =
    NilpotentCoefficients.productEquiv (j • e n)
  rw [NilpotentCoefficients.productEquiv_smul]
  exact (e.symm_apply_apply (j • n)).trans
    (congrArg (fun x => j • x) (e.symm_apply_apply n).symm)

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- Lemma 1.2, including both branches of the manuscript's disjunction. -/
theorem primary_decomposition [Profinite J] [Profinite N] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] (hN : Pronilpotent N)
    (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    PrimaryDecomposition (N := N) P := by
  rcases hcase with hG | hJ
  · exact lemma_1_2_of_prosupersolvable hN hG P hP
  · exact lemma_1_2_of_pronilpotent hN hJ P hP

end LocalConjugacy
