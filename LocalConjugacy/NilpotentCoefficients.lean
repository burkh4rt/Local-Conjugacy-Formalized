module

/-
The productEquiv construction adapts Mathlib/GroupTheory/Sylow.lean.
Copyright (c) 2018 Chris Hughes. Authors: Chris Hughes, Thomas Browning.
Used and adapted under the Apache-2.0 license; see LICENSE.
-/
public import LocalConjugacy.PrimaryPGroup
public import LocalConjugacy.CocycleProducts
public import LocalConjugacy.StructuralImages

@[expose] public section

namespace LocalConjugacy
namespace NilpotentCoefficients

variable {N : Type*} [Group N] [Finite N] [Group.IsNilpotent N]

abbrev PrimeIndex (N : Type*) := {p : ℕ // p ∈ (Nat.card N).primeFactors}

instance primeFact (p : PrimeIndex N) : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩

noncomputable def primarySylow (p : PrimeIndex N) : Sylow p.val N := default

noncomputable abbrev Factor (N : Type*) [Group N] (p : PrimeIndex N) :=
  (primarySylow p).toSubgroup

instance factorCharacteristic (p : PrimeIndex N) : (Factor N p).Characteristic :=
  Sylow.characteristic_of_normal (primarySylow p) inferInstance

theorem factors_commute : Pairwise fun p q : PrimeIndex N =>
    ∀ x y : N, x ∈ Factor N p → y ∈ Factor N q → Commute x y := by
  intro p q hpq
  apply Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance
  exact IsPGroup.disjoint_of_ne p.val q.val (fun he => hpq (Subtype.ext he)) _ _
    (primarySylow p).isPGroup' (primarySylow q).isPGroup'

/-- The finite nilpotent coefficient group is the product of its primary
subgroups. This follows Mathlib's `Sylow.directProductOfNormal` construction,
with one chosen Sylow per prime so the component action is explicit. -/
noncomputable def productEquiv : (∀ p : PrimeIndex N, Factor N p) ≃* N := by
  classical
  let φ := Subgroup.noncommPiCoprod (factors_commute (N := N))
  apply MulEquiv.ofBijective φ
  letI := Fintype.ofFinite N
  letI (p : PrimeIndex N) := Fintype.ofFinite (Factor N p)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order factors_commute
    intro p q hpq
    simpa only [Nat.card_eq_fintype_card] using IsPGroup.coprime_card_of_ne p.val q.val (fun he => hpq (Subtype.ext he)) _ _
      (primarySylow p).isPGroup' (primarySylow q).isPGroup'
  · simp only [← Nat.card_eq_fintype_card]
    calc
      Nat.card (∀ p : PrimeIndex N, Factor N p) = ∏ p : PrimeIndex N, Nat.card (Factor N p) := Nat.card_pi
      _ = ∏ p : PrimeIndex N, p.val ^ (Nat.card N).factorization p.val := by
        congr 1 with p
        exact (primarySylow p).card_eq_multiplicity
      _ = ∏ p ∈ (Nat.card N).primeFactors, p ^ (Nat.card N).factorization p :=
        Finset.prod_finset_coe (fun p : ℕ => p ^ (Nat.card N).factorization p) (Nat.card N).primeFactors
      _ = (Nat.card N).factorization.prod (· ^ ·) := rfl
      _ = Nat.card N := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

variable {J : Type*} [Group J] [MulDistribMulAction J N]

@[instance_reducible] noncomputable def factorAction (p : PrimeIndex N) :
    MulDistribMulAction J (Factor N p) :=
  MulDistribMulAction.compHom (Factor N p)
    ((MulAut.characteristic (Factor N p)).comp (MulDistribMulAction.toMulAut J N))

attribute [local instance] factorAction

set_option backward.isDefEq.respectTransparency false in
theorem productEquiv_smul (j : J) (x : ∀ p : PrimeIndex N, Factor N p) :
    productEquiv (j • x) = j • productEquiv x := by
  classical
  change Subgroup.noncommPiCoprod factors_commute (j • x) =
    (MulDistribMulAction.toMulAut J N j) (Subgroup.noncommPiCoprod factors_commute x)
  simp only [Subgroup.noncommPiCoprod_apply]
  exact (Finset.map_noncommProd Finset.univ (fun i : PrimeIndex N => (x i : N))
    (fun i _ k _ hik => factors_commute hik _ _ (x i).property (x k).property)
    (MulDistribMulAction.toMulAut J N j)).symm

variable [TopologicalSpace J] [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul J N]

instance factorContinuousSMul (p : PrimeIndex N) : ContinuousSMul J (Factor N p) where
  continuous_smul := ((continuous_fst : Continuous (Prod.fst : J × Factor N p → J)).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

end NilpotentCoefficients

/-- Lemma 1.2 in the pronilpotent-acting-group case, with finite nilpotent
coefficients. This includes the product over all primes of the ambient group,
not only the prime divisors of the coefficient order. -/
theorem lemma_1_2_of_pronilpotent
    {J N : Type*} [Group J] [Group N] [TopologicalSpace J] [Profinite J]
    [TopologicalSpace N] [DiscreteTopology N] [Finite N]
    [MulDistribMulAction J N] [ContinuousSMul J N]
    (hN : Pronilpotent N) (hJ : Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    PrimaryDecomposition (N := N) P := by
  letI := pronilpotent_iff_nilpotent.mp hN
  letI (p : NilpotentCoefficients.PrimeIndex N) :=
    NilpotentCoefficients.factorAction (J := J) p
  have h (p : NilpotentCoefficients.PrimeIndex N) :
      PrimaryDecomposition (N := NilpotentCoefficients.Factor N p) P :=
    primaryDecomposition_pGroup_of_pronilpotent hJ
      (NilpotentCoefficients.primarySylow p).isPGroup' P hP
  let e := (NilpotentCoefficients.productEquiv (N := N)).symm
  apply primaryDecomposition_of_equiv P e continuous_of_discreteTopology
    continuous_of_discreteTopology _ (primaryDecomposition_pi P h)
  intro j n
  apply e.symm.injective
  change NilpotentCoefficients.productEquiv (e (j • n)) =
    NilpotentCoefficients.productEquiv (j • e n)
  rw [NilpotentCoefficients.productEquiv_smul]
  exact (e.symm_apply_apply (j • n)).trans (congrArg (fun x => j • x) (e.symm_apply_apply n).symm)

end LocalConjugacy
