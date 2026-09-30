module

public import LocalConjugacy.CocycleActions

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N]

/-- The affine action attached to a nonabelian cocycle. -/
@[instance_reducible] def cocycleAffineAction {K : Subgroup J}
    (f : Cocycle (N := N) K) : MulAction K N where
  smul x n := f.toFun x * ((x : J) • n)
  one_smul n := by
    change f.toFun 1 * (((1 : K) : J) • n) = n
    simp only [cocycle_one, Subgroup.coe_one, one_smul, one_mul]
  mul_smul x y n := by
    change f.toFun (x * y) * (((x * y : K) : J) • n) =
      f.toFun x * ((x : J) • (f.toFun y * ((y : J) • n)))
    simp only [f.map_mul, Subgroup.coe_mul, mul_smul, smul_mul', mul_assoc]

/-- The coprime vanishing fact used in the finite-coefficient case of
Proposition 2.2 and Lemma 1.2. The acting pro-`q` group may be infinite. -/
theorem cohomologous_trivial_of_coprime_proP
    [IsTopologicalGroup J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] [Finite N] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hne : q ≠ p) (hN : IsPGroup p N) (K : Subgroup J) (hK : IsProP q K)
    (f : Cocycle (N := N) K) : Cohomologous f (trivialCocycle K) := by
  letI := cocycleAffineAction f
  have hc (n : N) : IsClosed (MulAction.stabilizer K n : Set K) := by
    change IsClosed {x : K | f.toFun x * ((x : J) • n) = n}
    exact isClosed_eq (f.continuous_toFun.mul
      (continuous_subtype_val.smul continuous_const)) continuous_const
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hn : ¬ q ∣ Nat.card N := by
    rw [hk]
    exact fun h => hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : p.Prime)).mp ((Fact.out : q.Prime).dvd_of_dvd_pow h))
  obtain ⟨n, hn⟩ := proP_fixed_point hK hc hn
  refine ⟨n, fun x => ?_⟩
  change 1 = n⁻¹ * f.toFun x * ((x : J) • n)
  have he : f.toFun x * ((x : J) • n) = n := hn x
  rw [mul_assoc, he, inv_mul_cancel]

end LocalConjugacy
