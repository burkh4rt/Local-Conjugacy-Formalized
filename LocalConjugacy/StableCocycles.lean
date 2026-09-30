module

public import LocalConjugacy.CocycleActions

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- Stable classes are independent of the representative, including when
the subgroup is not normal in the ambient group. -/
theorem invariant_cohomologous {L K : Subgroup J}
    {f g : Cocycle (N := N) K} (hf : InvariantUnder L K f)
    (hfg : Cohomologous f g) : InvariantUnder L K g := by
  obtain ⟨a, ha⟩ := hfg
  intro j hj
  obtain ⟨n, hn⟩ := hf j hj
  refine ⟨a⁻¹ * n * (j • a), fun x hx hjx => ?_⟩
  rw [ha, ha]
  simp only [smul_mul', smul_inv', smul_smul]
  rw [hn x hx hjx]
  have he : j * (j⁻¹ * x * j) = x * j := by group
  simp only [Subgroup.coe_mk, he, smul_mul', smul_inv', smul_smul, mul_inv_rev, inv_inv]
  group

/-- The first clause of primary decomposition requires no finiteness,
nilpotence, or solvability assumption. -/
theorem primary_restriction_is_stable (P : PrimeDivisor J → Subgroup J)
    (f : Cocycle (N := N) (⊤ : Subgroup J)) (p : PrimeDivisor J) :
    InvariantUnder ⊤ (P p) (restrictCocycle le_top f) :=
  invariant_restriction (P p) f

end LocalConjugacy
