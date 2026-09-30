module

public import LocalConjugacy.CocycleActions

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J]
  [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]
  {K : Subgroup J} [K.Normal]

/-- The stabilizer of the cohomology class under twisting. -/
def cocycleInvarianceSubgroup (f : Cocycle (N := N) K) : Subgroup J where
  carrier := {j | Cohomologous f (twistCocycle f j)}
  one_mem' := by
    change Cohomologous f (twistCocycle f 1)
    rw [twist_one]
    exact cohomologous_refl f
  mul_mem' := by
    intro a b ha hb
    change Cohomologous f (twistCocycle f (a * b))
    rw [twist_mul]
    exact cohomologous_trans ha (twist_cohomologous hb a)
  inv_mem' := by
    intro a ha
    have h := twist_cohomologous ha a⁻¹
    rw [← twist_mul, inv_mul_cancel, twist_one] at h
    exact cohomologous_symm h

/-- With finite coefficients, class invariance is closed in the acting group. -/
theorem cocycleInvarianceSubgroup_isClosed [Finite N] [T2Space N]
    (f : Cocycle (N := N) K) : IsClosed (cocycleInvarianceSubgroup f : Set J) := by
  have he : (cocycleInvarianceSubgroup f : Set J) =
      ⋃ n : N, ⋂ x : K,
        {j : J | j • f.toFun (conjugateDomain K j x) =
          n⁻¹ * f.toFun x * ((x : J) • n)} := by
    ext j
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [he]
  apply isClosed_iUnion_of_finite
  intro n
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  apply Continuous.smul continuous_id
  apply f.continuous_toFun.comp
  exact ((continuous_id.inv.mul continuous_const).mul continuous_id).subtype_mk _

/-- Invariance under a dense cyclic subgroup suffices for a finite coefficient group. -/
theorem invariantUnder_of_dense_generator [Finite N] [T2Space N]
    (Q : Subgroup J) (t : Q) (ht : Dense (Subgroup.zpowers t : Set Q))
    (f : Cocycle (N := N) K) (hf : Cohomologous f (twistCocycle f t)) :
    InvariantUnder Q K f := by
  let L := (cocycleInvarianceSubgroup f).comap Q.subtype
  have hL : IsClosed (L : Set Q) :=
    (cocycleInvarianceSubgroup_isClosed f).preimage continuous_subtype_val
  have hz : (Subgroup.zpowers t : Set Q) ⊆ L := Subgroup.zpowers_le.mpr hf
  have hall := closure_minimal hz hL
  rw [ht.closure_eq] at hall
  intro q hq
  have hq' : Cohomologous f (twistCocycle f q) := hall (Set.mem_univ (⟨q, hq⟩ : Q))
  obtain ⟨n, hn⟩ := hq'
  exact ⟨n, fun x hx _ => hn ⟨x, hx⟩⟩

end LocalConjugacy
