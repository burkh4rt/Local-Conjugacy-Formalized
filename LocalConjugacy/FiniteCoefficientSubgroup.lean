module

public import LocalConjugacy.CocycleProducts

@[expose] public section

namespace LocalConjugacy

theorem locallyFiniteGroup_of_finite (G : Type*) [Group G] [Finite G] :
    LocallyFiniteGroup G := fun _ _ => Set.toFinite _

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [CompactSpace J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- A finite set of coefficients is contained in a finite invariant subgroup.
Compactness makes each orbit finite; local finiteness handles their generated subgroup. -/
theorem exists_finite_invariant_coefficient_subgroup (hN : LocallyFiniteGroup N)
    (s : Set N) (hs : s.Finite) :
    ∃ M : Subgroup N, Finite M ∧ s ⊆ M ∧
      ∀ (j : J) (n : N), n ∈ M → j • n ∈ M := by
  let t : Set N := ⋃ n ∈ s, Set.range (fun j : J => j • n)
  have ht : t.Finite := hs.biUnion fun n _ =>
    (isCompact_range (continuous_id.smul continuous_const)).finite_of_discrete
  let M := Subgroup.closure t
  refine ⟨M, (hN t ht).to_subtype, ?_, ?_⟩
  · intro n hn
    apply Subgroup.subset_closure
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn, ⟨1, one_smul J n⟩⟩⟩
  · intro j n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
        obtain ⟨has, k, rfl⟩ := Set.mem_iUnion.mp ha
        apply Subgroup.subset_closure
        exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨has,
          ⟨j * k, mul_smul j k a⟩⟩⟩
    | one => simpa only [smul_one] using M.one_mem
    | mul x y _ _ hx hy => simpa only [smul_mul'] using M.mul_mem hx hy
    | inv x _ hx => simpa only [smul_inv'] using M.inv_mem hx

end

section Subgroup
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N]
  [MulDistribMulAction J N]
  (M : Subgroup N) (hM : ∀ (j : J) (n : N), n ∈ M → j • n ∈ M)

@[instance_reducible] def coefficientSubgroupAction : MulDistribMulAction J M where
  smul j n := ⟨j • n.val, hM j n.val n.property⟩
  one_smul n := Subtype.ext (one_smul J n.val)
  mul_smul j k n := Subtype.ext (mul_smul j k n.val)
  smul_one j := Subtype.ext (smul_one j)
  smul_mul j n m := Subtype.ext (smul_mul' j n.val m.val)

theorem coefficientSubgroupContinuousSMul [ContinuousSMul J N] :
    letI := coefficientSubgroupAction M hM
    ContinuousSMul J M := by
  letI := coefficientSubgroupAction M hM
  exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

namespace Cocycle

def corestrictCoefficient {K : Subgroup J} (f : Cocycle (N := N) K)
    (hf : ∀ x, f.toFun x ∈ M) :
    letI := coefficientSubgroupAction M hM
    Cocycle (N := M) K := by
  letI := coefficientSubgroupAction M hM
  exact { toFun := fun x => ⟨f.toFun x, hf x⟩
          continuous_toFun := f.continuous_toFun.subtype_mk hf
          map_mul := fun x y => Subtype.ext (f.map_mul x y) }

end Cocycle
end Subgroup

end LocalConjugacy
