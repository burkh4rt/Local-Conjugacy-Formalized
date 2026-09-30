module

public import LocalConjugacy.StableCocycles
public import LocalConjugacy.ProfiniteSylow

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N] [Finite N]

/-- A finite collection of continuous cocycles and the action are simultaneously
trivial on some open normal subgroup. This is the finite-quotient step needed
before using induction on finite group orders. -/
theorem exists_cocycle_openNormal {ι : Type*} [Finite ι]
    (f : ι → Cocycle (N := N) (⊤ : Subgroup J)) :
    ∃ U : OpenNormalSubgroup J,
      (∀ u ∈ U, ∀ n : N, u • n = n) ∧
      ∀ i u, u ∈ U → (f i).toFun ⟨u, trivial⟩ = 1 := by
  let A : Set J := ⋂ n : N, {j : J | j • n = n}
  let B : Set J := ⋂ i : ι, {j : J | (f i).toFun ⟨j, trivial⟩ = 1}
  have hA : IsOpen A := isOpen_iInter_of_finite fun n =>
    (continuous_id.smul continuous_const).isOpen_preimage {n} (isOpen_discrete _)
  have hB : IsOpen B := isOpen_iInter_of_finite fun i =>
    ((f i).continuous_toFun.comp (continuous_id.subtype_mk _)).isOpen_preimage {1}
      (isOpen_discrete _)
  have h1 : (1 : J) ∈ A ∩ B := by
    constructor
    · simp [A]
    · simp only [B, Set.mem_iInter, Set.mem_setOf_eq]
      exact fun i => cocycle_one (f i)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hA.inter hB) h1
  refine ⟨U, ?_, ?_⟩
  · intro u hu n
    exact Set.mem_iInter.mp (hU hu).1 n
  · intro i u hu
    exact Set.mem_iInter.mp (hU hu).2 i

/-- The factorization records the quotient action explicitly, so it does not
silently replace the coefficient action when passing to a finite quotient. -/
theorem cocycles_factor_through_finite_quotient {ι : Type*} [Finite ι]
    (f : ι → Cocycle (N := N) (⊤ : Subgroup J)) :
    ∃ (U : OpenNormalSubgroup J) (a : (J ⧸ U.toSubgroup) →* MulAut N)
      (c : ι → (J ⧸ U.toSubgroup) → N),
      (∀ j, a (QuotientGroup.mk' U.toSubgroup j) = MulDistribMulAction.toMulAut J N j) ∧
      (∀ i j, c i (QuotientGroup.mk' U.toSubgroup j) = (f i).toFun ⟨j, trivial⟩) ∧
      ∀ i, CocycleFn a (c i) := by
  obtain ⟨U, ha, hf⟩ := exists_cocycle_openNormal f
  let α := MulDistribMulAction.toMulAut J N
  have hk : U.toSubgroup ≤ α.ker := by
    intro u hu
    apply MulEquiv.ext
    exact ha u hu
  let a := QuotientGroup.lift U.toSubgroup α hk
  let c : ι → (J ⧸ U.toSubgroup) → N := fun i =>
    Quotient.lift (fun j : J => (f i).toFun ⟨j, trivial⟩) (by
      intro j k hjk
      have he : (⟨j, trivial⟩ : (⊤ : Subgroup J)) * ⟨j⁻¹ * k, trivial⟩ = ⟨k, trivial⟩ := by
        apply Subtype.ext
        simp
      have hmul := (f i).map_mul ⟨j, trivial⟩ ⟨j⁻¹ * k, trivial⟩
      rw [he, hf i (j⁻¹ * k) (QuotientGroup.leftRel_apply.mp hjk), smul_one, mul_one] at hmul
      exact hmul.symm)
  refine ⟨U, a, c, fun _ => rfl, fun _ _ => rfl, ?_⟩
  intro i x y
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup y
  exact (f i).map_mul ⟨j, trivial⟩ ⟨k, trivial⟩

/-- With the quotient action fixed, inflation neither creates nor destroys
cohomology between representatives. -/
theorem cohomologousFn_quotient_iff (U : OpenNormalSubgroup J)
    (a : (J ⧸ U.toSubgroup) →* MulAut N)
    (ha : ∀ j, a (QuotientGroup.mk' U.toSubgroup j) = MulDistribMulAction.toMulAut J N j)
    (f g : (J ⧸ U.toSubgroup) → N) :
    CohomologousFn a f g ↔
      CohomologousFn (MulDistribMulAction.toMulAut J N)
        (f ∘ QuotientGroup.mk' U.toSubgroup) (g ∘ QuotientGroup.mk' U.toSubgroup) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun j => ?_⟩
    simpa only [Function.comp_apply, ha] using hn (QuotientGroup.mk' U.toSubgroup j)
  · rintro ⟨n, hn⟩
    refine ⟨n, fun x => ?_⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup x
    simpa only [Function.comp_apply, ha] using hn j

end LocalConjugacy
