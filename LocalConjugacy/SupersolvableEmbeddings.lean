module

public import LocalConjugacy.SupersolvableHallAction

@[expose] public section

namespace LocalConjugacy

theorem prosupersolvable_of_continuous_injective {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [Profinite G] [TopologicalSpace H] [Profinite H]
    (hG : Prosupersolvable G) (f : H →* G) (hf : Continuous f) (hi : Function.Injective f) :
    Prosupersolvable H := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y he => hi (congrArg Subtype.val he), f.rangeRestrict_surjective⟩
  have he : Continuous e := hf.subtype_mk _
  have hei : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  intro V
  exact supersolvable_of_prosupersolvable_surjective (prosupersolvable_subgroup hG f.range)
    ((QuotientGroup.mk' V.toSubgroup).comp e.symm.toMonoidHom)
    (continuous_quotient_mk'.comp hei)
    ((QuotientGroup.mk'_surjective V.toSubgroup).comp e.symm.surjective)

section Action
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

theorem prosupersolvable_restricted_action (hG : Prosupersolvable (ActionProduct J N))
    (L : Subgroup J) (hL : IsClosed (L : Set J)) : Prosupersolvable (ActionProduct L N) := by
  letI := profinite_closed_subgroup L hL
  let f : ActionProduct L N →* ActionProduct J N :=
    SemidirectProduct.map (MonoidHom.id N) L.subtype (fun _ => rfl)
  apply prosupersolvable_of_continuous_injective hG f
  · apply continuous_induced_rng.mpr
    exact actionProduct_continuous_left.prodMk
      (continuous_subtype_val.comp actionProduct_continuous_right)
  · intro x y he
    apply SemidirectProduct.ext
    · exact congrArg (fun z : ActionProduct J N => z.left) he
    · exact Subtype.ext (congrArg (fun z : ActionProduct J N => z.right) he)

theorem prosupersolvable_coefficient_embedding {A : Type*} [Group A]
    [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [MulDistribMulAction J A] [ContinuousSMul J A]
    (hG : Prosupersolvable (ActionProduct J N)) (f : A →* N)
    (hi : Function.Injective f) (ha : ∀ (j : J) (a : A), f (j • a) = j • f a) :
    Prosupersolvable (ActionProduct J A) := by
  let φ : ActionProduct J A →* ActionProduct J N :=
    SemidirectProduct.map f (MonoidHom.id J) (fun j => MonoidHom.ext (ha j))
  apply prosupersolvable_of_continuous_injective hG φ
  · apply continuous_induced_rng.mpr
    exact (continuous_of_discreteTopology.comp actionProduct_continuous_left).prodMk
      actionProduct_continuous_right
  · intro x y he
    apply SemidirectProduct.ext
    · exact hi (congrArg (fun z : ActionProduct J N => z.left) he)
    · exact congrArg (fun z : ActionProduct J N => z.right) he

end Action
end LocalConjugacy
