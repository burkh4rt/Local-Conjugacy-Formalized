module

public import LocalConjugacy.Definitions

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- The declared semidirect-product topology is the ordinary product topology. -/
def actionProductHomeomorph : ActionProduct J N ≃ₜ N × J where
  toEquiv := SemidirectProduct.equivProd
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

theorem actionProduct_continuous_left : Continuous (fun x : ActionProduct J N => x.left) :=
  continuous_fst.comp actionProductHomeomorph.continuous_toFun

theorem actionProduct_continuous_right : Continuous (fun x : ActionProduct J N => x.right) :=
  continuous_snd.comp actionProductHomeomorph.continuous_toFun

theorem actionProduct_continuous_inl :
    Continuous (SemidirectProduct.inl : N →* ActionProduct J N) :=
  continuous_induced_rng.mpr (continuous_id.prodMk continuous_const)

theorem actionProduct_continuous_inr :
    Continuous (SemidirectProduct.inr : J →* ActionProduct J N) :=
  continuous_induced_rng.mpr (continuous_const.prodMk continuous_id)

instance actionProduct_topologicalGroup [IsTopologicalGroup J] [IsTopologicalGroup N]
    [ContinuousSMul J N] : IsTopologicalGroup (ActionProduct J N) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    exact ((actionProduct_continuous_left.comp continuous_fst).mul
      ((actionProduct_continuous_right.comp continuous_fst).smul
        (actionProduct_continuous_left.comp continuous_snd))).prodMk
      ((actionProduct_continuous_right.comp continuous_fst).mul
        (actionProduct_continuous_right.comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    exact (actionProduct_continuous_right.inv.smul actionProduct_continuous_left.inv).prodMk
      actionProduct_continuous_right.inv

instance actionProduct_profinite [Profinite J] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] : Profinite (ActionProduct J N) where
  toIsTopologicalGroup := inferInstance
  toCompactSpace := actionProductHomeomorph.symm.compactSpace
  toT2Space := actionProductHomeomorph.symm.t2Space
  toTotallyDisconnectedSpace := actionProductHomeomorph.symm.totallyDisconnectedSpace

end LocalConjugacy
