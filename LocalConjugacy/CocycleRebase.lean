module

public import LocalConjugacy.Cohomology

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

namespace Cocycle

/-- Regard a cocycle on an ambient subgroup as a cocycle on the whole subgroup
viewed as a group in its own right. -/
def subgroupTop {L : Subgroup J} (f : Cocycle (N := N) L) :
    Cocycle (J := L) (N := N) ⊤ where
  toFun x := f.toFun x
  continuous_toFun := f.continuous_toFun.comp continuous_subtype_val
  map_mul x y := f.map_mul x y

def ofSubgroupTop {L : Subgroup J} (f : Cocycle (J := L) (N := N) ⊤) :
    Cocycle (N := N) L where
  toFun x := f.toFun ⟨x, trivial⟩
  continuous_toFun := f.continuous_toFun.comp (continuous_id.subtype_mk _)
  map_mul x y := f.map_mul ⟨x, trivial⟩ ⟨y, trivial⟩

/-- Restrict the ambient group used for the cocycle action, without changing
the domain subgroup or the values. -/
def onSubgroup {L K : Subgroup J} (f : Cocycle (N := N) K) :
    Cocycle (J := L) (N := N) (K.subgroupOf L) where
  toFun x := f.toFun ⟨x, x.property⟩
  continuous_toFun := f.continuous_toFun.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  map_mul x y := f.map_mul ⟨x, x.property⟩ ⟨y, y.property⟩

def ofOnSubgroup {L K : Subgroup J} (hKL : K ≤ L)
    (f : Cocycle (J := L) (N := N) (K.subgroupOf L)) : Cocycle (N := N) K where
  toFun x := f.toFun ⟨⟨x, hKL x.property⟩, x.property⟩
  continuous_toFun := f.continuous_toFun.comp
    ((continuous_subtype_val.subtype_mk _).subtype_mk _)
  map_mul x y := f.map_mul ⟨⟨x, hKL x.property⟩, x.property⟩
    ⟨⟨y, hKL y.property⟩, y.property⟩

end Cocycle

/-- Rebase the restriction isomorphism from a subgroup considered as its own
group to the original ambient group. -/
theorem restrictionIsomorphism_of_subgroup {L K : Subgroup J} (hKL : K ≤ L)
    (h : RestrictionIsomorphism (J := L) (N := N) ⊤ (K.subgroupOf L) le_top) :
    RestrictionIsomorphism (N := N) L K hKL := by
  constructor
  · intro f g hr
    have hh : Cohomologous f.subgroupTop g.subgroupTop := by
      apply h.1
      obtain ⟨n, hn⟩ := hr
      exact ⟨n, fun x => hn ⟨x, x.property⟩⟩
    obtain ⟨n, hn⟩ := hh
    exact ⟨n, fun x => hn ⟨x, trivial⟩⟩
  · intro g hg
    have hinv : InvariantUnder ⊤ (K.subgroupOf L) (g.onSubgroup (L := L)) := by
      intro j _
      obtain ⟨n, hn⟩ := hg j j.property
      exact ⟨n, fun x hx hjx => hn x hx hjx⟩
    obtain ⟨f, n, hn⟩ := h.2 (g.onSubgroup (L := L)) hinv
    refine ⟨f.ofSubgroupTop, n, fun x => ?_⟩
    exact hn ⟨⟨x, hKL x.property⟩, x.property⟩

end LocalConjugacy
