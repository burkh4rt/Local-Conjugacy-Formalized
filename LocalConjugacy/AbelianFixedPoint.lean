module

public import LocalConjugacy.AbelianManuscript
public import LocalConjugacy.LocalSupplement
public import LocalConjugacy.Actions

@[expose] public section

namespace LocalConjugacy

/-- Proposition 4.2, `thm:fix_pt_ab`. -/
theorem proposition_4_2 {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {Ω : Type*} [MulAction G Ω] [Nonempty Ω]
    (N H : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    (hH : IsClosed (H : Set G)) (hcomm : ∀ n m : N, n * m = m * n)
    (hHN : Supplements N H) (htrans : Transitive (G := G) (Ω := Ω))
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hlocal : SylowFixedPoints (Ω := Ω) H) : HasFixedPoint (Ω := Ω) H := by
  obtain ⟨x⟩ := ‹Nonempty Ω›
  have hl := locallyContains_stabilizer_of_sylowFixedPoints htrans H x hlocal
  have hs := supplements_of_locallyContains N (MulAction.stabilizer G x) H
    hN (hclosed x) hH hHN hl
  obtain ⟨g, hg⟩ := proposition_4_1 N (MulAction.stabilizer G x) H
    hN (hclosed x) hH hcomm hs hHN hl
  exact fixedPoint_of_conjugate_le_stabilizer H x g hg

end LocalConjugacy
