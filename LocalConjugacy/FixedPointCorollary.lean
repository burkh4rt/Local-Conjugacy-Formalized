module

public import LocalConjugacy.LocalInclusion
public import LocalConjugacy.Actions

@[expose] public section

namespace LocalConjugacy

/-- Corollary 1.4. Closedness of each point stabilizer supplies the closed
subgroup required by Corollary 1.3; no topology on the acted-on set is used. -/
theorem corollary_1_4 {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {Ω : Type*} [MulAction G Ω] [Nonempty Ω]
    (N J : Subgroup G) (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hsplit : Splits N J) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (htrans : Transitive (G := G) (Ω := Ω))
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hnormal : ∃ x : Ω, IntersectionNormal N (MulAction.stabilizer G x))
    (hlocal : SylowFixedPoints (Ω := Ω) J) : HasFixedPoint (Ω := Ω) J := by
  obtain ⟨x, hx⟩ := hnormal
  apply fixedPoint_of_local_inclusion htrans J x hlocal
  exact corollary_1_3 N J (MulAction.stabilizer G x) hN hJ (hclosed x)
    hsplit hpron hcase hx

end LocalConjugacy
