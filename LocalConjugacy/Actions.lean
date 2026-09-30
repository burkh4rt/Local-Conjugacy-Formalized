module

public import LocalConjugacy.Definitions

@[expose] public section

namespace LocalConjugacy

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- The geometric step in Corollary 1.4 and Proposition 4.2. -/
theorem fixedPoint_of_conjugate_le_stabilizer (J : Subgroup G) (x : Ω)
    (g : G) (h : conjugate g J ≤ MulAction.stabilizer G x) :
    HasFixedPoint (Ω := Ω) J := by
  refine ⟨g⁻¹ • x, ?_⟩
  intro j hj
  have hf : (g * j * g⁻¹) • x = x := h (Subgroup.mem_map_of_mem _ hj)
  have ht := congrArg (fun y : Ω => g⁻¹ • y) hf
  simpa [mul_smul] using ht

/-- Transitivity takes a fixed point to conjugate subgroup inclusion in a
chosen point stabilizer. -/
theorem conjugate_le_stabilizer_of_fixedPoint (htrans : Transitive (G := G) (Ω := Ω))
    (J : Subgroup G) (x : Ω) (hfix : HasFixedPoint (Ω := Ω) J) :
    ∃ g : G, conjugate g J ≤ MulAction.stabilizer G x := by
  obtain ⟨y, hy⟩ := hfix
  obtain ⟨g, hg⟩ := htrans y x
  refine ⟨g, ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  change (g * j * g⁻¹) • x = x
  rw [← hg]
  simp [mul_smul, hy j hj]

theorem fixedPoint_iff_conjugate_le_stabilizer
    (htrans : Transitive (G := G) (Ω := Ω)) (J : Subgroup G) (x : Ω) :
    HasFixedPoint (Ω := Ω) J ↔ ∃ g : G, conjugate g J ≤ MulAction.stabilizer G x :=
  ⟨conjugate_le_stabilizer_of_fixedPoint htrans J x,
   fun ⟨g, hg⟩ => fixedPoint_of_conjugate_le_stabilizer J x g hg⟩

theorem locallyContains_stabilizer_of_sylowFixedPoints [TopologicalSpace G]
    (htrans : Transitive (G := G) (Ω := Ω)) (J : Subgroup G) (x : Ω)
    (hlocal : SylowFixedPoints (Ω := Ω) J) :
    LocallyContains (MulAction.stabilizer G x) J := by
  intro p hp
  obtain ⟨P, hP, hf⟩ := hlocal p hp
  exact ⟨P, hP, conjugate_le_stabilizer_of_fixedPoint htrans P x hf⟩

/-- This is the proved reduction used by Corollary 1.4. `inclusion` is an
explicit input, not an axiom or a claimed proof of Corollary 1.3. -/
theorem fixedPoint_of_local_inclusion [TopologicalSpace G]
    (htrans : Transitive (G := G) (Ω := Ω)) (J : Subgroup G) (x : Ω)
    (hlocal : SylowFixedPoints (Ω := Ω) J)
    (inclusion : LocallyContains (MulAction.stabilizer G x) J →
      ∃ g : G, conjugate g J ≤ MulAction.stabilizer G x) :
    HasFixedPoint (Ω := Ω) J := by
  obtain ⟨g, hg⟩ := inclusion (locallyContains_stabilizer_of_sylowFixedPoints htrans J x hlocal)
  exact fixedPoint_of_conjugate_le_stabilizer J x g hg

end LocalConjugacy
