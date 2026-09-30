module

public import LocalConjugacy.Counterexamples.Heisenberg

@[expose] public section

namespace LocalConjugacy.HeisenbergExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Diagonal and anti-diagonal base coordinates identify the stabilizer
of `(0, 1)` with `C₃ × S₃`, as stated in the manuscript. -/
def hCoordinates : C3 × S →* G where
  toFun z := match z.2 with
    | .r a => ⟨fun i => if i = 0 then 1 else if i = 1 then
        z.1 * Multiplicative.ofAdd a else z.1 * Multiplicative.ofAdd (-a), 1⟩
    | .sr a => ⟨fun i => if i = 0 then 1 else if i = 1 then
        z.1 * Multiplicative.ofAdd (-a) else z.1 * Multiplicative.ofAdd a, .sr 0⟩
  map_one' := by decide
  map_mul' := by decide

def hCoordinatesHom : C3 × S →* H :=
  hCoordinates.codRestrict H (by decide)

theorem hCoordinates_bijective : Function.Bijective hCoordinatesHom := by
  constructor
  · exact (by decide : ∀ x y, hCoordinatesHom x = hCoordinatesHom y → x = y)
  · exact (by decide : ∀ y, ∃ x, hCoordinatesHom x = y)

/-- The manuscript's identification of the order-18 subgroup. -/
noncomputable def hEquivProduct : H ≃* C3 × S :=
  (MulEquiv.ofBijective hCoordinatesHom hCoordinates_bijective).symm

end LocalConjugacy.HeisenbergExample
