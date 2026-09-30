module

public import LocalConjugacy.ExampleDefinitions
public import LocalConjugacy.Counterexamples.HeisenbergStructure

@[expose] public section

namespace LocalConjugacy.HeisenbergExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Upper-unitriangular coordinates inside the imprimitive wreath product. -/
def heisenbergCoordinates : Heisenberg3 →* G where
  toFun x := ⟨fun i => Multiplicative.ofAdd (x.c - x.b * i), .r x.a⟩
  map_one' := by decide
  map_mul' := by decide

def heisenbergHom : Heisenberg3 →* N :=
  heisenbergCoordinates.codRestrict N (by decide)

theorem heisenberg_bijective : Function.Bijective heisenbergHom := by
  constructor
  · exact (by decide : ∀ x y, heisenbergHom x = heisenbergHom y → x = y)
  · exact (by decide : ∀ y, ∃ x, heisenbergHom x = y)

/-- N is the Heisenberg group over F₃, not merely a group of the right order. -/
noncomputable def nEquivHeisenberg : N ≃* Heisenberg3 :=
  (MulEquiv.ofBijective heisenbergHom heisenberg_bijective).symm

/-- The chosen complement is C₆ via its reductions modulo 3 and 2. -/
def cyclicCoordinates : Multiplicative (ZMod 6) →* G where
  toFun x := sectionMap (Multiplicative.ofAdd (ZMod.cast x.toAdd : ZMod 3),
    Multiplicative.ofAdd (ZMod.cast x.toAdd : ZMod 2))
  map_one' := by decide
  map_mul' := by decide

def cyclicHom : Multiplicative (ZMod 6) →* J :=
  cyclicCoordinates.codRestrict J (by decide)

theorem cyclic_bijective : Function.Bijective cyclicHom := by
  constructor
  · exact (by decide : ∀ x y, cyclicHom x = cyclicHom y → x = y)
  · exact (by decide : ∀ y, ∃ x, cyclicHom x = y)

noncomputable def jEquivC6 : J ≃* Multiplicative (ZMod 6) :=
  (MulEquiv.ofBijective cyclicHom cyclic_bijective).symm

/-- The constructed ambient group is the natural three-coordinate wreath product. -/
def gEquivWreath : G ≃* WreathC3S3 := MulEquiv.refl _

end LocalConjugacy.HeisenbergExample
