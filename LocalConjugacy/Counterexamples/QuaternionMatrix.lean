module

public import LocalConjugacy.Counterexamples.Quaternion

@[expose] public section

namespace LocalConjugacy.QuaternionExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

instance : Fintype G := Fintype.ofEquiv (Q × S) SemidirectProduct.equivProd.symm
instance : DecidableEq G := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2,
     fun h => ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩⟩

abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 3)

/-- Quaternion generators i and j in GL(2,3). -/
def qi : Mat := !![0, 1; 2, 0]
def qj : Mat := !![1, 1; 1, 2]
/-- An order-three rotation and an order-two reflection implementing the action. -/
def sr : Mat := !![0, 1; 2, 2]
def ss : Mat := !![1, 0; 2, 2]

def qMatrix : Q → Mat
  | .a i => qi ^ i.val
  | .xa i => qj * qi ^ i.val

def sMatrix : S → Mat
  | .r i => sr ^ i.val
  | .sr i => ss * sr ^ i.val

def matrix (g : G) : Mat := qMatrix g.left * sMatrix g.right

theorem matrix_one : matrix 1 = 1 := by decide

theorem matrix_mul : ∀ g h : G, matrix (g * h) = matrix g * matrix h := by decide

/-- The semidirect product is realized as invertible matrices over F₃. -/
def matrixHom : G →* GL (Fin 2) (ZMod 3) where
  toFun g :=
    { val := matrix g
      inv := matrix g⁻¹
      val_inv := by rw [← matrix_mul, mul_inv_cancel, matrix_one]
      inv_val := by rw [← matrix_mul, inv_mul_cancel, matrix_one] }
  map_one' := Units.ext matrix_one
  map_mul' g h := Units.ext (matrix_mul g h)

theorem matrix_injective : Function.Injective matrix := by decide

theorem matrix_covers : ∀ m : Mat, m.det ≠ 0 → ∃ g : G, matrix g = m := by decide

/-- The precise matrix-group identification named in the preprint. -/
noncomputable def equivGL : G ≃* GL (Fin 2) (ZMod 3) :=
  MulEquiv.ofBijective matrixHom ⟨
    fun _ _ h => matrix_injective (congrArg Units.val h),
    fun m => by
      obtain ⟨g, hg⟩ := matrix_covers m.val (by
        exact Matrix.GeneralLinearGroup.det_ne_zero m)
      exact ⟨g, Units.ext hg⟩⟩

end LocalConjugacy.QuaternionExample
