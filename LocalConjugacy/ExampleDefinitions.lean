module

public import LocalConjugacy.Definitions

@[expose] public section

namespace LocalConjugacy

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Coordinates of the matrix [[1,a,c],[0,1,b],[0,0,1]] over F₃.
This fixes the Heisenberg group itself, rather than only its order and exponent. -/
structure Heisenberg3 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
  deriving DecidableEq, Fintype

/-- Equality of Heisenberg coordinates. Written explicitly so the independent
Challenge and Solution share the same proof without private generated helpers. -/
@[ext] theorem Heisenberg3.ext {x y : Heisenberg3}
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) : x = y := by
  cases x
  cases y
  cases ha
  cases hb
  cases hc
  rfl

/-- Matrix multiplication in the three coordinates; the cross term is a · b'. -/
instance heisenbergMul : Mul Heisenberg3 :=
  ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩

/-- The identity matrix has all three upper-diagonal coordinates zero. -/
instance heisenbergOne : One Heisenberg3 := ⟨⟨0, 0, 0⟩⟩

/-- Matrix inversion introduces the cross-term correction in the top-right entry. -/
instance heisenbergInv : Inv Heisenberg3 :=
  ⟨fun x => ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

/-- The matrix coordinate operations satisfy the group axioms over F₃. -/
instance : Group Heisenberg3 where
  mul := heisenbergMul.mul
  one := heisenbergOne.one
  inv := heisenbergInv.inv
  mul_assoc x y z := by
    -- The group law is associative by the distributive law in F₃.
    apply Heisenberg3.ext
    · change (x.a + y.a) + z.a = x.a + (y.a + z.a)
      ring
    · change (x.b + y.b) + z.b = x.b + (y.b + z.b)
      ring
    · change (x.c + y.c + x.a * y.b) + z.c + (x.a + y.a) * z.b =
        x.c + (y.c + z.c + y.a * z.b) + x.a * (y.b + z.b)
      ring
  one_mul x := by
    -- The zero triple is the identity matrix.
    apply Heisenberg3.ext
    · change 0 + x.a = x.a
      ring
    · change 0 + x.b = x.b
      ring
    · change 0 + x.c + 0 * x.b = x.c
      ring
  mul_one x := by
    apply Heisenberg3.ext
    · change x.a + 0 = x.a
      ring
    · change x.b + 0 = x.b
      ring
    · change x.c + 0 + x.a * 0 = x.c
      ring
  inv_mul_cancel := by decide

/-- The natural permutation action on three coordinates. -/
def wreathPerm : DihedralGroup 3 → ZMod 3 → ZMod 3
  | .r a, i => a + i
  | .sr a, i => -(a + i)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem wreathPerm_one : ∀ i, wreathPerm 1 i = i := by decide
theorem wreathPerm_mul : ∀ s t i, wreathPerm (s * t) i = wreathPerm s (wreathPerm t i) := by decide

def wreathAction : DihedralGroup 3 →* MulAut (ZMod 3 → Multiplicative (ZMod 3)) where
  toFun s :=
    { toFun := fun b i => b (wreathPerm s⁻¹ i)
      invFun := fun b i => b (wreathPerm s i)
      left_inv := fun b => by ext i; dsimp; rw [← wreathPerm_mul, inv_mul_cancel, wreathPerm_one]
      right_inv := fun b => by ext i; dsimp; rw [← wreathPerm_mul, mul_inv_cancel, wreathPerm_one]
      map_mul' := fun _ _ => rfl }
  map_one' := by ext b i; dsimp; rw [inv_one, wreathPerm_one]
  map_mul' s t := by ext b i; dsimp; rw [mul_inv_rev, wreathPerm_mul]

/-- The imprimitive wreath product C₃ ≀ S₃ used in the preprint. -/
abbrev WreathC3S3 := (ZMod 3 → Multiplicative (ZMod 3)) ⋊[wreathAction] DihedralGroup 3

/-- Nonabelian cocycles for an explicitly supplied finite-group action. -/
def FiniteCocycle {J N : Type*} [Group J] [Group N] (a : J →* MulAut N) :=
  {f : J → N // ∀ x y, f (x * y) = f x * a x (f y)}

/-- Two cocycles differ by one global coboundary coefficient.
The structural equivalence proof is included so the quotient is an actual type. -/
def finiteCohomologySetoid {J N : Type*} [Group J] [Group N]
    (a : J →* MulAut N) : Setoid (FiniteCocycle a) where
  r f g := ∃ n : N, ∀ x, g.val x = n⁻¹ * f.val x * a x n
  iseqv := by
    constructor
    · -- The identity coefficient leaves a cocycle unchanged.
      intro f
      exact ⟨1, by simp⟩
    · -- Inverting a witness reverses the cohomology relation.
      rintro f g ⟨n, hn⟩
      refine ⟨n⁻¹, fun x => ?_⟩
      rw [hn x]
      simp [mul_assoc]
    · -- Multiplication composes the two global witnesses.
      rintro f g h ⟨n, hn⟩ ⟨m, hm⟩
      refine ⟨n * m, fun x => ?_⟩
      rw [hm x, hn x]
      simp [mul_assoc]

/-- Nonabelian H¹ for finite discrete groups, as an actual quotient of cocycles. -/
def FiniteH1 {J N : Type*} [Group J] [Group N] (a : J →* MulAut N) :=
  Quotient (finiteCohomologySetoid a)

end LocalConjugacy
