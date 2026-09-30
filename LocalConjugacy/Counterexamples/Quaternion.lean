module

public import LocalConjugacy.Definitions

@[expose] public section

/-!
The `Q₈ ⋊ S₃` obstruction from the introduction. We use Mathlib's quaternion
and dihedral groups, with `S₃ = DihedralGroup 3`. The action rotates `i,j,k`
and sends `(i,j,k)` to `(-j,-i,-k)` under a reflection.
All finite checks use kernel-checked `decide`, never `native_decide`.
-/

namespace LocalConjugacy.QuaternionExample

abbrev Q := QuaternionGroup 2
abbrev S := DihedralGroup 3

open QuaternionGroup

def rotate : Q → Q
  | .a i => ![a 0, xa 0, a 2, xa 2] i
  | .xa i => ![xa 3, a 3, xa 1, a 1] i

def reflect : Q → Q
  | .a i => ![a 0, xa 2, a 2, xa 0] i
  | .xa i => ![a 3, xa 3, a 1, xa 1] i

def act : S → Q → Q
  | .r i, x => rotate^[i.val] x
  | .sr i, x => reflect (rotate^[i.val] x)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem act_one : ∀ x : Q, act 1 x = x := by decide
theorem act_mul : ∀ s t : S, ∀ x : Q, act (s * t) x = act s (act t x) := by decide
theorem act_mul_Q : ∀ s : S, ∀ x y : Q, act s (x * y) = act s x * act s y := by decide

def action : S →* MulAut Q where
  toFun s :=
    { toFun := act s
      invFun := act s⁻¹
      left_inv := fun x => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun x => by rw [← act_mul, mul_inv_cancel, act_one]
      map_mul' := act_mul_Q s }
  map_one' := by ext x; exact act_one x
  map_mul' s t := by ext x; exact act_mul s t x

abbrev G := Q ⋊[action] S

/-- The nontrivial central cocycle (sign of the permutation). -/
def signCocycle : S → Q
  | .r _ => 1
  | .sr _ => a 2

def IsCocycle (f : S → Q) : Prop :=
  ∀ s t, f (s * t) = f s * act s (f t)

def Equivalent (f g : S → Q) : Prop :=
  ∃ n : Q, ∀ s, g s = n⁻¹ * f s * act s n

instance (f : S → Q) : Decidable (IsCocycle f) := inferInstanceAs
  (Decidable (∀ s t, f (s * t) = f s * act s (f t)))
instance (f g : S → Q) : Decidable (Equivalent f g) := inferInstanceAs
  (Decidable (∃ n : Q, ∀ s, g s = n⁻¹ * f s * act s n))

theorem sign_isCocycle : IsCocycle signCocycle := by decide
theorem not_equivalent : ¬ Equivalent (fun _ => 1) signCocycle := by decide

/-- The two restrictions are cohomologous at the prime 2. -/
theorem locally_equivalent_two : ∃ n : Q, ∀ s : S,
    s = 1 ∨ s = DihedralGroup.sr 0 → signCocycle s = n⁻¹ * act s n := by decide

/-- The restrictions at the prime 3 agree identically. -/
theorem locally_equivalent_three : ∀ i : ZMod 3, signCocycle (.r i) = 1 := by decide

/-- Reconstruction of a cocycle from its values on `r` and `s`. -/
def candidate (a b : Q) : S → Q
  | .r i => ![1, a, a * act (.r 1) a] i
  | .sr i => b * act (.sr 0) (![1, a, a * act (.r 1) a] i)

theorem candidate_classification : ∀ a b : Q, IsCocycle (candidate a b) →
    Equivalent (candidate a b) (fun _ => 1) ∨
    Equivalent (candidate a b) signCocycle := by decide

theorem cocycle_eq_candidate (f : S → Q) (hf : IsCocycle f) :
    f = candidate (f (.r 1)) (f (.sr 0)) := by
  have h1 : f 1 = 1 := by
    have h := hf 1 1
    rw [one_mul, act_one] at h
    exact (mul_eq_left.mp h.symm)
  have hr2 : f (.r 2) = f (.r 1) * act (.r 1) (f (.r 1)) := hf (.r 1) (.r 1)
  have hs0 := hf (.sr 0) (.r 0)
  have hs1 := hf (.sr 0) (.r 1)
  have hs2 := hf (.sr 0) (.r 2)
  change f (.sr 0) = f (.sr 0) * act (.sr 0) (f 1) at hs0
  rw [h1] at hs0
  rw [hr2] at hs2
  funext s
  rcases s with i | i <;> fin_cases i <;>
    first | exact h1 | rfl | exact hr2 | exact hs0 | exact hs1 | exact hs2

/-- There are exactly two cohomology classes, represented by `1` and sign. -/
theorem exactly_two_classes :
    IsCocycle (fun _ => 1) ∧ IsCocycle signCocycle ∧
    ¬ Equivalent (fun _ => 1) signCocycle ∧
    (∀ f : S → Q, IsCocycle f →
      Equivalent f (fun _ => 1) ∨ Equivalent f signCocycle) := by
  refine ⟨by decide, sign_isCocycle, not_equivalent, ?_⟩
  intro f hf
  rw [cocycle_eq_candidate f hf]
  apply candidate_classification
  rwa [← cocycle_eq_candidate f hf]

/-- Every cocycle on the cyclic Sylow 2-subgroup is a coboundary. -/
theorem sylow_two_H1_trivial : ∀ f : ZMod 2 → Q,
    (∀ x y, f (x + y) = f x * act (if x = 0 then 1 else .sr 0) (f y)) →
    ∃ n : Q, ∀ x, f x = n⁻¹ * act (if x = 0 then 1 else .sr 0) n := by decide

/-- Every cocycle on the cyclic Sylow 3-subgroup is a coboundary. -/
theorem sylow_three_H1_trivial : ∀ f : ZMod 3 → Q,
    (∀ x y, f (x + y) = f x * act (.r x) (f y)) →
    ∃ n : Q, ∀ x, f x = n⁻¹ * act (.r x) n := by decide

end LocalConjugacy.QuaternionExample
