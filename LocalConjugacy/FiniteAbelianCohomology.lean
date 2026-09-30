module

public import LocalConjugacy.Definitions

@[expose] public section

namespace LocalConjugacy
namespace FiniteAbelianCohomology

variable {J A : Type*} [Group J] [CommGroup A]

/-- Coboundaries form a subgroup when the coefficient group is abelian. -/
def coboundaryHom (a : J →* MulAut A) : A →* (J → A) where
  toFun n x := n⁻¹ * a x n
  map_one' := by ext x; simp
  map_mul' n m := by
    ext x
    simp only [mul_inv_rev, map_mul, Pi.mul_apply]
    ac_rfl

theorem norm_coboundary [Fintype J] (a : J →* MulAut A) (f : J → A)
    (hf : CocycleFn a f) (P : Subgroup J) (n : A)
    (hP : ∀ x : P, f x * a x n = n) :
    ∃ b : A, ∀ x : J, f x ^ P.index = b⁻¹ * a x b := by
  classical
  let u : J ⧸ P → A := Quotient.lift (fun x : J => f x * a x n) (by
    intro x y hxy
    have hm : x⁻¹ * y ∈ P := QuotientGroup.leftRel_apply.mp hxy
    have he := hP ⟨x⁻¹ * y, hm⟩
    have hy : x * (x⁻¹ * y) = y := by group
    calc
      f x * a x n = f x * a x (f (x⁻¹ * y) * a (x⁻¹ * y) n) := by rw [he]
      _ = f (x * (x⁻¹ * y)) * a (x * (x⁻¹ * y)) n := by
        rw [hf x (x⁻¹ * y)]
        simp only [map_mul, MulAut.mul_apply, mul_assoc]
      _ = f y * a y n := by rw [hy])
  have hu (x y : J) : u (x • (QuotientGroup.mk y : J ⧸ P)) =
      f x * a x (u (QuotientGroup.mk y)) := by
    change f (x * y) * a (x * y) n = f x * a x (f y * a y n)
    rw [hf]
    simp only [map_mul, MulAut.mul_apply]
    group
  let b : A := ∏ q : J ⧸ P, u q
  have hb (x : J) : b = f x ^ P.index * a x b := by
    calc
      b = ∏ q : J ⧸ P, u (x • q) := by
        exact (Fintype.prod_equiv (MulAction.toPerm x) _ _ (fun q => rfl)).symm
      _ = ∏ q : J ⧸ P, (f x * a x (u q)) := by
        apply Finset.prod_congr rfl
        intro q _
        induction q using Quotient.inductionOn with
        | h y => exact hu x y
      _ = f x ^ P.index * a x b := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          ← map_prod]
        rw [Fintype.card_eq_nat_card]
        rfl
  refine ⟨b⁻¹, fun x => ?_⟩
  have he := hb x
  simp only [inv_inv, map_inv]
  exact (eq_mul_inv_iff_mul_eq.mpr he.symm)

/-- For finite groups and abelian coefficients, a cocycle that is trivial
on one Sylow subgroup for every prime is a coboundary. The proof uses the
explicit coset norm above, followed by the coprimality of Sylow indices. -/
theorem local_coboundary [Fintype J] [Finite A]
    (a : J →* MulAut A) (f : J → A) (hf : CocycleFn a f)
    (hloc : ∀ p : ℕ, p.Prime → ∃ P : Sylow p J, ∃ n : A,
      ∀ x : P, f x * a x n = n) :
    ∃ b : A, ∀ x : J, f x = b⁻¹ * a x b := by
  classical
  let B := (coboundaryHom a).range
  let π := QuotientGroup.mk' B
  have hone : orderOf (π f) = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, n, hP⟩ := hloc p hp
    obtain ⟨b, hb⟩ := norm_coboundary a f hf P.toSubgroup n hP
    have hpow : π f ^ P.toSubgroup.index = 1 := by
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨b, funext (fun x => (hb x).symm)⟩
    exact P.not_dvd_index (hpd.trans (orderOf_dvd_of_pow_eq_one hpow))
  have hfB : f ∈ B := (QuotientGroup.eq_one_iff f).mp (orderOf_eq_one_iff.mp hone)
  obtain ⟨b, hb⟩ := hfB
  exact ⟨b, fun x => (congrFun hb x).symm⟩

end FiniteAbelianCohomology
end LocalConjugacy
