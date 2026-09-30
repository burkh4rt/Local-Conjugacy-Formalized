module

public import LocalConjugacy.Counterexamples.QuaternionComplements

@[expose] public section

namespace LocalConjugacy.QuaternionExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Every nontrivial involution of S₃ gives trivial H¹ on its cyclic subgroup. -/
theorem involution_coboundaries : ∀ s : S, s ≠ 1 → s ^ 2 = 1 →
    ∀ f : ZMod 2 → Q,
    (∀ x y, f (x + y) = f x * action (s ^ x.val) (f y)) →
    ∃ n, ∀ x, f x = n⁻¹ * action (s ^ x.val) n := by decide

theorem order_three_coboundaries : ∀ s : S, s ^ 3 = 1 →
    ∀ f : ZMod 3 → Q,
    (∀ x y, f (x + y) = f x * action (s ^ x.val) (f y)) →
    ∃ n, ∀ x, f x = n⁻¹ * action (s ^ x.val) n := by decide

theorem two_map (e : Multiplicative (ZMod 2) →* S) (x : ZMod 2) :
    e (Multiplicative.ofAdd x) = e (Multiplicative.ofAdd 1) ^ x.val := by
  fin_cases x
  · exact e.map_one
  · change e (Multiplicative.ofAdd 1) = e (Multiplicative.ofAdd 1) ^ 1
    rw [pow_one]

theorem three_map (e : Multiplicative (ZMod 3) →* S) (x : ZMod 3) :
    e (Multiplicative.ofAdd x) = e (Multiplicative.ofAdd 1) ^ x.val := by
  fin_cases x
  · exact e.map_one
  · change e (Multiplicative.ofAdd 1) = e (Multiplicative.ofAdd 1) ^ 1
    rw [pow_one]
  · exact (e.map_pow (Multiplicative.ofAdd 1) 2)

theorem coboundary_of_card_two (P : Subgroup S) (hP : Nat.card P = 2)
    (f : FiniteCocycle (action.comp P.subtype)) :
    ∃ n : Q, ∀ x : P, f.val x = n⁻¹ * action (x : S) n := by
  let e : Multiplicative (ZMod 2) ≃* P :=
    mulEquivOfPrimeCardEq (p := 2) (by simp) hP
  let k := P.subtype.comp e.toMonoidHom
  have hn : k (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    have := e.injective (Subtype.ext (h.trans (congrArg Subtype.val e.map_one).symm))
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1) this
  have hp : k (Multiplicative.ofAdd 1) ^ 2 = 1 := by
    rw [← map_pow]
    exact k.map_one
  obtain ⟨n, hn⟩ := involution_coboundaries _ hn hp
    (fun x => f.val (e (Multiplicative.ofAdd x))) (by
      intro x y
      change f.val (e (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) = _
      rw [map_mul, ← two_map k x]
      exact f.property (e (Multiplicative.ofAdd x)) (e (Multiplicative.ofAdd y)))
  refine ⟨n, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective x
  have hh := hn x.toAdd
  rw [← two_map k x.toAdd] at hh
  simpa [k] using hh

theorem coboundary_of_card_three (P : Subgroup S) (hP : Nat.card P = 3)
    (f : FiniteCocycle (action.comp P.subtype)) :
    ∃ n : Q, ∀ x : P, f.val x = n⁻¹ * action (x : S) n := by
  let e : Multiplicative (ZMod 3) ≃* P :=
    mulEquivOfPrimeCardEq (p := 3) (by simp) hP
  let k := P.subtype.comp e.toMonoidHom
  have hp : k (Multiplicative.ofAdd 1) ^ 3 = 1 := by
    rw [← map_pow]
    exact k.map_one
  obtain ⟨n, hn⟩ := order_three_coboundaries _ hp
    (fun x => f.val (e (Multiplicative.ofAdd x))) (by
      intro x y
      change f.val (e (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) = _
      rw [map_mul, ← three_map k x]
      exact f.property (e (Multiplicative.ofAdd x)) (e (Multiplicative.ofAdd y)))
  refine ⟨n, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective x
  have hh := hn x.toAdd
  rw [← three_map k x.toAdd] at hh
  simpa [k] using hh

/-- All primes and every Sylow subgroup are included, not only the displayed generators. -/
theorem sylow_coboundaries (p : ℕ) [Fact p.Prime] (P : Sylow p S)
    (f : FiniteCocycle (action.comp P.toSubgroup.subtype)) :
    ∃ n : Q, ∀ x : P, f.val x = n⁻¹ * action (x : S) n := by
  have hc := P.card_eq_multiplicity
  have hS : Nat.card S = 6 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hS] at hc
  by_cases h2 : p = 2
  · subst p
    apply coboundary_of_card_two _ _ f
    have hfac : (Nat.factorization 6) 2 = 1 := by
      rw [show 6 = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide)]
      simp [(by decide : Nat.Prime 2).factorization, (by decide : Nat.Prime 3).factorization]
    rw [hfac] at hc
    simpa using hc
  by_cases h3 : p = 3
  · subst p
    apply coboundary_of_card_three _ _ f
    have hfac : (Nat.factorization 6) 3 = 1 := by
      rw [show 6 = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide)]
      simp [(by decide : Nat.Prime 2).factorization, (by decide : Nat.Prime 3).factorization]
    rw [hfac] at hc
    simpa using hc
  have hnd : ¬ p ∣ 6 := by
    intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp (show p ∣ 2 * 3 from h) with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp h)
  have hcard : Nat.card P = 1 := by simpa [Nat.factorization_eq_zero_of_not_dvd hnd] using hc
  letI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hf : f.val 1 = 1 := by
    have h := f.property 1 1
    simpa using h
  refine ⟨1, fun x => ?_⟩
  rw [Subsingleton.elim x 1, hf]
  simp

theorem sylow_H1_subsingleton (p : ℕ) [Fact p.Prime] (P : Sylow p S) :
    Subsingleton (FiniteH1 (action.comp P.toSubgroup.subtype)) := by
  let z : FiniteCocycle (action.comp P.toSubgroup.subtype) := ⟨fun _ => 1, by simp⟩
  have h (c : FiniteH1 (action.comp P.toSubgroup.subtype)) :
      c = Quotient.mk _ z := by
    induction c using Quotient.inductionOn with
    | h f =>
      obtain ⟨n, hn⟩ := sylow_coboundaries p P f
      have hr : (finiteCohomologySetoid (action.comp P.toSubgroup.subtype)).r z f :=
        ⟨n, fun x => by simpa [z] using hn x⟩
      exact (Quotient.sound hr).symm
  exact ⟨fun x y => (h x).trans (h y).symm⟩

end LocalConjugacy.QuaternionExample
