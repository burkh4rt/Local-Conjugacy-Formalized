module

public import LocalConjugacy.InvariantRestriction
public import LocalConjugacy.ProPFixedPoint

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

@[ext] theorem Cocycle.ext {K : Subgroup J} {f g : Cocycle (N := N) K}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Left coefficient action on cocycles. Its orbits are cohomology classes. -/
def coboundaryCocycle {K : Subgroup J} (f : Cocycle (N := N) K) (n : N) :
    Cocycle (N := N) K where
  toFun x := n * f.toFun x * ((x : J) • n⁻¹)
  continuous_toFun := (continuous_const.mul f.continuous_toFun).mul
    (continuous_subtype_val.smul continuous_const)
  map_mul x y := by
    rw [f.map_mul]
    simp only [Subgroup.coe_mul, smul_mul', smul_smul, smul_inv']
    group

@[instance_reducible] def coefficientAction (K : Subgroup J) : MulAction N (Cocycle (N := N) K) where
  smul n f := coboundaryCocycle f n
  one_smul f := by
    apply Cocycle.ext
    intro x
    change 1 * f.toFun x * ((x : J) • (1 : N)⁻¹) = f.toFun x
    simp
  mul_smul n m f := by
    apply Cocycle.ext
    intro x
    change (n * m) * f.toFun x * ((x : J) • (n * m)⁻¹) =
      n * (m * f.toFun x * ((x : J) • m⁻¹)) * ((x : J) • n⁻¹)
    simp only [mul_inv_rev, smul_mul']
    group

def CohomologyClass {K : Subgroup J} (f : Cocycle (N := N) K) :=
  {g : Cocycle (N := N) K // Cohomologous f g}

theorem orbit_eq_cohomologyClass {K : Subgroup J} (f : Cocycle (N := N) K) :
    @MulAction.orbit N (Cocycle (N := N) K) (coefficientAction K).toSMul f =
      {g | Cohomologous f g} := by
  letI := coefficientAction (N := N) K
  ext g
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n⁻¹, fun x => ?_⟩
    have he := congrArg (fun c : Cocycle (N := N) K => c.toFun x) hn
    change n * f.toFun x * ((x : J) • n⁻¹) = g.toFun x at he
    simpa only [inv_inv] using he.symm
  · rintro ⟨n, hn⟩
    refine ⟨n⁻¹, ?_⟩
    apply Cocycle.ext
    intro x
    change n⁻¹ * f.toFun x * ((x : J) • (n⁻¹)⁻¹) = g.toFun x
    simpa only [inv_inv] using (hn x).symm

instance finite_cohomologyClass [Finite N] {K : Subgroup J} (f : Cocycle (N := N) K) :
    Finite (CohomologyClass f) := by
  letI := coefficientAction (N := N) K
  letI : Finite (MulAction.orbit N f) := Finite.of_surjective
    (fun n : N => (⟨n • f, ⟨n, rfl⟩⟩ : MulAction.orbit N f))
    (by rintro ⟨g, n, hn⟩; exact ⟨n, Subtype.ext hn⟩)
  have he := orbit_eq_cohomologyClass f
  exact Finite.of_equiv (MulAction.orbit N f) (Set.equivOfEq he)

theorem card_cohomologyClass {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    {K : Subgroup J} (f : Cocycle (N := N) K) [Finite (CohomologyClass f)] :
    ∃ k : ℕ, Nat.card (CohomologyClass f) = p ^ k := by
  letI := coefficientAction (N := N) K
  have he := Set.equivOfEq (orbit_eq_cohomologyClass f)
  letI : Finite (MulAction.orbit N f) := Finite.of_equiv (CohomologyClass f) he.symm
  obtain ⟨k, hk⟩ := hN.card_orbit f
  exact ⟨k, (Nat.card_congr he).symm.trans hk⟩

theorem twist_one {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) :
    twistCocycle f 1 = f := by
  ext x
  simp only [twistCocycle, conjugateDomain, inv_one, one_mul, mul_one, one_smul]
  rfl

theorem twist_mul {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) (j k : J) :
    twistCocycle f (j * k) = twistCocycle (twistCocycle f k) j := by
  apply Cocycle.ext
  intro x
  change (j * k) • f.toFun ⟨(j * k)⁻¹ * x * (j * k), _⟩ =
    j • (k • f.toFun ⟨k⁻¹ * (j⁻¹ * x * j) * k, _⟩)
  simp only [mul_inv_rev, mul_smul, mul_assoc]

@[instance_reducible] def classAction {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K)
    (Q : Subgroup J) (hinv : InvariantUnder Q K f) : MulAction Q (CohomologyClass f) where
  smul q g := ⟨twistCocycle g.val q, by
    have hq : Cohomologous f (twistCocycle f q) := by
      obtain ⟨n, hn⟩ := hinv q q.property
      exact ⟨n, fun x => hn x x.property (conjugateDomain K q x).property⟩
    exact cohomologous_trans hq (twist_cohomologous g.property q)⟩
  one_smul g := Subtype.ext (twist_one g.val)
  mul_smul q r g := Subtype.ext (twist_mul g.val q r)

theorem classAction_closed_stabilizers [T2Space N]
    {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K)
    (Q : Subgroup J) (hinv : InvariantUnder Q K f) (g : CohomologyClass f) :
    @IsClosed Q _ (@MulAction.stabilizer Q (CohomologyClass f) _ (classAction f Q hinv) g : Set Q) := by
  letI := classAction f Q hinv
  have he : (MulAction.stabilizer Q g : Set Q) =
      ⋂ x : K, {q : Q | (q : J) • g.val.toFun (conjugateDomain K q x) = g.val.toFun x} := by
    ext q
    simp only [MulAction.mem_stabilizer_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h x
      exact congrArg (fun c : CohomologyClass f => c.val.toFun x) h
    · intro h
      apply Subtype.ext
      exact Cocycle.ext h
  rw [he]
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  apply Continuous.smul continuous_subtype_val
  apply g.val.continuous_toFun.comp
  exact ((continuous_subtype_val.inv.mul continuous_const).mul
    continuous_subtype_val).subtype_mk _

/-- The finite-orbit part of Proposition 2.1. It permits infinite `N` when
the particular cohomology class has finitely many representatives. -/
theorem fixed_cocycle_of_finite_class [T2Space N]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p) (hN : IsPGroup p N)
    {K : Subgroup J} [K.Normal] (Q : Subgroup J) (hQ : IsProP q Q)
    (f : Cocycle (N := N) K) (hinv : InvariantUnder Q K f)
    [Finite (CohomologyClass f)] :
    ∃ g : Cocycle (N := N) K, Cohomologous f g ∧
      ∀ x : Q, twistCocycle g x = g := by
  letI := classAction f Q hinv
  obtain ⟨k, hk⟩ := card_cohomologyClass hN f
  have hn : ¬ q ∣ Nat.card (CohomologyClass f) := by
    rw [hk]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp
      ((Fact.out : q.Prime).dvd_of_dvd_pow h))
  obtain ⟨g, hg⟩ := proP_fixed_point hQ (classAction_closed_stabilizers f Q hinv) hn
  exact ⟨g.val, g.property, fun x => congrArg Subtype.val (hg x)⟩

end LocalConjugacy
