module

public import LocalConjugacy.ProcyclicSupplement
public import LocalConjugacy.CocycleActions

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- The action whose fixed points are the intertwiners between two cocycles. -/
@[instance_reducible] def intertwiningAction
    (f g : Cocycle (N := N) (⊤ : Subgroup J)) : MulAction J N where
  smul j n := f.toFun ⟨j, trivial⟩ * (j • n) * (g.toFun ⟨j, trivial⟩)⁻¹
  one_smul n := by
    change f.toFun 1 * ((1 : J) • n) * (g.toFun 1)⁻¹ = n
    simp [cocycle_one]
  mul_smul j k n := by
    change f.toFun (⟨j, trivial⟩ * ⟨k, trivial⟩) * ((j * k) • n) *
        (g.toFun (⟨j, trivial⟩ * ⟨k, trivial⟩))⁻¹ =
      f.toFun ⟨j, trivial⟩ *
        (j • (f.toFun ⟨k, trivial⟩ * (k • n) * (g.toFun ⟨k, trivial⟩)⁻¹)) *
        (g.toFun ⟨j, trivial⟩)⁻¹
    simp only [f.map_mul, g.map_mul, Subgroup.coe_mk, mul_smul, mul_inv_rev,
      smul_mul', smul_inv']
    group

/-- The group of automorphisms of one cocycle, regarded as a subgroup of the
coefficient group. Its order is a power of `p` when the coefficients form a
finite `p`-group. -/
def cocycleCentralizer (K : Subgroup J) (f : Cocycle (N := N) (⊤ : Subgroup J)) :
    Subgroup N :=
  ⨅ x : K, ((MulAut.conj (f.toFun ⟨x, trivial⟩) *
    MulDistribMulAction.toMulAut J N x).toMonoidHom).eqLocus (MonoidHom.id N)

theorem mem_cocycleCentralizer (K : Subgroup J)
    (f : Cocycle (N := N) (⊤ : Subgroup J)) (n : N) :
    n ∈ cocycleCentralizer K f ↔
      ∀ x : K, f.toFun ⟨x, trivial⟩ * ((x : J) • n) * (f.toFun ⟨x, trivial⟩)⁻¹ = n := by
  simp only [cocycleCentralizer, Subgroup.mem_iInf]
  rfl

/-- A nonempty set of intertwiners is a torsor for the cocycle centralizer. -/
theorem card_intertwiners {p : ℕ} [Fact p.Prime] [Finite N]
    (hN : IsPGroup p N) (K : Subgroup J)
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (n₀ : N) (hn₀ : ∀ x : K, g.toFun ⟨x, trivial⟩ =
      n₀⁻¹ * f.toFun ⟨x, trivial⟩ * ((x : J) • n₀)) :
    letI := intertwiningAction f g
    ∃ k : ℕ, Nat.card (MulAction.fixedPoints K N) = p ^ k := by
  let a := MulDistribMulAction.toMulAut J N
  have hfg (x : K) : g.toFun ⟨x, trivial⟩ =
      n₀⁻¹ * f.toFun ⟨x, trivial⟩ * a x n₀ := hn₀ x
  letI := intertwiningAction f g
  let T := MulAction.fixedPoints K N
  have ht (n : N) : n ∈ T ↔ n * n₀⁻¹ ∈ cocycleCentralizer K f := by
    rw [mem_cocycleCentralizer]
    change (∀ x : K, f.toFun ⟨x, trivial⟩ * a x n * (g.toFun ⟨x, trivial⟩)⁻¹ = n) ↔
      ∀ x : K, f.toFun ⟨x, trivial⟩ * a x (n * n₀⁻¹) * (f.toFun ⟨x, trivial⟩)⁻¹ = n * n₀⁻¹
    simp only [map_mul, map_inv, hfg, mul_inv_rev, inv_inv]
    constructor
    · intro h x
      have he := congrArg (fun z => z * n₀⁻¹) (h x)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using he
    · intro h x
      have he := congrArg (fun z => z * n₀) (h x)
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he
  let e : T ≃ cocycleCentralizer K f :=
    { toFun := fun n => ⟨n.val * n₀⁻¹, (ht n.val).mp n.property⟩
      invFun := fun n => ⟨n.val * n₀, (ht _).mpr (by simpa using n.property)⟩
      left_inv := fun n => by apply Subtype.ext; simp
      right_inv := fun n => by apply Subtype.ext; simp }
  obtain ⟨k, hk⟩ := (hN.to_subgroup (cocycleCentralizer K f)).exists_card_eq
  exact ⟨k, (Nat.card_congr e).trans hk⟩

/-- Restriction to a normal subgroup is injective on finite `p`-coefficient
cohomology when there is a pro-`q` supplement, with `q ≠ p`. -/
theorem restriction_injective_of_coprime_supplement
    [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] [Finite N] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hne : q ≠ p) (hN : IsPGroup p N)
    (K Q : Subgroup J) [K.Normal] (hQ : IsProP q Q) (hs : Supplements K Q)
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hr : Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) f) (restrictCocycle le_top g)) :
    Cohomologous f g := by
  obtain ⟨n₀, hn₀⟩ := hr
  obtain ⟨k, hk⟩ := card_intertwiners hN K f g n₀ hn₀
  let a := MulDistribMulAction.toMulAut J N
  have hcont (n : N) : Continuous (fun x : Q =>
      f.toFun ⟨x, trivial⟩ * a x n * (g.toFun ⟨x, trivial⟩)⁻¹) :=
    ((f.continuous_toFun.comp (continuous_subtype_val.subtype_mk _)).mul
      (continuous_subtype_val.smul continuous_const)).mul
      (g.continuous_toFun.comp (continuous_subtype_val.subtype_mk _)).inv
  letI := intertwiningAction f g
  let T := MulAction.fixedPoints K N
  have hc (n : T) : IsClosed (MulAction.stabilizer Q n : Set Q) := by
    have he : (MulAction.stabilizer Q n : Set Q) =
        {x : Q | f.toFun ⟨x, trivial⟩ * a x n.val * (g.toFun ⟨x, trivial⟩)⁻¹ = n.val} := by
      ext x
      exact Subtype.ext_iff
    rw [he]
    exact isClosed_eq (hcont n.val) continuous_const
  have hcard : ¬ q ∣ Nat.card T := by
    rw [hk]
    exact fun h => hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : p.Prime)).mp ((Fact.out : q.Prime).dvd_of_dvd_pow h))
  obtain ⟨n, hn⟩ := proP_fixed_point hQ hc hcard
  have hglobal (j : J) : j • (n.val : N) = n.val := by
    obtain ⟨x, hx, y, hy, rfl⟩ := hs j
    rw [mul_smul]
    have hy' : y • (n.val : N) = n.val := congrArg Subtype.val (hn ⟨y, hy⟩)
    rw [hy']
    exact n.property ⟨x, hx⟩
  refine ⟨n.val, fun j => ?_⟩
  have he := hglobal j
  change f.toFun j * a j n.val * (g.toFun j)⁻¹ = n.val at he
  change g.toFun j = n.val⁻¹ * f.toFun j * a j n.val
  calc
    g.toFun j = n.val⁻¹ * (f.toFun j * a j n.val * (g.toFun j)⁻¹) * g.toFun j := by rw [he]; group
    _ = n.val⁻¹ * f.toFun j * a j n.val := by group

end LocalConjugacy
