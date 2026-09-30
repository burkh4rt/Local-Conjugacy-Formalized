module

public import LocalConjugacy.NilpotentRestriction
public import LocalConjugacy.PronilpotentSylow
public import LocalConjugacy.CocycleDescent
public import LocalConjugacy.PronilpotentZorn

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [Finite N] [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Injectivity in the primary restriction theorem for a pronilpotent acting
group, obtained by simultaneous descent of two cocycles to a finite quotient. -/
theorem pronilpotent_sylow_restriction_injective
    {p : ℕ} [Fact p.Prime] (hJ : Pronilpotent J) (hN : IsPGroup p N)
    (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hr : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) f) (restrictCocycle le_top g)) :
    Cohomologous f g := by
  classical
  let fs : Bool → Cocycle (N := N) (⊤ : Subgroup J) := fun b => if b then g else f
  obtain ⟨U, a, c, ha, hc, hmul⟩ := cocycles_factor_through_finite_quotient fs
  let F := J ⧸ U.toSubgroup
  let π := QuotientGroup.mk' U.toSubgroup
  letI := hJ U
  letI : MulDistribMulAction F N := MulDistribMulAction.compHom N a
  let ff : Cocycle (J := F) (N := N) ⊤ :=
    { toFun := fun x => c false x
      continuous_toFun := continuous_of_discreteTopology
      map_mul := fun x y => hmul false x y }
  let gg : Cocycle (J := F) (N := N) ⊤ :=
    { toFun := fun x => c true x
      continuous_toFun := continuous_of_discreteTopology
      map_mul := fun x y => hmul true x y }
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  have hr' : Cohomologous (restrictCocycle (show S.toSubgroup ≤ ⊤ from le_top) ff)
      (restrictCocycle le_top gg) := by
    obtain ⟨n, hn⟩ := hr
    refine ⟨n, fun x => ?_⟩
    have hx : (x : F) ∈ P.map π := by rw [hS]; exact x.property
    obtain ⟨y, hy, hπy⟩ := hx
    change c true (x : F) = n⁻¹ * c false (x : F) * a (x : F) n
    rw [← hπy, hc true y, hc false y, ha y]
    exact hn ⟨y, hy⟩
  obtain ⟨n, hn⟩ := (finite_nilpotent_sylow_restriction hN S).1 ff gg hr'
  refine ⟨n, fun x => ?_⟩
  have hh := hn ⟨π x, trivial⟩
  change c true (π x) = n⁻¹ * c false (π x) * a (π x) n at hh
  rw [hc true x, hc false x, ha x] at hh
  exact hh

/-- Surjectivity onto stable classes for a pronilpotent acting group and finite
`p`-group coefficients. The input cocycle is descended from the actual chosen
Sylow subgroup, then the finite theorem is inflated. -/
theorem pronilpotent_sylow_restriction_surjective
    {p : ℕ} [Fact p.Prime] (hJ : Pronilpotent J) (hN : IsPGroup p N)
    (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (f : Cocycle (N := N) P) (hinv : InvariantUnder ⊤ P f) :
    ∃ g : Cocycle (N := N) (⊤ : Subgroup J), RestrictsTo le_top g f := by
  letI := sylowPro_normal_of_pronilpotent hJ P hP
  obtain ⟨U, hact, hf⟩ := exists_subgroup_cocycle_openNormal P f
  let F := J ⧸ U.toSubgroup
  let π := QuotientGroup.mk' U.toSubgroup
  let α := MulDistribMulAction.toMulAut J N
  have hk : U.toSubgroup ≤ α.ker := by
    intro u hu
    apply MulEquiv.ext
    exact hact u hu
  let a : F →* MulAut N := QuotientGroup.lift U.toSubgroup α hk
  letI : MulDistribMulAction F N := MulDistribMulAction.compHom N a
  have ha (j : J) (n : N) : π j • n = j • n := rfl
  have hconst := cocycle_constant_on_quotient_fibers P f U hf
  let f' := Cocycle.descend (P := P) (π := π) (ha := ha) (f := f) (hf := hconst)
  have hi : InvariantUnder ⊤ (P.map π) f' := Cocycle.descend_invariant
    (P := P) (π := π) (ha := ha) (f := f) (hf := hconst)
    (QuotientGroup.mk'_surjective U.toSubgroup) hinv
  letI := hJ U
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  have hres : RestrictionIsomorphism (N := N) ⊤ (P.map π) le_top := by
    rw [hS]
    exact finite_nilpotent_sylow_restriction hN S
  obtain ⟨g, n, hn⟩ := hres.2 f' hi
  refine ⟨Cocycle.inflate π continuous_quotient_mk' ha g, n, fun x => ?_⟩
  have hh := hn (subgroupImageHom P π x)
  rw [Cocycle.descend_apply] at hh
  change f.toFun x = n⁻¹ * g.toFun ⟨π x, trivial⟩ * ((π x) • n) at hh
  rw [ha] at hh
  exact hh

/-- The restriction isomorphism used for each primary coefficient factor in
the pronilpotent case of Lemma 1.2, for arbitrary profinite acting groups. -/
theorem pronilpotent_sylow_restriction
    {p : ℕ} [Fact p.Prime] (hJ : Pronilpotent J) (hN : IsPGroup p N)
    (P : Subgroup J) (hP : IsSylowPro p ⊤ P) :
    RestrictionIsomorphism (N := N) ⊤ P le_top := by
  refine ⟨pronilpotent_sylow_restriction_injective_zorn hJ hN P hP, ?_⟩
  intro τ hτ
  obtain ⟨_, φ, hφ⟩ := pronilpotent_sylow_extension_zorn hJ hN P hP τ hτ
  exact ⟨φ, hφ⟩

end LocalConjugacy
