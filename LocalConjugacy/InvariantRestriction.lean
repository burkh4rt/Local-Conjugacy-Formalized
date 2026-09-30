module

public import LocalConjugacy.Cohomology

@[expose] public section

namespace LocalConjugacy

section General

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Conjugation by `j⁻¹` on a normal subgroup, kept in the ambient group. -/
def conjugateDomain (K : Subgroup J) [K.Normal] (j : J) : K →* K where
  toFun x := ⟨j⁻¹ * x * j, by
    simpa using (inferInstance : K.Normal).conj_mem x x.property j⁻¹⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

/-- Conjugation action on cocycles on a normal subgroup. -/
def twistCocycle {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) (j : J) :
    Cocycle (N := N) K where
  toFun x := j • f.toFun (conjugateDomain K j x)
  continuous_toFun := by
    apply Continuous.const_smul
    apply f.continuous_toFun.comp
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  map_mul x y := by
    rw [(conjugateDomain K j).map_mul, f.map_mul, smul_mul', smul_smul, smul_smul]
    congr 1
    change (j * (j⁻¹ * (x : J) * j)) • _ = ((x : J) * j) • _
    simp [mul_assoc]

theorem invariant_iff_twist {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) :
    InvariantUnder (⊤ : Subgroup J) K f ↔ ∀ j : J, Cohomologous f (twistCocycle f j) := by
  constructor
  · intro h j
    obtain ⟨n, hn⟩ := h j (Subgroup.mem_top _)
    exact ⟨n, fun x => hn x x.property (conjugateDomain K j x).property⟩
  · intro h j _
    obtain ⟨n, hn⟩ := h j
    exact ⟨n, fun x hx _ => hn ⟨x, hx⟩⟩

theorem twist_cohomologous {K : Subgroup J} [K.Normal]
    {f g : Cocycle (N := N) K} (h : Cohomologous f g) (j : J) :
    Cohomologous (twistCocycle f j) (twistCocycle g j) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨j • n, fun x => ?_⟩
  change j • g.toFun (conjugateDomain K j x) =
    (j • n)⁻¹ * (j • f.toFun (conjugateDomain K j x)) * ((x : J) • (j • n))
  rw [hn]
  simp only [smul_mul', smul_inv', smul_smul]
  congr 1
  change (j * (j⁻¹ * (x : J) * j)) • n = ((x : J) * j) • n
  simp [mul_assoc]

theorem restrict_twist {K L : Subgroup J} [K.Normal] [L.Normal]
    (hKL : K ≤ L) (f : Cocycle (N := N) L) (j : J) :
    restrictCocycle hKL (twistCocycle f j) = twistCocycle (restrictCocycle hKL f) j := by
  rfl

/-- A bijective equivariant restriction map induces a bijection on the
classes invariant under the ambient group. This is used in Lemma 1.2's
surjectivity argument, without assuming that a representative is fixed. -/
theorem invariant_restriction_isomorphism (L K : Subgroup J) [L.Normal] [K.Normal]
    (hKL : K ≤ L) (hiso : RestrictionIsomorphism (N := N) L K hKL) :
    (∀ f g : Cocycle (N := N) L, InvariantUnder ⊤ L f → InvariantUnder ⊤ L g →
      Cohomologous (restrictCocycle hKL f) (restrictCocycle hKL g) → Cohomologous f g) ∧
    (∀ g : Cocycle (N := N) K, InvariantUnder ⊤ K g →
      ∃ f : Cocycle (N := N) L, InvariantUnder ⊤ L f ∧ RestrictsTo hKL f g) := by
  refine ⟨fun f g _ _ h => hiso.1 f g h, ?_⟩
  intro g hg
  have hgL : InvariantUnder L K g := fun j _ => hg j (Subgroup.mem_top _)
  obtain ⟨f, hf⟩ := hiso.2 g hgL
  refine ⟨f, ?_, hf⟩
  rw [invariant_iff_twist]
  intro j
  apply hiso.1
  change Cohomologous (restrictCocycle hKL f) (restrictCocycle hKL (twistCocycle f j))
  rw [restrict_twist]
  have hfg : Cohomologous (restrictCocycle hKL f) g := hf
  exact cohomologous_trans hfg (cohomologous_trans
    ((invariant_iff_twist g).mp hg j) (cohomologous_symm (twist_cohomologous hfg j)))

end General

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

set_option linter.unusedVariables false

/-- The normal-Sylow invariant-restriction observation, retained as a helper.
It is not Proposition 2.3 of the current manuscript (the Hall restriction result). -/
theorem normal_sylow_invariant_restriction [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N)
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ P : Subgroup J)
    [J₀.Normal] [P.Normal] (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀)
    (hP : IsSylowPro p ⊤ P) (hP₀ : P ≤ J₀)
    (hiso : RestrictionIsomorphism (N := N) J₀ P hP₀) :
    (∀ f g : Cocycle (N := N) J₀, InvariantUnder ⊤ J₀ f → InvariantUnder ⊤ J₀ g →
      Cohomologous (restrictCocycle hP₀ f) (restrictCocycle hP₀ g) → Cohomologous f g) ∧
    (∀ g : Cocycle (N := N) P, InvariantUnder ⊤ P g →
      ∃ f : Cocycle (N := N) J₀, InvariantUnder ⊤ J₀ f ∧ RestrictsTo hP₀ f g) :=
  invariant_restriction_isomorphism J₀ P hP₀ hiso

end LocalConjugacy
