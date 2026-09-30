module

public import LocalConjugacy.StableCocycles

@[expose] public section

namespace LocalConjugacy

section Products
variable {J : Type*} [Group J] [TopologicalSpace J]
  {ι : Type*} {N : ι → Type*} [∀ i, Group (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, MulDistribMulAction J (N i)]

namespace Cocycle

def component {K : Subgroup J} (f : Cocycle (N := ∀ i, N i) K) (i : ι) :
    Cocycle (N := N i) K where
  toFun x := f.toFun x i
  continuous_toFun := (continuous_apply i).comp f.continuous_toFun
  map_mul x y := congrFun (f.map_mul x y) i

def pi {K : Subgroup J} (f : ∀ i, Cocycle (N := N i) K) :
    Cocycle (N := ∀ i, N i) K where
  toFun x i := (f i).toFun x
  continuous_toFun := continuous_pi fun i => (f i).continuous_toFun
  map_mul x y := funext fun i => (f i).map_mul x y

end Cocycle

theorem cohomologous_pi_iff {K : Subgroup J} (f g : Cocycle (N := ∀ i, N i) K) :
    Cohomologous f g ↔ ∀ i, Cohomologous (f.component i) (g.component i) := by
  constructor
  · rintro ⟨n, hn⟩ i
    exact ⟨n i, fun x => congrFun (hn x) i⟩
  · intro h
    choose n hn using h
    exact ⟨n, fun x => funext fun i => hn i x⟩

theorem invariant_pi_iff {L K : Subgroup J} (f : Cocycle (N := ∀ i, N i) K) :
    InvariantUnder L K f ↔ ∀ i, InvariantUnder L K (f.component i) := by
  constructor
  · intro h i j hj
    obtain ⟨n, hn⟩ := h j hj
    exact ⟨n i, fun x hx hjx => congrFun (hn x hx hjx) i⟩
  · intro h j hj
    choose n hn using fun i => h i j hj
    exact ⟨n, fun x hx hjx => funext fun i => hn i x hx hjx⟩

theorem primaryDecomposition_pi (P : PrimeDivisor J → Subgroup J)
    (h : ∀ i, PrimaryDecomposition (N := N i) P) :
    PrimaryDecomposition (N := ∀ i, N i) P := by
  classical
  refine ⟨primary_restriction_is_stable P, ?_, ?_⟩
  · intro f g hr
    apply (cohomologous_pi_iff f g).mpr
    intro i
    apply (h i).2.1 (f.component i) (g.component i)
    intro p
    obtain ⟨n, hn⟩ := hr p
    exact ⟨n i, fun x => congrFun (hn x) i⟩
  · intro f hf
    have hi (i : ι) : ∃ g : Cocycle (N := N i) (⊤ : Subgroup J),
        ∀ p, RestrictsTo (show P p ≤ ⊤ from le_top) g ((f p).component i) :=
      (h i).2.2 (fun p => (f p).component i)
        (fun p => (invariant_pi_iff (f p)).mp (hf p) i)
    choose g hg using hi
    refine ⟨Cocycle.pi g, fun p => ?_⟩
    choose n hn using fun i => hg i p
    exact ⟨n, fun x => funext fun i => hn i x⟩

end Products

section Coefficients
variable {J N M : Type*} [Group J] [Group N] [Group M]
  [TopologicalSpace J] [TopologicalSpace N] [TopologicalSpace M]
  [MulDistribMulAction J N] [MulDistribMulAction J M]

namespace Cocycle

def mapCoefficient {K : Subgroup J} (f : Cocycle (N := N) K)
    (e : N →* M) (he : Continuous e) (ha : ∀ (j : J) (n : N), e (j • n) = j • e n) :
    Cocycle (N := M) K where
  toFun x := e (f.toFun x)
  continuous_toFun := he.comp f.continuous_toFun
  map_mul x y := by rw [f.map_mul, e.map_mul, ha]

end Cocycle

theorem cohomologous_mapCoefficient {K : Subgroup J} {f g : Cocycle (N := N) K}
    (h : Cohomologous f g) (e : N →* M) (he : Continuous e)
    (ha : ∀ (j : J) (n : N), e (j • n) = j • e n) :
    Cohomologous (f.mapCoefficient e he ha) (g.mapCoefficient e he ha) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨e n, fun x => ?_⟩
  change e (g.toFun x) = _
  rw [hn, e.map_mul, e.map_mul, e.map_inv, ha]
  rfl

theorem invariant_mapCoefficient {L K : Subgroup J} {f : Cocycle (N := N) K}
    (h : InvariantUnder L K f) (e : N →* M) (he : Continuous e)
    (ha : ∀ (j : J) (n : N), e (j • n) = j • e n) :
    InvariantUnder L K (f.mapCoefficient e he ha) := by
  intro j hj
  obtain ⟨n, hn⟩ := h j hj
  refine ⟨e n, fun x hx hjx => ?_⟩
  change j • e (f.toFun ⟨j⁻¹ * x * j, hjx⟩) = _
  rw [← ha, hn, e.map_mul, e.map_mul, e.map_inv, ha]
  rfl

/-- Transport primary decomposition across an equivariant continuous group
isomorphism of the coefficient groups. -/
theorem primaryDecomposition_of_equiv (P : PrimeDivisor J → Subgroup J)
    (e : N ≃* M) (he : Continuous e) (hei : Continuous e.symm)
    (ha : ∀ (j : J) (n : N), e (j • n) = j • e n)
    (h : PrimaryDecomposition (N := M) P) : PrimaryDecomposition (N := N) P := by
  have hai (j : J) (m : M) : e.symm (j • m) = j • e.symm m := by
    apply e.injective
    rw [e.apply_symm_apply, ha, e.apply_symm_apply]
  refine ⟨primary_restriction_is_stable P, ?_, ?_⟩
  · intro f g hr
    have hh := h.2.1 (f.mapCoefficient e.toMonoidHom he ha)
      (g.mapCoefficient e.toMonoidHom he ha) (fun p => by
        obtain ⟨n, hn⟩ := hr p
        refine ⟨e n, fun x => ?_⟩
        change e (g.toFun ⟨x, trivial⟩) = (e n)⁻¹ * e (f.toFun ⟨x, trivial⟩) * ((x : J) • e n)
        rw [hn x, e.map_mul, e.map_mul, e.map_inv, ha])
    obtain ⟨n, hn⟩ := hh
    refine ⟨e.symm n, fun x => ?_⟩
    apply e.injective
    have hx := hn x
    change e (g.toFun x) = n⁻¹ * e (f.toFun x) * ((x : J) • n) at hx
    simpa only [map_mul, map_inv, ha, e.apply_symm_apply] using hx
  · intro f hf
    obtain ⟨g, hg⟩ := h.2.2 (fun p => (f p).mapCoefficient e.toMonoidHom he ha)
      (fun p => invariant_mapCoefficient (hf p) e.toMonoidHom he ha)
    refine ⟨g.mapCoefficient e.symm.toMonoidHom hei hai, fun p => ?_⟩
    obtain ⟨n, hn⟩ := hg p
    refine ⟨e.symm n, fun x => ?_⟩
    have hh := congrArg e.symm (hn x)
    simpa only [Cocycle.mapCoefficient, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.symm_apply_apply, map_mul, map_inv, hai] using hh

end Coefficients
end LocalConjugacy
