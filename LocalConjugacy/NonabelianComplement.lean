module

public import LocalConjugacy.AbelianComplement
public import LocalConjugacy.NilpotentCoefficients

@[expose] public section

namespace LocalConjugacy
namespace NonabelianComplement
open AbelianComplement

section Algebra
variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)

/-- The order of the two factors matters for nonabelian coefficients. -/
theorem projection_mul_reverse (x y : G) :
    projection N H hc (x * y) =
      MulAut.conjNormal x (projection N H hc y) * projection N H hc x := by
  let nx := projection N H hc x
  let ny := projection N H hc y
  let hx : H := (hc.equiv x).2
  let hy : H := (hc.equiv y).2
  have hxe : (nx : G) * hx = x := hc.equiv_fst_mul_equiv_snd x
  have hye : (ny : G) * hy = y := hc.equiv_fst_mul_equiv_snd y
  have he : ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) = x * y := by
    change (x * ny * x⁻¹ * nx) * (hx * hy) = x * y
    calc
      (x * ny * x⁻¹ * nx) * (hx * hy) = x * ny * x⁻¹ * ((nx : G) * hx) * hy := by group
      _ = x * y := by rw [hxe, ← hye]; group
  have hf := congrArg (fun z => (hc.equiv z).1) he
  rw [show ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) =
      hc.equiv.symm (MulAut.conjNormal x ny * nx, hx * hy) from rfl,
    hc.equiv.apply_symm_apply] at hf
  exact hf.symm

/-- A conjugate inclusion gives a coboundary for the inverse projection cocycle. -/
theorem local_coboundary (S : Subgroup G) (g : G) (hg : conjugate g S ≤ H) :
    ∃ n : N, ∀ x : S,
      1 = n⁻¹ * (projection N H hc x)⁻¹ * MulAut.conjNormal (x : G) n := by
  let b := projection N H hc g⁻¹
  refine ⟨b⁻¹, fun x => ?_⟩
  have hm : g * x * g⁻¹ ∈ H := hg (Subgroup.mem_map_of_mem _ x.property)
  have he : (x : G) * g⁻¹ = g⁻¹ * (g * x * g⁻¹) := by group
  have hf : MulAut.conjNormal (x : G) b * projection N H hc x = b := by
    rw [← projection_mul_reverse N H hc, he, projection_mul_right N H hc g⁻¹ hm]
  have h' : MulAut.conjNormal (x : G) b = b * (projection N H hc x)⁻¹ := by
    calc
      MulAut.conjNormal (x : G) b =
          (MulAut.conjNormal (x : G) b * projection N H hc x) * (projection N H hc x)⁻¹ := by group
      _ = _ := by rw [hf]
  rw [inv_inv, map_inv, h']
  group

theorem inclusion_of_coboundary (K : Subgroup G) (n : N)
    (hn : ∀ x : K, 1 = n⁻¹ * (projection N H hc x)⁻¹ * MulAut.conjNormal (x : G) n) :
    conjugate (n : G) K ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  have h := congrArg Subtype.val (hn ⟨x, hx⟩)
  change (1 : G) = (n : G)⁻¹ * (projection N H hc x : G)⁻¹ * (x * n * x⁻¹) at h
  have he : (projection N H hc x : G)⁻¹ * x = (n : G) * x * (n : G)⁻¹ := by
    have hh := congrArg (fun z : G => (n : G) * z * x * (n : G)⁻¹) h
    group at hh
    simpa only [zpow_neg_one] using hh.symm
  have hmem : (projection N H hc x : G)⁻¹ * x ∈ H := by
    have hh := hc.equiv_fst_mul_equiv_snd x
    change (projection N H hc x : G) * ((hc.equiv x).2 : G) = x at hh
    have hy := congrArg (fun z : G => (projection N H hc x : G)⁻¹ * z) hh
    simp only [inv_mul_cancel_left] at hy
    rw [← hy]
    exact (hc.equiv x).2.property
  change (n : G) * x * (n : G)⁻¹ ∈ H
  rwa [he] at hmem

end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
  (N H : Subgroup G) [N.Normal] (hc : Subgroup.IsComplement' N H)
  (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))

include hN hH in
theorem continuous_projection : Continuous (projection N H hc) := by
  letI := profinite_closed_subgroup N hN
  letI := profinite_closed_subgroup H hH
  have hm : Continuous hc.equiv.symm :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have he : Continuous hc.equiv :=
    (hm.isClosedMap.isQuotientMap hm hc.equiv.symm.surjective).continuous_iff.mpr
      (continuous_id.congr (fun x => (hc.equiv.apply_symm_apply x).symm))
  exact continuous_fst.comp he

@[instance_reducible] def conjugationAction (N : Subgroup G) [N.Normal] : MulDistribMulAction G N :=
  MulDistribMulAction.compHom N (MulAut.conjNormal : G →* MulAut N)

attribute [local instance] conjugationAction

instance conjugationContinuousSMul (N : Subgroup G) [N.Normal] : ContinuousSMul G N where
  continuous_smul := (((continuous_fst : Continuous (Prod.fst : G × N → G)).mul
    (continuous_subtype_val.comp continuous_snd)).mul continuous_fst.inv).subtype_mk _

noncomputable def inverseCocycle (K : Subgroup G) : Cocycle (J := K) (N := N) ⊤ where
  toFun x := (projection N H hc (x : K))⁻¹
  continuous_toFun := ((continuous_projection N H hc hN hH).comp
    (continuous_subtype_val.comp continuous_subtype_val)).inv
  map_mul x y := by
    change (projection N H hc ((x : G) * y))⁻¹ = _
    rw [projection_mul_reverse N H hc, mul_inv_rev, ← map_inv]
    rfl

include hc hN hH

/-- The complement/cocycle argument in Proposition 3.1, with its exact
primary-decomposition input isolated. -/
theorem local_inclusion_of_primary (K : Subgroup G) (hK : IsClosed (K : Set G))
    (hloc : LocallyContains H K)
    (hprimary : ∀ (P : PrimeDivisor K → Subgroup K),
      (∀ p, IsSylowPro p.val.val ⊤ (P p)) → PrimaryDecomposition (N := N) P) :
    ∃ n : N, conjugate (n : G) K ≤ H := by
  classical
  letI := profinite_closed_subgroup K hK
  choose S hS g hg using fun p : PrimeDivisor K => hloc p.val.val p.val.property
  let P : PrimeDivisor K → Subgroup K := fun p => (S p).subgroupOf K
  have hP (p : PrimeDivisor K) : IsSylowPro p.val.val ⊤ (P p) :=
    isSylowPro_subgroupOf K (S p) hK (hS p)
  let f := inverseCocycle N H hc hN hH K
  have hcoh : Cohomologous f (trivialCocycle ⊤) := by
    apply (hprimary P hP).2.1
    intro p
    obtain ⟨n, hn⟩ := local_coboundary N H hc (S p) (g p) (hg p)
    refine ⟨n, fun x => ?_⟩
    exact hn ⟨x, x.property⟩
  obtain ⟨n, hn⟩ := hcoh
  refine ⟨n, inclusion_of_coboundary N H hc K n (fun x => ?_)⟩
  exact hn ⟨x, trivial⟩

/-- The local-inclusion form of the complement theorem when the acting
subgroup is pronilpotent and the normal coefficient subgroup is finite. -/
theorem local_inclusion_of_pronilpotent [Finite N] [DiscreteTopology N]
    (hpronN : Pronilpotent N) (K : Subgroup G) (hK : IsClosed (K : Set G))
    (hpronK : Pronilpotent K) (hloc : LocallyContains H K) :
    ∃ n : N, conjugate (n : G) K ≤ H := by
  letI := profinite_closed_subgroup K hK
  exact local_inclusion_of_primary N H hc hN hH K hK hloc
    (fun P hP => lemma_1_2_of_pronilpotent hpronN hpronK P hP)

end Topology
end NonabelianComplement
end LocalConjugacy
