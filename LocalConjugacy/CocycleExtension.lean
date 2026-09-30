module

public import LocalConjugacy.FixedCocycle
public import LocalConjugacy.Supplements

@[expose] public section

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Extend a cocycle on a closed normal subgroup by making it trivial on a
closed supplement. Fixedness and triviality on the intersection are exactly
the compatibility conditions for this construction. -/
theorem extend_fixed_cocycle (K Q : Subgroup J) [K.Normal]
    (hK : IsClosed (K : Set J)) (hQ : IsClosed (Q : Set J)) (hs : Supplements K Q)
    (f : Cocycle (N := N) K)
    (hfix : ∀ q : Q, twistCocycle f q = f)
    (htriv : ∀ (x : J) (_ : x ∈ Q) (hx : x ∈ K), f.toFun ⟨x, hx⟩ = 1) :
    ∃ F : Cocycle (N := N) (⊤ : Subgroup J), restrictCocycle le_top F = f := by
  classical
  have hs' := hs
  choose a ha b hb he using hs'
  let F : J → N := fun j => f.toFun ⟨a j, ha j⟩
  have hval (x : K) (q : Q) : F ((x : J) * q) = f.toFun x := by
    let j : J := (x : J) * q
    let d : K := ⟨(x : J)⁻¹ * a j, K.mul_mem (K.inv_mem x.property) (ha j)⟩
    have hd : (d : J) ∈ Q := by
      have hd' : (x : J)⁻¹ * a j = (q : J) * (b j)⁻¹ := by
        have hh := he j
        change a j * b j = (x : J) * q at hh
        calc
          (x : J)⁻¹ * a j = (x : J)⁻¹ * (a j * b j) * (b j)⁻¹ := by group
          _ = (q : J) * (b j)⁻¹ := by rw [hh]; group
      rw [show (d : J) = (x : J)⁻¹ * a j from rfl, hd']
      exact Q.mul_mem q.property (Q.inv_mem (hb j))
    have hx : (⟨a j, ha j⟩ : K) = x * d := by apply Subtype.ext; dsimp [d]; group
    change f.toFun ⟨a j, ha j⟩ = f.toFun x
    rw [hx, f.map_mul, htriv d hd d.property, smul_one, mul_one]
  have hconj (q : Q) (y : K) :
      f.toFun ⟨(q : J) * y * (q : J)⁻¹,
        (inferInstance : K.Normal).conj_mem y y.property q⟩ = (q : J) • f.toFun y := by
    have hh := congrArg (fun g : Cocycle (N := N) K =>
      g.toFun ⟨(q : J) * y * (q : J)⁻¹,
        (inferInstance : K.Normal).conj_mem y y.property q⟩) (hfix q)
    change (q : J) • f.toFun ⟨(q : J)⁻¹ * ((q : J) * y * (q : J)⁻¹) * q, _⟩ = _ at hh
    have hz : (q : J)⁻¹ * ((q : J) * y * (q : J)⁻¹) * q = y := by group
    simpa only [hz] using hh.symm
  have hmul (j k : J) : F (j * k) = F j * (j • F k) := by
    obtain ⟨x, hx, q, hq, rfl⟩ := hs j
    obtain ⟨y, hy, r, hr, rfl⟩ := hs k
    let z : K := ⟨q * y * q⁻¹, (inferInstance : K.Normal).conj_mem y hy q⟩
    have hm : x * q * (y * r) = (x * (q * y * q⁻¹)) * (q * r) := by group
    rw [hm]
    change F (↑((⟨x, hx⟩ : K) * z) * ↑((⟨q, hq⟩ : Q) * ⟨r, hr⟩)) = _
    rw [hval (⟨x, hx⟩ * z) (⟨q, hq⟩ * ⟨r, hr⟩), f.map_mul]
    dsimp only [z, Subgroup.coe_mk]
    rw [hconj ⟨q, hq⟩ ⟨y, hy⟩, hval ⟨x, hx⟩ ⟨q, hq⟩, hval ⟨y, hy⟩ ⟨r, hr⟩]
    exact congrArg (fun t => f.toFun ⟨x, hx⟩ * t) (mul_smul x q (f.toFun ⟨y, hy⟩)).symm
  letI := profinite_closed_subgroup K hK
  letI := profinite_closed_subgroup Q hQ
  let m : K × Q → J := fun t => (t.1 : J) * t.2
  have hm : Continuous m := (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  have hms : Function.Surjective m := by
    intro j
    obtain ⟨x, hx, q, hq, he⟩ := hs j
    exact ⟨(⟨x, hx⟩, ⟨q, hq⟩), he⟩
  have hcont : Continuous F := hm.isClosedMap.isQuotientMap hm hms |>.continuous_iff.mpr (by
    change Continuous (fun t : K × Q => F ((t.1 : J) * t.2))
    exact (f.continuous_toFun.comp (continuous_fst : Continuous (Prod.fst : K × Q → K))).congr
      (fun t => (hval t.1 t.2).symm))
  let F' : Cocycle (N := N) (⊤ : Subgroup J) :=
    { toFun := fun j => F j
      continuous_toFun := hcont.comp continuous_subtype_val
      map_mul := fun j k => hmul j k }
  refine ⟨F', Cocycle.ext fun x => ?_⟩
  change F x = f.toFun x
  simpa only [Subgroup.coe_one, mul_one] using hval x 1

end LocalConjugacy
