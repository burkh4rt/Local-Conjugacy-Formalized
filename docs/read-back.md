# Read-back against arXiv:2609.37678v1

This is the agent's second-pass comparison, performed on 2026-09-30 against the
actual source downloaded from <https://arxiv.org/src/2609.37678v1>, not merely
against the older local manuscript or its previous review notes. It is not an
independent human review. Michael C. Burkhart's planned verification of the
definitions and theorem statements remains pending.

The unmodified TeX is `sources/local-conjugacy-prosolvable-re.tex`, SHA-256
`022b7c53635f6e18b93bbc60191e7c9c28288b0f813124e3365b5025722b67b9`. The original
downloaded archive is also included. The TeX contains eleven numbered results:
one Theorem, one Lemma, two Corollaries, and seven Propositions. The two
counterexamples occur in the Introduction. All thirteen are selected in
`comparator.json`; the definition of each selected statement is visible in
`Challenge.lean`, whose only import is Mathlib.

## Statement-by-statement comparison

The line numbers below refer to the exact TeX snapshot. All Lean names have
prefix `LocalConjugacy.`. “Matches” means the mathematical statement matches
under the conventions explained below, not that an independent expert has
approved it.

| Preprint                  | Source line | Lean declaration            | Read-back                                                                                                                                                                                                                                                                                                                       |
| ------------------------- | ----------: | --------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Theorem 1.1               |          70 | `theorem_1_1`               | Matches: arbitrary profinite G; closed normal pronilpotent N; both closed supplements; either G prosupersolvable or G/N pronilpotent; conjugacy iff local conjugacy. No finite-N restriction.                                                                                                                                   |
| Lemma 1.2                 |          90 | `lemma_1_2`                 | Matches: profinite J, finite discrete nilpotent coefficient group with continuous action; either NJ prosupersolvable or J pronilpotent; simultaneous restriction is bijective onto the full product of stable classes indexed by π(J). Preservation of the distinguished class is explicitly conjoined in the compared theorem. |
| Corollary 1.3             |          97 | `corollary_1_3`             | Matches: internal semidirect product of closed factors, pronilpotent N, the same structural alternative, and N∩H normal in N. A possibly different ambient conjugator and Sylow subgroup is allowed for every prime. The conclusion is inclusion of a conjugate of J.                                                           |
| Corollary 1.4             |         103 | `corollary_1_4`             | Matches: nonempty transitive G-set with every stabilizer closed, and normal N-stabilizer at some point. Local fixed points may differ with the prime. No topology or continuous-action assumption is imposed on Ω.                                                                                                              |
| Proposition 2.1           |         139 | `proposition_2_1`           | Matches: locally finite, possibly infinite, discrete p-group N; closed normal J₀; closed procyclic pro-p₀ subgroup Q, p₀≠p; Q-stable cocycle. Conclusion gives a cohomologous literally Q-fixed representative trivial on J₀∩Q. The symmetric cohomology relation reverses the paper's displayed ψ∼φ harmlessly.                |
| Proposition 2.2           |         155 | `proposition_2_2`           | Matches: prosolvable J, locally finite discrete p-group N, closed normal J₀ of prime index p₀≠p. The actual restriction on quotient cohomology is bijective onto J-stable classes. Its distinguished-point preservation is proved in the shared definitions.                                                                    |
| Proposition 2.3           |         177 | `proposition_2_3`           | Matches: profinite J, finite discrete p-group N, prosupersolvable NJ, arbitrary Hall subgroup for primes ≤p, and bijectivity onto all H¹(Q,N). The obsolete extra hypothesis `Prosolvable J` was removed from both Challenge and Solution.                                                                                      |
| Proposition 3.1           |         239 | `proposition_3_1`           | Matches: the hypotheses of Theorem 1.1 with finite N and two closed complements. Replaced the older locally-finite/discrete signature with `[Finite N]`. Discreteness is now derived from finiteness and the inherited Hausdorff topology.                                                                                      |
| Proposition 3.2           |         250 | `proposition_3_2`           | Matches: exactly Theorem 1.1 with finite N; G is still allowed to be infinite profinite.                                                                                                                                                                                                                                        |
| Proposition 4.1           |         303 | `proposition_4_1`           | Matches: arbitrary profinite G, closed abelian normal N, two closed supplements H and H′, local inclusion implies inclusion of an ambient conjugate. No solvability or semidirect-product assumption is added.                                                                                                                  |
| Proposition 4.2           |         313 | `proposition_4_2`           | Matches: arbitrary transitive nonempty G-set with closed stabilizers, closed H supplementing closed abelian normal N, local Sylow fixed points imply an H-fixed point.                                                                                                                                                          |
| Quaternion counterexample |          88 | `counterexample_quaternion` | Uses the explicit Q₈ ⋊ S₃ action with a proved isomorphism to GL(2,3); literal cardinality two of the quotient cohomology set; trivial cohomology for every Sylow subgroup at every prime; actual complements locally conjugate at every prime but not conjugate in the ambient group.                                          |
| Heisenberg counterexample |         108 | `counterexample_heisenberg` | Identifies G with the imprimitive C₃ ≀ S₃, N with the three-coordinate Heisenberg group over F₃, J with C₆, and H with C₃×S₃. Proves all four orders, nilpotence of N and J, supersolvability of G, the splitting, local inclusion at every prime, failure of global inclusion, and failure of normality of N∩H in N.           |

## Definition read-back

- `Profinite` is a compact Hausdorff totally disconnected topological group.
  Subgroup topologies are inherited, and closedness hypotheses implement the
  paper's convention H≤G means a closed subgroup. Normality is explicit.
- `Pronilpotent`, `Prosupersolvable`, and `Prosolvable` quantify over all open
  normal quotients. These quotients are finite in a profinite group.
  `Supersolvable` uses a finite invariant normal series with cyclic factors. It
  does not replace supersolvability with solvability.
- `IsProP` is the finite-quotient condition. It permits infinite-order elements
  such as those in Z_p. In contrast, `IsPGroup` is used for the discrete
  algebraic coefficient p-groups in Section 2.
- `IsSylowPro p H P` means P is a closed pro-p subgroup of H maximal among such
  subgroups. Both P and H are represented inside the ambient group. `IsHallPro`
  is closedness and the ordinary order/index Hall condition in every finite
  quotient. Its cutoff is tested only at primes, so `{r | r≤p}` encodes precisely
  the paper's π. Every prime is included in local conjugacy, local inclusion, and
  local fixed-point assertions.
- `Supplements N H` is the setwise equality NH=G, not merely dense generation.
  `Splits N J` additionally requires N normal and N∩J=1. With closed factors in a
  profinite group this is the internal topological semidirect product.
  `IntersectionNormal N H` states normality in N, the important hypothesis
  exhibited by the Heisenberg counterexample.
- `conjugate g H` means gHg⁻¹. The preprint's H^g therefore corresponds to
  `conjugate g⁻¹ H`. Existential conjugacy and inclusion claims are unchanged.
  The paper's n^(j⁻¹) is `j • n`. Thus the equations for cocycles, coboundaries,
  twists, and stable elements agree after this change of convention.
- `Cocycle` includes continuity. `Cohomologous` uses one global n for all x; it
  is not pointwise conjugacy. `H1` is the actual quotient by this equivalence
  relation. Stable classes compare on K∩jKj⁻¹, rather than incorrectly assuming a
  Sylow subgroup is normal. A class needs a stable representative, not a
  representative fixed literally by all twists.
- `PrimeDivisor J` is π(J), the primes dividing some finite continuous quotient
  of J. The target in Lemma 1.2 is the entire product, not a finite-support sum
  or the image of restriction by definition. `primaryRestriction` is the literal
  tuple of restriction maps. Its bijectivity is proved.
- In finite examples, `FiniteH1` is the same cocycle/coboundary quotient with
  continuity omitted because every group is finite discrete. `DihedralGroup 3` is
  the order-six presentation of S₃ (not the order-three cyclic group), and
  `QuaternionGroup 2` is Q₈. The wreath action is the natural action on three
  coordinates, so its order is 162, not the regular wreath product's order.
  `Heisenberg3` has law (a,b,c)(a′,b′,c′)=(a+a′,b+b′,c+c′+ab′), the upper
  unitriangular 3×3 matrix law. The isomorphism with N is explicit.

## Changes from the reused package and remaining proof differences

The formalized Proposition 3.1 now has finite N, and Proposition 2.3 no longer
has a separate prosolvability hypothesis. V1 also repairs the old N_p notation in
Proposition 2.3, the class-level invariance argument at the end of Lemma 1.2, and
several compactness and finite-index explanations. The old manuscript issue list
was deliberately not copied as if those issues remained current.

The two Zorn arguments, finite-kernel induction, and compactness through G/(N∩U)
follow the preprint. Supporting lemmas make continuity and descent steps
explicit. Proposition 2.2 expands the twisting/fiber argument instead of citing
an unformalized inflation–restriction theorem. Proposition 4.1 proves its abelian
complement input by a finite-quotient cocycle norm argument instead of assuming
the result cited from Shin. Proposition 4.2, which has no separate proof printed
in v1, is proved using Proposition 4.1 and a closed point stabilizer. See the
correspondence guide for the files.

The formal proof chooses a stabilizer satisfying the normality assumption in
Corollary 1.4 and uses ambient G-conjugators, which the statement allows.
Prime-index reductions require a prime different from p without asserting it is
the smallest; the needed normality and subgroup containment are proved. These are
proof elaborations, not stronger hypotheses in the stated results.

No statement-level scope gap is known after this read-back. This assessment must
still be checked by the source author. Compilation, compiled-type comparison, and
the transitive axiom audit are recorded separately and do not certify
mathematical fidelity or replace Palomar's independent verification.
