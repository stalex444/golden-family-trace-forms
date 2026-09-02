# The trace form of a tensor product of algebras, and the trace forms of ℚ[x]/(x³ − x − 1), ℚ[x]/(x⁴ − x − 1) and their compositum

Seven general theorems, kernel-checked in Lean 4 + Mathlib: the trace form
of a tensor product of finite free algebras is the tensor product of the
trace forms; the discriminant of a tensor basis is the signed product
formula; and over a linearly ordered field the Sylvester signature of a
tensor product of quadratic forms obeys the product rule
`(p₁p₂ + n₁n₂, p₁n₂ + n₁p₂)`. Then sixteen instances at the two
golden-family fields and their compositum: Gram matrices, discriminants
−23 and −283, signatures (2,1) and (3,1), and the compositum's trace form
with signature (7,5) and discriminant (−23)⁴·(−283)³, derived from the
general theorems.

## The twenty-three compared statements

All in `Challenge.lean` (Mathlib vocabulary only, `sorry`-proved as the
comparison surface) and proved in `Solution.lean` by transfer from the
seven proof modules. Namespace `TraceForms`.

### General theorems (1)–(7)

Throughout, `R` is a commutative ring and `A`, `B` are commutative
`R`-algebras that are free and finite as `R`-modules.

| # | theorem | statement |
|---|---|---|
| 1 | `trace_tmul` | `Tr_{A ⊗ B}(a ⊗ b) = Tr_A(a) · Tr_B(b)` |
| 2 | `traceForm_tmul` | `⟨a ⊗ b, a' ⊗ b'⟩_{A ⊗ B} = ⟨a, a'⟩_A · ⟨b, b'⟩_B` |
| 3 | `traceMatrix_tensorProduct` | the trace matrix of a tensor basis `bA ⊗ bB` is the Kronecker product of the trace matrices |
| 4 | `discr_tensorProduct` | for finite index types, `disc(bA ⊗ bB) = disc(bA)^|κ| · disc(bB)^|ι|`, with sign |
| 5 | `traceForm_toQuadraticMap_tensor` | with 2 invertible in `R`: the trace quadratic form of `A ⊗ B` is `QuadraticForm.tmul` of the trace quadratic forms |
| 6 | `sigPos_tmul` | over a linearly ordered field with 2 invertible, finite-dimensional `V`, `W`: `sigPos(Q₁ ⊗ Q₂) = p₁p₂ + n₁n₂` |
| 7 | `sigNeg_tmul` | `sigNeg(Q₁ ⊗ Q₂) = p₁n₂ + n₁p₂` |

`sigPos` and `sigNeg` are Mathlib's basis-free Sylvester invariants of a
quadratic form over an ordered field, the maximal dimensions of a
positive- and a negative-definite subspace. Statements 6–7 are the
`(p, n)`-refinement of the classical fact that the signature is
multiplicative on the Witt ring of an ordered field (Lam 2005, Chapter
VIII), stated for arbitrary, possibly degenerate forms. The Witt-ring
statement gives only the difference `p − n`; recovering `p` and `n`
separately for a possibly degenerate tensor product would also need the
dimension of the radical of a tensor product, which Mathlib does not have
either. The entry proves the two counts directly, without the Witt ring. None of 1–7 is in
Mathlib at the pin; they are built from Mathlib's trace of a tensor
product of endomorphisms, tensor bases, the determinant of a Kronecker
product, the tensor product of quadratic forms, orthogonal bases, and the
uniqueness half of Sylvester's law.

### Instances at the two fields (8)–(17)

`K₃ = ℚ[x]/(x³ − x − 1)` and `K₄ = ℚ[x]/(x⁴ − x − 1)`; the trace matrix in
the power basis is the Hankel matrix of the power sums of the roots.

| # | theorem | statement |
|---|---|---|
| 8 | `traceMatrix_cubic` | trace matrix of `1, x, x²` in `K₃` is `!![3,0,2; 0,2,3; 2,3,2]` |
| 9 | `traceMatrix_quartic` | trace matrix of `1, x, x², x³` in `K₄` is `!![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]` |
| 10 | `discr_cubic` | `Algebra.discr` of the cubic power family is `−23` |
| 11 | `discr_quartic` | `Algebra.discr` of the quartic power family is `−283` |
| 12 | `traceForm_cubic_equiv` | the cubic trace form is equivalent to the weighted sum of squares with weights `3, 2, −23/6` |
| 13 | `traceForm_quartic_equiv` | the quartic trace form is equivalent to the weighted sum of squares with weights `4, 4, −9/4, 283/36` |
| 14 | `sigPos_cubic` | `sigPos` of the trace form of `K₃` is 2 |
| 15 | `sigNeg_cubic` | `sigNeg` of the trace form of `K₃` is 1 |
| 16 | `sigPos_quartic` | `sigPos` of the trace form of `K₄` is 3 |
| 17 | `sigNeg_quartic` | `sigNeg` of the trace form of `K₄` is 1 |

### Instances at the compositum (18)–(23)

| # | theorem | statement |
|---|---|---|
| 18 | `trace_tmul_compositum` | in `K₃ ⊗[ℚ] K₄`, `Tr(x ⊗ y) = Tr(x) · Tr(y)` |
| 19 | `traceMatrix_compositum` | the trace matrix of the tensor power family `xⁱ ⊗ yʲ` is the Kronecker product of the two Hankel matrices |
| 20 | `discr_compositum` | `Algebra.discr ℚ (xⁱ ⊗ yʲ) = (−23)⁴ · (−283)³` |
| 21 | `sigPos_compositum` | `sigPos` of the trace form of `K₃ ⊗[ℚ] K₄` is 7 |
| 22 | `sigNeg_compositum` | `sigNeg` of the trace form of `K₃ ⊗[ℚ] K₄` is 5 |
| 23 | `isField_compositum` | `K₃ ⊗[ℚ] K₄` is a field (the compositum `ℚ(ρ, Q)`, degree 12) |

In the Solution, 20–22 are derived from the general theorems 4, 6 and 7
and the factor data 10–11 and 14–17: `(7, 5) = (2·3 + 1·1, 2·1 + 1·3)`.

## The classical setting, and what is not formalized

The trace form of a number field with `r₁` real and `r₂` pairs of complex
embeddings has signature `(r₁ + r₂, r₂)`: for the Hankel form of a
polynomial this is Hermite's 1856 theorem (the signature difference counts
the distinct real roots), and for the discriminant matrix of a number
field it is Taussky's 1968 note; Conner and Perlis's 1984 survey is the
standard reference. Here `(r₁, r₂) = (1, 1)`, `(2, 1)` and `(2, 5)`, so
the classical theorem predicts exactly `(2, 1)`, `(3, 1)` and `(7, 5)`,
and the Hermite counts `2 − 1 = 1` and `3 − 1 = 2` match the real-root
counts of the two trinomials. That general theorem is **not** formalized;
the two-field instances are proved by explicit congruence and the
compositum instance by the general theorems. The embedding counts appear
in no compared statement.

The power-basis discriminants 10–11 are the field discriminants because
both fields are monogenic (LMFDB records 3.1.23.1 and 4.2.283.1, cited);
the tensor power family is an integral basis of the compositum because
the two discriminants are coprime (the standard integral-basis theorem for
linearly disjoint fields). Both identifications are context, not
formalized. Statement 20 is the discriminant of the family.

## Why these two fields

The cubic field is the cubic field of smallest absolute discriminant
among those with one real place: in the LMFDB's list of signature-`[1,1]`
cubic fields sorted by `|disc|`, 3.1.23.1 (discriminant −23) comes first,
then 3.1.31.1 (−31). Its Galois closure is the Artin field of the
weight-one newform [23.1.b.a](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/23/1/b/a/)
`= η(z)η(23z)`, the classical Hecke example of a weight-one cusp form
with Artin image `S₃`; the LMFDB records its analytic conductor as
minimal among all classical newforms and its Stark unit as the root of
`x³ − x − 1` itself. Its integral trace form — which the Gram matrix 8 is,
the power basis being an integral basis — is the object of the research
line on integral trace forms of cubic fields opened by Mantilla-Soler
(Algebra & Number Theory, 2010). The quartic field is the degree-four
member of the same trinomial family, registered as the degree-four
Mahler-measure minimizer (PALOMAR-2026-08-31-000004), with the same
profile: prime discriminant, monogenic. The compositum is the field the
registered entry PALOMAR-2026-09-01-000005 treats as `ℚ(ρQ)` through the
degree-12 minimal polynomial of the product; that `ℚ(ρ, Q) = ℚ(ρQ)` is a
degree count and is context here.

## Prior art

Mathlib at the pin supplies the infrastructure the statements are
built from — `Algebra.traceForm`, `Algebra.traceMatrix`, `Algebra.discr`
with `discr_def`, `LinearMap.trace_tensorProduct'`, `Basis.tensorProduct`,
`Matrix.det_kronecker`, `QuadraticForm.tmul` with `tensorDistrib_tmul`
and `associated_tmul`, `LinearMap.BilinForm.exists_orthogonal_basis`,
`IntermediateField.LinearDisjoint.of_finrank_coprime`, and `sigPos`,
`sigNeg` with `sigPos_of_equiv_weightedSumSquares` — but none of the
general theorems 1–7 and no trace-form or discriminant computation for
either field.

**Disclosed prior art on statement 4.** Mathlib at the pin holds
`NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`: for
two linearly disjoint number fields with coprime different ideals, the
absolute value of the discriminant of their compositum is
`|d₁|^[K₂:ℚ] · |d₂|^[K₁:ℚ]`, proved through the different (the classical
statement is Khanduja 2019). Statement 4 is the basis-level version with
sign, for arbitrary finite free algebras over any commutative ring, with
no number-field, integrality or coprimality hypothesis. The two are
different statements; neither implies the other, and the Mathlib theorem
is not used here.

**On the instances.** The nearest prior work is the Lean 4 certification
framework of Baanen, Chavarri Villarello and Dahmen (CPP 2025) and its
2026 sequel (Chavarri Villarello and Dahmen): they certify rings of
integers and field discriminants, then signatures `(r₁, r₂)` by
real-root counting, unit groups and class groups, for LMFDB entries at
large. Neither treats the trace form's Sylvester signature, and their
published example sets (seven non-monogenic cubic fields unramified
outside 2, 3, 5 in the first; the v1 example directory of the second)
contain neither of the two fields here (checked 2026-09-02). Relative to
that work, the compared discriminants 10–11 are power-basis discriminants
derived from the explicit Gram matrices, a weaker notion than the
certified field discriminant, which coincides with it here because both
fields are monogenic (LMFDB, cited). As of the 2026-09-02 sweep the entry
is not aware of a formalization, in any surveyed prover ecosystem, of the
trace form of a tensor product of algebras, of the signature product rule,
or of a number field's trace-form Sylvester signature.

## Verify it

```
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.31.0`; Mathlib pinned at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. `#print axioms` on each of
the twenty-three compared theorems returns exactly
`[propext, Classical.choice, Quot.sound]`; the audit was also run over
every theorem of the proof modules (all 51 theorems of `PdtTraceLink`,
which has 57 declarations, the six others being definitions; all
theorems of `PdtTraceSignature`; all 29 theorems and lemmas of
`PdtTraceCompositum`; all 19 declarations of `PdtTraceTensor`). The only
`sorry` in the repository are the twenty-three placeholders of
`Challenge.lean`, which are the comparison surface by construction.

## Repository layout

| file | content |
|---|---|
| `Challenge.lean` | the twenty-three compared statements, Mathlib-only, `sorry`-proved |
| `Solution.lean` | proofs of the twenty-three statements by transfer from the proof modules |
| `PdtTraceTensor.lean` | the seven general theorems (1)–(7) and the compositum instance as their corollary |
| `PdtSignature.lean` | the quartic Gram matrix `M`, `det M = −283`, the explicit congruence `Pᵀ M P = D`, `D = diag(4, 4, −9/4, 283/36)` |
| `PdtSignatureRho.lean` | the cubic Gram matrix `Mρ`, `det Mρ = −23`, `Pρᵀ Mρ Pρ = Dρ`, `Dρ = diag(3, 2, −23/6)` |
| `PdtIrreducible.lean` | irreducibility of `x³ − x − 1` and `x⁴ − x − 1` over ℚ by reduction modulo 2 (consumed only by statement 23) |
| `PdtTraceLink.lean` | `M` and `Mρ` are the trace matrices of the power families; `Algebra.discr` of the power bases is `−283` and `−23` |
| `PdtTraceSignature.lean` | the trace forms as quadratic forms, the isometries to weighted sums of squares, and `sigPos`/`sigNeg` |
| `PdtTraceCompositum.lean` | the compositum: `Tr(x ⊗ y) = Tr(x)Tr(y)`, the Kronecker Gram matrix, the discriminant, the orthogonal tensor basis and the `(7, 5)` signature, and the field property |
| `comparator.json` | the twenty-three compared names, `Challenge` → `Solution` |
| `formalization.yaml` | metadata, sources, alignment of each statement to its source, fidelity notes |

## Provenance

The seven proof modules live in the author's public
[pdt-lean](https://github.com/stalex444/pdt-lean) development and are
copied here byte-for-byte from its revision
`add583f3a7fc465a7fa78e2a236fe728ea9ec850`. Three of them predate this
entry there: `PdtSignature`, `PdtSignatureRho` and `PdtIrreducible`
(June 2026). The other four, `PdtTraceLink`, `PdtTraceSignature`,
`PdtTraceCompositum` and `PdtTraceTensor`, were written for this entry
on 2026-09-02, developed and committed in pdt-lean at that revision, and
then copied here. This repository is a complete, self-contained proof
development for the compared statements, not a wrapper: every compared
theorem is proved from Mathlib within these files.

Three registered entries of the author touch the same two fields and are
cited as context, never re-compared: PALOMAR-2026-08-19-000007 (pdt-lean,
whose compared content is quantum kinematics), PALOMAR-2026-09-01-000005
(the compositum's minimal polynomial, conjugate census and unit-ness of
`ρQ`), and PALOMAR-2026-09-01-000012 (the family boundary: `Q` not Pisot,
the real-root picture). None of them compares a trace form, a
discriminant, a signature, or any tensor-product statement.

## Sources

- Ch. Hermite, *Extrait d'une lettre … sur le nombre des racines d'une
  équation algébrique comprises entre des limites données*, J. reine
  angew. Math. 52 (1856), 39–51.
  [doi:10.1515/crll.1856.52.39](https://doi.org/10.1515/crll.1856.52.39)
- O. Taussky, *The discriminant matrices of an algebraic number field*,
  J. London Math. Soc. 43 (1968), 152–154.
  [doi:10.1112/jlms/s1-43.1.152](https://doi.org/10.1112/jlms/s1-43.1.152)
- J. J. Sylvester, *A demonstration of the theorem that every
  homogeneous quadratic polynomial is reducible by real orthogonal
  substitutions to the form of a sum of positive and negative squares*,
  Philos. Mag. 4 (1852), 138–142.
  [doi:10.1080/14786445208647087](https://doi.org/10.1080/14786445208647087)
- P. E. Conner and R. Perlis, *A Survey of Trace Forms of Algebraic
  Number Fields*, World Scientific, 1984.
  [doi:10.1142/0066](https://doi.org/10.1142/0066)
- T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate
  Studies in Mathematics 67, AMS, 2005 (Chapter VIII: formally real
  fields and signatures).
- S. K. Khanduja, *The discriminant of compositum of algebraic number
  fields*, Int. J. Number Theory 15 (2019), no. 2, 353–360.
  [doi:10.1142/S1793042119500167](https://doi.org/10.1142/S1793042119500167)
- G. Mantilla-Soler, *Integral trace forms associated to cubic
  extensions*, Algebra & Number Theory 4 (2010), no. 6, 681–699.
  [doi:10.2140/ant.2010.4.681](https://doi.org/10.2140/ant.2010.4.681)
- E. S. Selmer, *On the irreducibility of certain trinomials*, Math.
  Scand. 4 (1956), 287–302.
  [doi:10.7146/math.scand.a-10478](https://doi.org/10.7146/math.scand.a-10478)
- A. Baanen, A. Chavarri Villarello, S. R. Dahmen, *Certifying rings of
  integers in number fields*, CPP 2025.
  [doi:10.1145/3703595.3705874](https://doi.org/10.1145/3703595.3705874)
- A. Chavarri Villarello, S. R. Dahmen, *Formally certifying number
  field invariants*, [arXiv:2607.26230](https://arxiv.org/abs/2607.26230)
  (2026).
- LMFDB, number fields [3.1.23.1](https://www.lmfdb.org/NumberField/3.1.23.1)
  and [4.2.283.1](https://www.lmfdb.org/NumberField/4.2.283.1); newform
  [23.1.b.a](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/23/1/b/a/)
  (`η(z)η(23z)`; Artin field the Galois closure of 3.1.23.1).

## Review note

Self-assessed. This is version 2. Version 1 (sixteen statements, no
general theorem) was reviewed by the registry on 2026-09-02 and blocked
on research interest — "fixed low-degree computations and direct
instances or applications of classical general results" — and on a
Challenge scope docstring that still described an earlier ten-statement
surface. Version 2 answers the first with the seven general theorems,
which are new kernel content, and the second by rewriting the Challenge's
opening account first. Checks applied before this submission: the kernel
build; the axiom audit of every compared theorem and every proof-module
theorem; the mechanical surface gates (names in both Lean files, `sorry`
counts, pins, count words against the comparator, vocabulary); and an
adversarial mock-referee audit of this version's surfaces. That audit
returned three blocking items — the version not yet committed at audit
time, one stale count phrase in the metadata, and a dangling clause in
this note — and two non-blocking ones (a stale module count in the
automation notes; a manifest package name copied from a sibling entry);
all five were resolved before submission. Its assessment of the
mathematics is recorded here as given: the general theorems are new
kernel content, statements 6–7 the most defensible against the
"classical instance" reading, statements 1–5 short generalisations of
library facts.
