#import "@preview/codelst:2.0.0": sourcecode
#import "@preview/touying:0.5.5": *
#import "@preview/diagraph:0.3.0" : raw-render
#import themes.metropolis: *

#let g_lean_blue = rgb("#0073A3")

#let target_date = datetime(year: 2025, month: 1, day: 15)

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Automated Bit-Level Reasoning in Lean 4],
    author: [Henrik Böving],
    date: target_date.display(),
    institution: [Lean FRO],
  ),
  config-colors(
    primary: g_lean_blue,
    secondary: g_lean_blue,
  ),
  config-common(
    slide-level: 2
  )
)

#title-slide()


= Motivation

== Motivation
#sourcecode(
```c
bool will_add_overflow_64bit(int32_t a, int32_t b) {
    int64_t result = (int64_t)a + (int64_t)b;
    return result < INT32_MIN || result > INT32_MAX;
}

bool will_add_overflow_optimized_b(int32_t a, int32_t b) {
    uint32_t c = (uint32_t)a + (uint32_t)b;
    return ((c ^ a) & (c ^ b)) >> 31;
}
```)

#pagebreak()

#sourcecode(
```lean
def will_add_overflow_64bit (a b : BitVec 32) : Bool :=
  let result := (a.signExtend 64) + (b.signExtend 64)
  let INT32_MAX := 0x7fffffff#32
  let INT32_MIN := (-0x7fffffff#32 - 1#32)
  BitVec.slt result (INT32_MIN.signExtend 64) || BitVec.slt (INT32_MAX.signExtend 64) result

def will_add_overflow_optimized_b (a b : BitVec 32) : Bool :=
  let c := a + b
  BitVec.getLsbD (((c ^^^ a) &&& (c ^^^ b)) >>> 31) 0

example (a b : BitVec 32) :
    will_add_overflow_64bit a b = will_add_overflow_optimized_b a b := by
  sorry -- now what?
```
)

= `bv_decide`
== Pipeline
Pipeline inspired by the (unverified) Bitwuzla @bitwuzla SMT solver:
+ Proof by Contradiction
+ Preprocessing
+ Translate the conjunction of all `BitVec` hypotheses into a boolean circuit
+ Prove that this circuit can never output `true`
  - $->$ the hypotheses cannot hold
  - $->$ contradiction

== Proof by Contradiction
TODO: come up with example that is:
- small
- show cases all steps of the preprocessing

TODO: show initial example and state after contradiction

== Preprocessing: Rewriting
TODO: split slides in two, left side explanation, right side result on example


== Preprocessing: And Flattening
TODO: split slides in two, left side explanation, right side result on example

== Preprocessing: Embedded Constraint Substitution
TODO: split slides in two, left side explanation, right side result on example

== Reflection
TODO: split slides in two, left side inductive + eval, right side result on example

== And Inverter Graphs (AIG)
#slide[
  #[
    #show raw: set text(size: 13pt)
    #sourcecode(
      ```lean
      inductive Decl (α : Type) where
        | const (b : Bool)
        | atom (idx : α)
        | gate (l r : Nat) (linv rinv : Bool)

      structure AIG (α : Type) where
        decls : Array (Decl α)
        cache : Cache α decls
        invariant : IsDAG α decls
      ```)
  ]
  #uncover("2-")[
    Need to:
    - write translators from `BVExpr` to `AIG`
    - build `AIG` theory
    - prove equivalence to `BitVec` operations:
      - thanks to Siddharth Bhat for `BitVec` theory!
  ]
][
  #[
    #set align(center)
    #show raw: set text(size: 13pt)
    ```
    #[.atom 0, .atom 1,
      .gate 0 1 true false, .gate 0 2 true true]
    ```
    #raw-render(
      ```dot
    Digraph AIG {
      0 [label="0", shape=doublecircle];
      1 [label="1", shape=doublecircle];
      2 [label="2 ∧",shape=trapezium];
      3 [label="3 ∧",shape=trapezium];
      3 -> 0 [color=red];
      3 -> 2 [color=red];
      2 -> 0 [color=red];
      2 -> 1 [color=blue];
    }
    ```)
  ]
]

== SAT Solver
SAT solvers:
- take a boolean formula
- attempt to find a variable assignment that makes it true (SATisfiable)
- produce an UNSAT certificate if they can't

#pause

Idea:
- give our circuit to a SAT solver (CaDiCal @cadical)
- if it returns SAT we recover a counter example
- if it returns UNSAT we obtain the certificate
- run a verified certificate checker to validate that the circuit is indeed UNSAT

== Convincing Lean
#sourcecode[
```lean
theorem verifyCert_correct : ∀ cnf c, verifyCert cnf c = true → cnf.Unsat

def verifyBVExpr (bv : BVLogicalExpr) (c : LratCert) : Bool :=
  verifyCert (AIG.toCNF bv.bitblast) c

theorem unsat_of_verifyBVExpr_eq_true {bv : BVLogicalExpr} {c : LratCert}
    (h : verifyBVExpr bv c = true) : bv.Unsat

```
]

#pause

Given a reflected expression `bv` and a certificate `c` we produce:
#sourcecode[
```lean
unsat_of_verifyBVExpr_eq_true (ofReduceBool (verifyBVExpr bv c) true rfl)
```
]

== Putting it all together
`bv_decide` is:
+ `by_contra`
+ Preprocessing as normal proof producing meta programs
+ Reflection (resulting expression equivalent to goal by `rfl`)
+ Bitblast the expression
+ Obtain counter example or UNSAT certificate from SAT solver
+ Convince Lean of the UNSAT certificate through `ofReduceBool`
#pause
#sourcecode[
```lean
example (a b : BitVec 32) :
    will_add_overflow_64bit a b = will_add_overflow_optimized_b a b := by
  unfold will_add_overflow_64bit will_add_overflow_optimized_b
  bv_decide -- finishes in 0.1s
```
]

= Performance Evaluation
== What's out there?
- Unverified high performance SMT solvers like Bitwuzla
  - the upper bound of what is possible
- HOL Light @hollight also has a CaDiCal based bitblaster
- Coq has:
  - SMTCoq @SMTCoq
  - CoqQFBV @CoqQFBV
- Isabelle doesn't have a bitblaster to my knowledge
== Lean MLIR
#figure(
  image("figures/cumul_problems_llvm_instcombine_proved.svg"),
  caption: [`bv_decide` vs Bitwuzla on LLVM `InstCombine` rewrites in Lean MLIR @leanmlir]
)
== HOL Light
TODO: Build graph from my HOL data: https://gist.github.com/hargoniX/066d343e49b83c847827ffb71c04d67f
== SMTCoq @SMTCoq
#[
  #set align(center)
  #image("figures/smtcoq.png")
]
== CoqQFBV @CoqQFBV
#[
  #set align(center)
  #image("figures/coqqfbv.png", width: 80%)
]
== SMTLib
#figure(
    stack(
        image("figures/cumul_problems_smtlib_sat.svg"),
        image("figures/cumul_problems_smtlib_unsat.svg"),
    ),
    caption: [`bv_decide` on SMTLib, collected by Abdalrhman Mohamed]
)

= Bibliography
== Bibliography
#bibliography("references.bib")
