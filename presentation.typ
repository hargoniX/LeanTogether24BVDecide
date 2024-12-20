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
Do these functions compute the same thing? #footnote[From https://grack.com/blog/2022/12/20/deriving-a-bit-twiddling-hack/]
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

#[
  #show raw: set text(size: 13pt)
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
]

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

Start with a contradiction proof:
#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  a k n : BitVec 64
  h1 : n < 18446744073709551615#64 - k ∧ k > 0
  ⊢ a + k ≠ a ∧ n < ~~~k
  ```)
]

#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  a k n : BitVec 64
  h1 : n < 18446744073709551615#64 - k ∧ k > 0
  h2 : ¬(a + k ≠ a ∧ n < ~~~k)
  ⊢ False
  ```)
]

== Preprocessing: Rewriting
Apply rewrite rules from Bitwuzla through `simp`:
#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  h1 : n < 18446744073709551615#64 - k ∧ k > 0
  h2 : ¬(a + k ≠ a ∧ n < ~~~k)
  ⊢ False
  ```)
]

#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  h1 : (n < (~~~k) && !k == 0#64) = true
  h2 : (!(!a + k == a && n < (~~~k))) = true
  ⊢ False
  ```)
]

== Preprocessing: And Flattening
Split ands into individual hypotheses:

#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  h1 : (n < (~~~k) && !k == 0#64) = true
  h2 : (!(!a + k == a && n < (~~~k))) = true
  ⊢ False
  ```)
]

#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  h1 : n < (~~~k) = true
  h3 : (!k == 0#64) = true
  h2 : (!(!a + k == a && n < (~~~k))) = true
  ⊢ False
  ```)
]

== Preprocessing: Embedded Constraint Substitution
Look for embedded constraints:
#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  h1 : n < (~~~k) = true
  h3 : (!k == 0#64) = true
  h2 : (!(!a + k == a && n < (~~~k))) = true
  ⊢ False
  ```)
]

#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  h1 : n < (~~~k) = true
  h3 : (!k == 0#64) = true
  h2 : (!(!a + k == a && true)) = true
  ⊢ False
  ```)
]

#pause
Now repeat until fixpoint!

#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  a k n : BitVec 64
  h1 : n < (~~~k) = true
  h3 : (!k == 0#64) = true
  h2 : (a + k == a) = true
  ⊢ False
  ```)
]


== Reflection
#[
  #show raw: set text(size: 13pt)
  #sourcecode(
  ```lean
  inductive BVExpr : Nat → Type where
    | var (idx : Nat) : BVExpr w
    | const (val : BitVec w) : BVExpr w
    | add (lhs : BVExpr w) (rhs : BVExpr w) : BVExpr w
    -- ...

  def BVExpr.eval (assign : Assignment) : BVExpr w → BitVec w
    | .var idx => assign.get idx
    | .const val => val
    | .add lhs rhs => (eval assign lhs) + (eval assign rhs)
    -- ...

  example (x : BitVec 16) :
      x + 1 = BVExpr.eval #R[⟨x⟩] (.add (.var 0) (.const 1#16)) := by
    rfl
  ```
  )
]

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

def verifyBVExpr (bv : BVExpr) (c : LratCert) : Bool :=
  verifyCert (AIG.toCNF bv.bitblast) c

theorem unsat_of_verifyBVExpr_eq_true {bv : BVExpr} {c : LratCert}
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
+ Proof by contradiction
+ Preprocessing using normal tactics
+ Reflection (resulting expression equivalent to goal by `rfl`)
+ Bitblast the expression
+ Obtain UNSAT certificate from SAT solver
+ Use `ofReduceBool` + UNSAT certificate to show the expression is `False`
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
#figure(
  image("figures/cumul_problems_hollight_hollight_proved.svg"),
  caption: [`bv_decide` vs HOL Light with CaDiCal #footnote[Data at https://gist.github.com/hargoniX/066d343e49b83c847827ffb71c04d67f]]
)
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

#pagebreak()

Rough data about the timeouts:
- $approx 4000$ due to kernel typechecking of reflection and preprocessing step
  - $->$ optimize kernel term
- $approx 7000$ due to timeout while running rewrite rules with `simp`
  - $->$ optimize `simp`
- remaining $approx 4000$ spread across various other stages of the pipeline

= Questions?

= Bibliography
== Bibliography
#bibliography("references.bib")
