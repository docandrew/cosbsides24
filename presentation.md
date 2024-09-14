---
marp: true
theme: gaia
class: invert
paginate: true
---

## Colorado Springs B-Sides '24

Preventing Bugs w/ Strong Typing and Formal Methods

https://github.com/docandrew/cosbsides24

---

## About me

- Not a Computer Science PhD
- Not a Mathematician

---

## This talk

- This is an _introduction_ to the topic of type theory and formal methods
- The goal: awareness of tools that _might help_ you write better software

---

## Types!

built-ins:

`bool`, `int`, `string`, `float`, `double`, `char`, `void`, `uint_32`

complex:

`struct`, `enum`, `union`, `class`

user-defined:

`zarfPackage`, `abstractFactoryGeneratorVisitor`

---

# But...

Lots more possibilities are out there...

**Let's go down the rabbit hole!**

---

## Type Theory

- Based around set theory
- i.e. the set of integers, the set of strings, etc.
- $\lambda$-calculus, typing system says a function f has type A -> B, can be applied f x only if x has type A.
- In other words, if the function expects an integer, you can't give it a string.
- `int f(int x)` is a function that takes an integer and returns an integer.
- If x is not in the _set_ of integers, type system will reject it.

---

## Type Theory

- Curry-Howard Isomorphism*: There's a correspondence between _types_ in programming languages and _propositions_ in logic.

\* or correspondence

---

## Fancy Types

- Enums = "Sum type"
    This variable can be a "Monday" _or_ a "Tuesday" _or_ a "Wednesday"

- Structs = "Product type"
    This variable is a "Name" _and_ a "Address"

- Sum types analogous to logical disjunction (OR, $\lor$)
- Product types analogous to logical conjunction (AND, $\land$)
- Functions analogous to logical implication (if X, then Y, $\rightarrow$)

---

## Some languages spell this out ($\rightarrow$)

- Haskell

```bash
$ docker run -it --rm haskell:latest
```

```haskell
ghci> let add3 x = x + 3
ghci> :info add3
```

- Rust

```rust
fn five() -> i32 {
    5
}
```

---

## Why should we care?

- We have tools to verify formal logic, so if we can make our code look like formal logic, we can _verify_ our code.

---

## Weak typing

```c
// enum for the days of the week
enum days {SUN, MON, TUE, WED, THU, FRI, SAT};

int main() {
    enum days today;
    today = 34;

    return today;
}
```

^^^ totally legal

---

## Can we go beyond type-safety?

- _Prove_ absence of undefined behavior
- _Prove_ absence of unsafe behavior
- _Prove_ **functional correctness** at compile-time?

---

## Formal Methods

- Goal: Mathematically prove that a program is correct.
- Since programs $\simeq$ proofs, this is equivalent to proving some kind of theorem.
- Weakly-typed programming languages may give us _some_ guarantees, but not enough to prove correctness.
- Stronger type systems can give us more guarantees beyond type-safety, such as memory-safety (Rust)
- We can use computer-assisted theorem proving to prove _correctness_ (meeting a specification).

---

## Formal Methods

- Spectrum of tools from very "mathy" to very practical

- Proof Assistants: Coq, HOL4, F*, Isabelle
- Model Checkers: TLA+
- Functional PLs with strong typing: Haskell, Standard ML, OCaml
  (and anything else with a $\lambda$ in the logo typically)
- PLs with dependent types/theorem proving: Idris, Agda, ATS, Lean
- Verifiable Programming Languages: Frama-C, SPARK

---

## Coq Proof Assistant

Demo

---

## What if we could take programming languages and make them more like formal logic?

---

## Lean Programming Language

Demo

---

## What if we could take a normal programming language but add a formal verification layer on top of it?

---

## SPARK

- Formally-verifiable subset of Ada
- Used in Airbus avionics and flight control
- Air traffic control systems, Rail systems
- Medical devices
- Nvidia is using it now

---

## How SPARK works:

- A program takes SPARK and generates Why3 "verification conditions" or VCs
- VCs are generated in "why3ml" language that can be checked by a theorem prover (https://www.why3.org/)
- Why3 translates the VCs into a logical formula (SMT)
- SMT solvers can then check the formula for _satisfiability_
<!-- SMT Solving is NP-Complete, very compute intensive -->

---

## Satisfiability / 3SAT

Given a series of clauses:

C1: A $\lor$ B $\lor$ C
C2: (A $\lor$ $\lnot$B) $\land$ D
C3: (B $\land$ C) $\lor$ $\lnot$D

Can we find values for A, B, C and D such that these are true?

(Yes: A = true, B = true, C = true, D = true)

Lots of difficult (NP) problems can be reduced to 3SAT.

---

## Satisfiability _modulo_ theories (SMT)

- Generalization of 3SAT for integers, real numbers, math.

- SMT _Solvers_: Z3, CVC4, AltErgo

- Standardized SMTLib input format

```
; Integer arithmetic
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (- x y) (+ x (- y) 1)))
(check-sat)
; unsat
(exit)
```

---

## SPARK Demo

---

## What's the Catch?

- Writing specifications is difficult

- Writing code that meets the specifications is difficult 

- Making the solver happy is difficult

- SMT Solving is NP-Complete...

- ...so solving is difficult (for your computer)

- Tools are getting better, but it's still a lot of work

---

## Conclusions

- Strong typing & formal verification can prevent bugs/CVEs

- Am I suggesting you rewrite your entire codebase in SPARK?

---

## YES!

---

## But seriously

- There's a time and a place
- Be aware of the tradeoffs
- If given a choice, pick languages/tools with more rigid underpinnings
  * Strict typing
  * Robust type systems 
  * Memory-safety
  * Thread-safety

---

## Example

- Base64 decoding CVE:
- https://exim.org/static/doc/security/CVE-2018-6789.txt
- https://devco.re/blog/2018/03/06/exim-off-by-one-RCE-exploiting-CVE-2018-6789-en/

---

## References

- Why3 https://www.why3.org/
- Software Foundations https://softwarefoundations.cis.upenn.edu/

---

## Symbols

$\lambda$ "lambda" (anonymous function definition)
$\vdash$ "proves," "yields"
$\rightarrow$ "implies"

---

## More about $\lambda$-calculus

Earlier we showed how you can build up a mathematical
framework from basic symbol manipulation like unary numbers.

$\lambda$-calculus is a similar idea, but using functions. Using basic function definitions and applications, you can build up a mathematical framework that's Turing complete.

We can define basic numbers, logical operations, and
arithmetic operations using $\lambda$-calculus. Since it's Turing-complete, you can compute anything!

---
