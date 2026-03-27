# Trust-Lean: Verified Code Generation Framework for Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Tests](https://img.shields.io/badge/Tests-410%2B-green.svg)](#performance)
[![Build](https://img.shields.io/badge/Build-632%20jobs-brightgreen.svg)](#quick-start)

## What is Trust-Lean?

**Trust-Lean** is a verified code generation framework that compiles multiple DSL frontends through a shared Core IR to multiple backends (C, Rust) with **machine-checked correctness proofs**. Every compilation step carries a Lean proof that the output preserves the semantics of the input.

The core value proposition: **define your DSL semantics in Lean 4, implement the `CodeGenerable` + `CodeGenSound` typeclasses, and get verified C or Rust code** — the framework handles compilation, backend emission, and proof obligations. Zero sorry, zero axioms — the kernel checks everything.

Trust-Lean currently supports three frontends (ArithExpr, BoolExpr, ImpStmt), two backends (C, Rust), a MicroC formal C99 subset with roundtrip parser, Int64/UInt32/UInt64 evaluators with agreement proofs, function call semantics, bitwise/casting operations, and Plonky3 field reduction bridges (Mersenne31, BabyBear, KoalaBear, Goldilocks).

## Ecosystem & Comparisons

Trust-Lean provides a **verified backend** for DSL-to-C/Rust compilation. Most verified compilers target general-purpose languages; Trust-Lean targets domain-specific languages with typeclass-based extensibility.

| Project | Approach | Proof Assistant | Verification Scope | Codegen Target |
|---------|----------|-----------------|---------------------|----------------|
| **Trust-Lean** | Typeclass-based DSL compilation | Lean 4 | Full pipeline (DSL → IR → code) | C, Rust |
| [CompCert](https://compcert.org/) | Verified C compiler | Coq | Compiler passes | Assembly |
| [fiat-crypto](https://github.com/mit-plv/fiat-crypto) | Synthesis from field specs | Coq | Field arithmetic | C, Rust, Go, Java |
| [CakeML](https://cakeml.org/) | Verified ML compiler | HOL4 | Full compiler | Assembly |
| [Jasmin](https://github.com/jasmin-lang/jasmin) | Verified assembly compiler | Coq (EasyCrypt) | Compiler correctness | x86 assembly |

**What makes Trust-Lean different:**
- **Typeclass extensibility**: new frontends and backends only need to implement `CodeGenerable` + `CodeGenSound` — the pipeline and proofs compose automatically
- **Fuel-based semantics**: `evalStmt_fuel_mono` (fuel monotonicity) is the gate theorem that unlocks all downstream proofs without well-founded recursion complexity
- **Industrial C backend**: sanitized identifiers (idempotent, keyword-safe, valid C), balanced braces on all 12 `Stmt` constructors, auto-generated headers
- **AMO-Lean integration**: verified bridge from `ExpandedSigma` to `Stmt` with simulation diagram proof, enabling verified compilation of optimized cryptographic code

## How It Works

```
DSL Frontends          Core IR              Backends
+-----------+    +-----------------+    +-----------+
| ArithExpr  |--->|                 |--->| C Backend |
| BoolExpr   |--->|  Stmt (12 ops)  |--->| Rust      |
| ImpStmt    |--->|  Value (Int|Bool)|    +-----------+
+-----------+    |  Fuel semantics  |
                 +-----------------+
                        |
                 CodeGenSound proofs
                 (per frontend)
```

### Compilation Pipeline

1. **Frontend** defines DSL syntax and semantics (`eval` function)
2. **`CodeGenerable`** instance compiles DSL to `Stmt` (Core IR)
3. **`CodeGenSound`** instance proves compilation preserves semantics
4. **`Pipeline.sound`** theorem composes frontend + backend correctness
5. **Backend** emits C or Rust from `Stmt` with structural correctness proofs

### Core IR

- **`Stmt`**: 12-constructor type (assign, store, load, seq, ite, while, for_, call, skip, break_, continue_, return_)
- **`Value`**: sum type `int Int | bool Bool` — avoids phantom type proof explosion while supporting heterogeneous computation
- **Key theorem**: `evalStmt_fuel_mono` — giving more fuel never changes the result

## Features

- **ArithExpr Frontend** — Arithmetic expressions with verified `compile_correct` theorem
- **BoolExpr Frontend** — Boolean logic with short-circuit semantics, De Morgan's laws verified
- **ImpStmt Frontend** — Imperative statements with control flow (while, for, break, continue, return)
- **C Backend** — Industrial-grade: sanitized identifiers (idempotent, keyword-safe), balanced braces, auto-headers (stdint.h, stdbool.h)
- **Rust Backend** — Balanced braces, control flow keywords, configurable integer types
- **AMO-Lean Bridge** — `ExpandedSigma -> Stmt` with `expandedSigmaToStmt_correct` simulation diagram (26 theorems, 0 sorry)
- **Typeclass System** — `CodeGenerable` (compilation), `CodeGenSound` (3-part verification contract), `BackendEmitter` (emission)
- **Foundation Proofs** — Fuel monotonicity, seq identity, break/continue/return propagation, memory model (store/load roundtrip)

## Quick Start

```bash
# Clone and build
git clone https://github.com/manuelpuebla/trust-lean.git
cd trust-lean
lake build

# Verify zero sorry
grep -r "sorry" TrustLean/ --include="*.lean" | wc -l  # should be 0

# Run integration tests
lake env lean TrustLean/Tests/Integration.lean
```

Requires Lean 4 toolchain and Mathlib.

## Examples

### ArithExpr: Compile and verify

```lean
-- Define an arithmetic expression
def myExpr : ArithExpr := .add (.lit 3) (.mul (.var 0) (.lit 5))

-- Compile to Core IR
def compiled := ArithExpr.compile myExpr defaultState

-- The compiler proves: evaluating the DSL = evaluating the compiled IR
#check @ArithExpr.compile_correct
-- ArithExpr.compile_correct : forall (a : ArithExpr) ...
--   evalStmt fuel llEnv (compile a st).2 = some (.normal, llEnv')
--   -> llEnv' (resultVar st) = .int (ArithExpr.eval env a)
```

### ImpStmt: While loop with verified semantics

```lean
-- Sum 1..10 in an imperative DSL
def sumProgram : ImpStmt :=
  .seq (.assign 0 (.lit 0))          -- x = 0
  (.seq (.assign 1 (.lit 1))         -- i = 1
  (.while (.lt_ (.var 1) (.lit 11))  -- while i < 11
    (.seq (.assign 0 (.add (.var 0) (.var 1)))  -- x += i
          (.assign 1 (.add (.var 1) (.lit 1))))))  -- i++

-- Evaluates to 55
#eval ImpStmt.eval 200 (fun _ => 0) sumProgram  -- some env where env 0 = 55
```

### C Backend: Generate verified C code

```lean
-- Generate C function from a Stmt
def cCode := generateCFunction defaultCConfig "compute"
  [("x", "int64_t"), ("y", "int64_t")]
  "int64_t"
  (.assign (.user "result") (.binOp .add (.varRef (.user "x")) (.varRef (.user "y"))))

-- Produces:
-- int64_t compute(int64_t x, int64_t y) {
--   result = (x + y);
-- }
```

## Performance

| Metric | Value |
|--------|-------|
| Lines of Code | 15,836 |
| Theorems + lemmas | 879 |
| @[simp] lemmas | 430 |
| Sorry | **0** |
| Axioms | **0** |
| Source files | 73 |
| Build | 632 jobs |

See [BENCHMARKS.md](BENCHMARKS.md) for full verification criteria and results. See [TESTS_POST.md](TESTS_POST.md) for adversarial post-hoc testing report.

## What's New in v3.1.0

### Changes Since v3.1.0

| Metric | v3.1.0 | v3.2.0 | Change |
|--------|--------|--------|--------|
| **Lines of Code** | 15,237 | **15,836** | +599 LOC |
| **Theorems + lemmas** | 839 | **879** | +40 |
| **Sorry** | 0 | **0** | Same |
| **Axioms** | 0 | **0** | Same |
| **Source files** | 71 | **73** | +2 |

### Key Achievements (v3.1.0 -> v3.2.0)

1. **Verified Rust Backend Properties** — 40 formal properties in `RustBackendProperties.lean`: determinism, balanced braces (hybrid induction+decide), expression emission, control flow structure
2. **Rust Keyword Sanitization** — 53 Rust keywords (39 strict + 14 reserved, Rust 2021 edition), `sanitizeIdentifierRust` with 4 theorems (not_keyword, nonempty, valid, idempotent)
3. **Shared countChar Infrastructure** — `countChar`, `countChar_empty`, `countChar_append` moved to Common.lean for cross-backend reuse
4. **Rust-Specific Formal Properties** — Cast postfix (`as`), no-parens if/while, boolean keyword emission (`true`/`false` not `1`/`0`), `as usize` array indexing

### Version History

```
v1.0.0 (Feb 20)    0 axioms    0 sorry    Core IR + 3 frontends + 2 backends + pipeline
v1.1.0 (Feb 21)    0 axioms    0 sorry    AMO-Lean bridge (ExpandedSigma -> Stmt)
v1.2.0 (Feb 21)    0 axioms    0 sorry    Industrial CBackend + formal properties
v2.0.0 (Mar 10)    0 axioms    0 sorry    MicroC: AST, evaluator, simulation, roundtrip
v3.0.0 (Mar 12)    0 axioms    0 sorry    Int64 overflow, call semantics, full inductive roundtrip
v3.1.0 (Mar 22)    0 axioms    0 sorry    Bitwise ops, unsigned MicroC, Plonky3 reductions
v3.2.0 (Mar 27)    0 axioms    0 sorry    Verified Rust Backend (40 formal properties)
```

## Future Work (v4.0+)

| Task | Relevance | Difficulty | Status |
|------|-----------|------------|--------|
| **Goldilocks 128-bit (u128 hi/lo)** | High — Plonky3 field requiring 128-bit splitting | High | Designed (v3.2) |
| **Short-circuit &&/\|\|** | Medium — needed for side-effecting expressions | Medium | Planned |
| **RustBackend formal properties** | Medium — CBackend has 34 theorems, Rust has 4 | Low | Designed |
| **Optimization passes** | High — constant folding, dead code elimination | High | Planned |
| **LLVM/WebAssembly backends** | Medium — extends target coverage | Medium | Planned |
| **Parallelism support** | Medium — `.par` currently interpreted as `.seq` | High | Deferred |

See [ARCHITECTURE.md](ARCHITECTURE.md) for the full DAG and design decisions.

## Relationship to Other Projects

- **LeanScribe** (predecessor): proved the core patterns work (3,095 LOC, 72 theorems, 0 sorry). Trust-Lean extends the IR from 5 to 12 constructors and adds the typeclass layer.
- **AMO-Lean** (integrated in v1.1.0): FRI optimization pipeline. Trust-Lean provides a verified bridge `ExpandedSigma -> Stmt` with a simulation diagram proof (`expandedSigmaToStmt_correct`).

## References

1. **CompCert**: Leroy "A Formally Verified Compiler Back-end" (J. Automated Reasoning, 2009)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **CakeML**: Kumar et al. "CakeML: A Verified Implementation of ML" (POPL 2014)
4. **Lean 4**: de Moura & Ullrich "The Lean 4 Theorem Prover and Programming Language" (CADE 2021)

## License

MIT License — see [LICENSE](LICENSE) for details.

---

**Trust-Lean v3.2.0** — Every compilation step is a theorem. 879 theorems, 0 sorry, 0 axioms.
