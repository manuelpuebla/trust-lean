# Trust-Lean: Architecture

## Vision

Trust-Lean is a **verified codegen framework** for Lean 4: a platform where multiple domain-specific languages (DSLs) compile to a shared Core IR, with multiple backends (C, Rust), typeclass-based extensibility, and verified correctness proofs. Inspired by Fiat-Crypto's architecture of composable, verified transformations.

**Core principle**: Any DSL that implements `CodeGenerable` gets verified compilation to any backend that implements `BackendEmitter` — with a machine-checked proof that the compilation preserves semantics.

```
  Frontend A ──┐                    ┌──→ C Backend
  Frontend B ──┼──→ Core IR (Stmt) ─┼──→ Rust Backend
  Frontend C ──┘                    └──→ (future backends)
               ↑                    ↑
          CodeGenerable          BackendEmitter
          CodeGenSound           (trusted pretty-printer
          (verified)              or verified emitter)
```

## Relationship with LeanScribe

Trust-Lean is the **successor project** to LeanScribe (v2.5.0 → v3.0). LeanScribe is a concrete verified compiler (`Expr Int + BoolExpr → Stmt → C`). Trust-Lean generalizes this into a framework.

### What Trust-Lean inherits from LeanScribe

| Component | LeanScribe source | Trust-Lean usage |
|---|---|---|
| **Core IR (Stmt)** | `LeanScribe/LowLevel.lean:69-76` | Direct adoption — 5 constructors (assign, seq, ite, while, skip) + new ones (store, load, for, call) |
| **Outcome type** | `LeanScribe/LowLevel.lean:78-82` | Extended — add break, continue, return(Option Value) |
| **Fuel-based evalStmt** | `LeanScribe/Interpret.lean:107-128` | Adopted pattern — fuel decrements only in while/for. Proven correct in LeanScribe |
| **evalStmt_fuel_mono** | `LeanScribe/Correctness.lean:310-347` | Same theorem structure — monotonicity restricted to Outcome.normal |
| **Bridge lemma pattern** | `assignmentsToStmt_correct` | Generalized — every frontend provides a bridge from its semantics to evalStmt |
| **@[simp] equation lemmas** | `LeanScribe/Interpret.lean` (42 lemmas) | Same pattern — every IR construct gets @[simp] lemmas for evalStmt |
| **C backend structure** | `LeanScribe/CBackend.lean` | Starting point for `stmtToC` — extended with store, load, for, call |
| **BinOp meta-lemma** | `lowerExpr_correct_binOp` | Generalized — `CodeGenSound` provides the meta-lemma obligation |
| **VarName tagged union** | `VarName.user` / `VarName.temp` | Adopted directly — constructor disjointness is foundational |
| **SSA property** | Temps are single-assignment | Preserved — temps assigned once per basic block |
| **LowLevelEnv as pure function** | `VarName → Int` | Migrated to `VarName → Value` or `ExtHashMap VarName Value` |
| **Test patterns** | 56 integration tests | Reused as regression suite for first frontend |

### What Trust-Lean does NOT inherit

| Component | Reason |
|---|---|
| `Expr Int` as source language | Becomes one instance of `CodeGenerable`, not the only frontend |
| `BoolExpr` as separate inductive | Subsumed by `Value = Int \| Bool` and typed expressions |
| `CommRing`-only denote | `denote` must handle both Int (CommRing + ring) and Bool (Decidable + decide) |
| `LowLevelEnv = VarName → Int` | Needs `VarName → Value` for heterogeneous types |
| Correctness.lean monolith (880 LOC) | Decomposed into per-frontend proof modules |
| Trusted C backend | Eventually verified (stretch goal); initially still trusted |

### LeanScribe as test oracle

Trust-Lean imports LeanScribe (or its types) as a dependency. For any `Expr Int` input, Trust-Lean's pipeline must produce identical results to LeanScribe's `toLowLevel_correct` / `lowerToStmt_correct`. This provides a regression guarantee: if Trust-Lean breaks for `Expr Int`, LeanScribe catches it.

```lean
-- Trust-Lean regression test pattern:
example (e : Expr Int) (env : VarId → Int) :
    TrustLean.compile e env = LeanScribe.denote e env := by
  -- Should follow from CodeGenSound instance + LeanScribe correctness
  ...
```

---

## Core Architecture

### 1. Value Type (Heterogeneous)

```lean
inductive Value where
  | int  : Int → Value
  | bool : Bool → Value
  deriving DecidableEq, Repr, BEq

-- Typed accessors with proof obligations
def Value.asInt : Value → Option Int
  | .int n => some n
  | _ => none

def Value.asBool : Value → Option Bool
  | .bool b => some b
  | _ => none
```

**Design decision**: Inductive sum type, not type-indexed AST. Per LeanScribe insight (BoolExpr_insights.md §7.1): phantom types cause proof explosion. Sum type gives constructor injectivity/disjointness from the kernel for free.

**Impact**: `LowLevelEnv = VarName → Value` (or `ExtHashMap VarName Value`). All evalStmt/evalExpr functions return `Value` instead of `Int`.

### 2. Extended Core IR

```lean
inductive BinOp where
  | add | sub | mul          -- Int → Int → Int
  | eqOp | ltOp              -- Int → Int → Bool (as Value)
  | land | lor               -- Bool → Bool → Bool (as Value)

inductive UnaryOp where
  | neg                      -- Int → Int
  | lnot                     -- Bool → Bool

inductive LowLevelExpr where
  | litInt    : Int → LowLevelExpr
  | litBool   : Bool → LowLevelExpr
  | varRef    : VarName → LowLevelExpr
  | binOp     : BinOp → LowLevelExpr → LowLevelExpr → LowLevelExpr
  | unaryOp   : UnaryOp → LowLevelExpr → LowLevelExpr
  | powCall   : LowLevelExpr → Nat → LowLevelExpr

inductive Stmt where
  | assign  : VarName → LowLevelExpr → Stmt
  | store   : LowLevelExpr → LowLevelExpr → LowLevelExpr → Stmt  -- array[index] = value
  | load    : VarName → LowLevelExpr → LowLevelExpr → Stmt       -- var = array[index]
  | seq     : Stmt → Stmt → Stmt
  | ite     : LowLevelExpr → Stmt → Stmt → Stmt
  | while   : LowLevelExpr → Stmt → Stmt
  | for_    : Stmt → LowLevelExpr → Stmt → Stmt → Stmt           -- init; cond; step; body
  | call    : VarName → String → List LowLevelExpr → Stmt         -- var = func(args)
  | skip    : Stmt
  | break_  : Stmt
  | continue_ : Stmt
  | return_ : Option LowLevelExpr → Stmt

inductive Outcome where
  | normal   : Outcome
  | break_   : Outcome
  | continue_: Outcome
  | return_  : Option Value → Outcome
  | outOfFuel: Outcome
```

**Note**: `for_` is syntactic sugar over `seq init (while cond (seq body step))` following Clight's decomposition. It exists for backend emission convenience but its semantics are defined by desugaring. This means proofs only need to handle while — `for_` correctness follows by definitional equality.

### 3. Typeclass Infrastructure

```lean
-- Operational API: how to compile a DSL to Core IR
class CodeGenerable (α : Type) where
  /-- The semantic type of the DSL (what denote returns) -/
  ValueType : Type
  /-- Semantic function of the source language -/
  denote : α → (VarId → Value) → ValueType
  /-- Compilation to Core IR -/
  lower : α → CodeGenState → StmtResult
  /-- Variable naming scheme -/
  varNames : VarId → String

-- Verification obligation: compilation preserves semantics
class CodeGenSound (α : Type) [CodeGenerable α] where
  /-- Central correctness theorem -/
  lower_correct :
    ∀ (a : α) (env : VarId → Value) (llEnv : LowLevelEnv),
      (∀ v, llEnv (.user (CodeGenerable.varNames v)) = env v) →
      ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
        evalStmt fuel llEnv (CodeGenerable.lower a default).stmt =
          some (.normal, resultEnv) ∧
        resultEnv (CodeGenerable.lower a default).resultVar =
          CodeGenerable.denote a env ∧
        ∀ v, resultEnv (.user (CodeGenerable.varNames v)) = env v
```

**Three-part contract** (same as LeanScribe's `lowerToStmt_correct`):
1. There exists sufficient fuel for normal termination
2. The result variable holds the correct value
3. User variables are preserved (only temps are written)

**Per-frontend work**: Each DSL provides an instance of `CodeGenerable` (mechanical) and `CodeGenSound` (the hard proof). The meta-lemma pattern from LeanScribe (`lowerExpr_correct_binOp`) generalizes: `CodeGenSound` provides a uniform proof obligation that each frontend must satisfy.

### 4. Backend Infrastructure

```lean
-- Backend emission (currently trusted, outside TCB)
class BackendEmitter (β : Type) where
  /-- Target language name -/
  name : String
  /-- Emit a statement in the target language -/
  emitStmt : β → Nat → Stmt → String  -- config, indentation, stmt
  /-- Emit a complete function -/
  emitFunction : β → String → List (String × String) → Stmt → LowLevelExpr → String
  /-- Emit a translation unit header -/
  emitHeader : β → String

-- Instances
structure CConfig where
  useInt64 : Bool := true
  includePowerHelper : Bool := true

structure RustConfig where
  useMut : Bool := true
  lifetime : Option String := none

instance : BackendEmitter CConfig where ...
instance : BackendEmitter RustConfig where ...
```

**TCB boundary**: Backend emitters are **outside the TCB** (trusted pretty-printers), same as LeanScribe's `CBackend.lean`. A verified emitter (proving that the C/Rust output has the same semantics as `evalStmt`) is a stretch goal requiring a formalized target language semantics (Clight for C, MIR for Rust).

### 5. Semantics Layer

```lean
-- Environment: heterogeneous
abbrev LowLevelEnv := VarName → Value

-- Or, for O(1) lookup (per LeanScribe insight on ExtHashMap):
-- abbrev LowLevelEnv := Std.ExtHashMap VarName Value

-- Core interpreter (fuel-based, per CertiCoq/LeanScribe pattern)
def evalStmt (fuel : Nat) (env : LowLevelEnv) : Stmt → Option (Outcome × LowLevelEnv)
-- Fuel only decreases in while/for. assign/seq/ite/skip/break/continue/return
-- do NOT consume fuel. This is the LeanScribe-proven model.

-- Equation lemmas (@[simp], per LeanScribe pattern)
@[simp] theorem evalStmt_skip : evalStmt fuel env .skip = some (.normal, env)
@[simp] theorem evalStmt_assign : evalStmt fuel env (.assign n e) = ...
@[simp] theorem evalStmt_seq : evalStmt fuel env (.seq s1 s2) = ...
@[simp] theorem evalStmt_ite : evalStmt fuel env (.ite c t f) = ...
@[simp] theorem evalStmt_while_zero : evalStmt 0 env (.while c b) = some (.outOfFuel, env)
@[simp] theorem evalStmt_while_succ : evalStmt (n+1) env (.while c b) = ...
@[simp] theorem evalStmt_break : evalStmt fuel env .break_ = some (.break_, env)
@[simp] theorem evalStmt_continue : evalStmt fuel env .continue_ = some (.continue_, env)
@[simp] theorem evalStmt_return : evalStmt fuel env (.return_ v) = ...

-- Fuel monotonicity (restricted to Outcome.normal, per LeanScribe proof)
theorem evalStmt_fuel_mono
    (h : evalStmt fuel env stmt = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalStmt fuel' env stmt = some (.normal, env')

-- Outcome propagation for while (Clight 3-rule pattern):
-- Rule 23: cond false → (.normal, env)
-- Rule 24/25: cond true, body produces .normal/.continue_ → re-enter while
-- body produces .break_ → (.normal, env')
-- body produces .return_ v → (.return_ v, env')
```

---

## Planned Frontends

### Frontend 1: Arithmetic Expressions (from LeanScribe)

```lean
-- Reuse LeanScribe's Expr Int directly
instance : CodeGenerable (LeanScribe.Expr Int) where
  ValueType := Int
  denote := LeanScribe.Expr.denote
  lower e s := LeanScribe.lowerToStmt varNames e  -- wraps lowerExpr + assignmentsToStmt
  varNames := defaultVarNames

instance : CodeGenSound (LeanScribe.Expr Int) where
  lower_correct := by
    -- Follows from LeanScribe.lowerToStmt_correct
    -- + Value.int injection
    intro a env llEnv hbridge
    obtain ⟨fuel, rEnv, heval, hresult, hpreserve⟩ := LeanScribe.lowerToStmt_correct ...
    exact ⟨fuel, rEnv, heval, by simp [Value.int, hresult], hpreserve⟩
```

### Frontend 2: Boolean Expressions (from LeanScribe)

```lean
instance : CodeGenerable LeanScribe.BoolExpr where
  ValueType := Bool
  denote := LeanScribe.BoolExpr.denote
  lower b s := LeanScribe.lowerBoolToStmt varNames b
  varNames := defaultVarNames

instance : CodeGenSound LeanScribe.BoolExpr where
  lower_correct := by
    -- Follows from LeanScribe.lowerBoolToStmt_correct
    ...
```

### Frontend 3: Imperative Programs (new)

```lean
-- A simple imperative language with assignments, loops, conditionals
inductive ImpStmt where
  | assign : VarId → ImpExpr → ImpStmt
  | seq    : ImpStmt → ImpStmt → ImpStmt
  | ite    : ImpBoolExpr → ImpStmt → ImpStmt → ImpStmt
  | while  : ImpBoolExpr → ImpStmt → ImpStmt
  | skip   : ImpStmt

-- This is the natural "next step" frontend — it maps almost 1:1 to Stmt
-- but operates on user-level variables (VarId) not low-level (VarName)
instance : CodeGenerable ImpStmt where ...
instance : CodeGenSound ImpStmt where ...
```

### Future Frontends (from original Trust-Lean vision)

| Frontend | DSL | Source | Target use case |
|---|---|---|---|
| AMO-Lean | At-Most-One constraints | `AMO.lean` | Cryptographic circuit constraints |
| vr1cs-lean | R1CS arithmetic circuits | `vr1cs.lean` | Zero-knowledge proof systems |
| Merkle | Merkle tree operations | `Merkle.lean` | Hash-based data structures |
| PolyCom | Polynomial commitments | `PolyCom.lean` | Cryptographic commitment schemes |

Each frontend implements `CodeGenerable` + `CodeGenSound` for its specific DSL. The proof obligation is always the same 3-part contract. The framework provides the shared IR, semantics, backends, and fuel infrastructure.

---

## File Structure

```
Trust-Lean/
├── lakefile.lean              # Lake project config, depends on LeanScribe (or Mathlib)
├── lean-toolchain             # leanprover/lean4:v4.26.0
├── ARCHITECTURE.md            # This file
├── BENCHMARKS.md              # Verification criteria + results
├── README.md                  # Project overview
│
├── TrustLean/
│   ├── Core/
│   │   ├── Value.lean         # Value inductive (Int | Bool), accessors, @[simp] lemmas
│   │   ├── IR.lean            # Stmt, LowLevelExpr, BinOp, UnaryOp, Outcome
│   │   ├── Env.lean           # LowLevelEnv (pure function or ExtHashMap), update, @[simp]
│   │   ├── Eval.lean          # evalStmt, evalLowLevelExpr, @[simp] equation lemmas
│   │   ├── FuelMono.lean      # evalStmt_fuel_mono theorem
│   │   └── CodeGen.lean       # CodeGenState, freshVar, addAssignment, StmtResult
│   │
│   ├── Typeclass/
│   │   ├── CodeGenerable.lean # CodeGenerable class definition
│   │   ├── CodeGenSound.lean  # CodeGenSound class + proof obligation
│   │   └── BackendEmitter.lean # BackendEmitter class definition
│   │
│   ├── Frontend/
│   │   ├── ArithExpr.lean     # CodeGenerable/Sound instance for Expr Int (wraps LeanScribe)
│   │   ├── BoolExpr.lean      # CodeGenerable/Sound instance for BoolExpr (wraps LeanScribe)
│   │   ├── ImpStmt.lean       # Imperative language frontend (new)
│   │   └── ...                # Future frontends (AMO, vr1cs, etc.)
│   │
│   ├── Backend/
│   │   ├── C.lean             # CConfig + BackendEmitter instance
│   │   ├── Rust.lean          # RustConfig + BackendEmitter instance
│   │   └── Common.lean        # Shared emission helpers (indentation, escaping)
│   │
│   └── Correctness/
│       ├── Bridge.lean        # assignmentsToStmt_correct (generalized from LeanScribe)
│       ├── ArithCorrect.lean  # Proof that ArithExpr instance is sound
│       ├── BoolCorrect.lean   # Proof that BoolExpr instance is sound
│       ├── ImpCorrect.lean    # Proof that ImpStmt instance is sound
│       └── Compose.lean       # Composition theorems: if A,B sound then seq(A,B) sound
│
├── Tests/
│   ├── Integration.lean       # End-to-end tests
│   ├── Regression.lean        # LeanScribe regression (same inputs → same outputs)
│   └── Stress.lean            # Fuel stress, nesting depth, edge cases
│
└── scripts/                   # Build, benchmark, CI scripts
```

---

## Dependencies

### Lean 4 ecosystem

| Dependency | Version | Purpose |
|---|---|---|
| `leanprover/lean4` | v4.26.0 | Toolchain |
| `leanprover-community/mathlib4` | v4.26.0 | `CommRing`, `ring` tactic, `DecidableEq` |
| `LeanScribe` | v3.0.0 (local) | First frontend, test oracle, proven patterns |

### LeanScribe integration

Trust-Lean depends on LeanScribe as a Lake dependency:

```lean
-- lakefile.lean
require LeanScribe from FileSystem.mk "../LeanScribe"
-- or: require LeanScribe from git "https://github.com/.../LeanScribe" @ "v3.0.0"
```

This imports:
- `LeanScribe.Basic` — `Expr`, `BoolExpr`, `denote`, `denoteBool`
- `LeanScribe.LowLevel` — `VarName`, `BinOp` (base), `Assignment`, `LowLevelExpr` (base)
- `LeanScribe.Interpret` — `evalProgram`, `evalLowLevelExpr` (base), `evalStmt` (reference)
- `LeanScribe.CodeGen` — `lowerExpr`, `lowerToStmt`, `lowerBoolExpr`, `lowerBoolToStmt`
- `LeanScribe.Correctness` — `toLowLevel_correct`, `lowerToStmt_correct`, `lowerBoolExpr_correct`, `lowerIfStmt_correct`, `lowerWhileStmt_correct`, `lowerIfExpr_correct`, `evalStmt_fuel_mono`, `assignmentsToStmt_correct`

Trust-Lean **extends** (not modifies) these types. It defines its own `Stmt` with additional constructors, its own `Value` type, and its own `evalStmt` that handles the extended IR. Bridge lemmas connect the two: for inputs that LeanScribe can handle, Trust-Lean's pipeline must agree with LeanScribe's.

---

## Key Design Decisions (informed by LeanScribe lessons)

### 1. Pure function environments for proofs (L-analysis from LeanScribe)

`LowLevelEnv = VarName → Value` for the proof layer. `ExtHashMap VarName Value` as optional runtime layer with bridge lemma. LeanScribe proved that pure functions have ideal `simp` infrastructure; `ExtHashMap` lacks some lemmas needed for deep proof chains.

### 2. Fuel-based semantics (convergence of CertiCoq + Clight + LeanScribe)

Fuel only decreases in `while`/`for`. Other constructs ignore fuel. This is the model LeanScribe proved correct — `evalStmt_fuel_mono` depends on this design. Deviation would require reproving monotonicity.

### 3. Outcome restricted monotonicity (LeanScribe L-265)

`evalStmt_fuel_mono` is restricted to `Outcome.normal`. It is FALSE for `Outcome.outOfFuel` (counterexample: `while(false) skip` with fuel 0 vs fuel 1). Trust-Lean inherits this restriction. New outcomes (break, continue, return) need their own monotonicity analysis — break/return are fuel-independent (like assign), continue requires care inside while.

### 4. IMP pattern for source languages (LeanScribe L-248)

Separate inductives for expressions and boolean expressions (not type-indexed AST). Per LeanScribe's BoolExpr insights (§7.1): phantom types cause proof explosion. Each frontend defines its own AST and provides `CodeGenerable`/`CodeGenSound` instances.

### 5. SSA property preserved (LeanScribe insight from CFG Machines paper)

Temporaries (`VarName.temp n`) are assigned exactly once per basic block. User variables (`VarName.user v`) may be reassigned in loops. This property is inherited from LeanScribe's let-lifting and is essential for correctness of the environment model.

### 6. `for` as sugar over `while` (Clight decomposition)

`for(init; cond; step) body` desugars to `seq init (while cond (seq body step))`. This means no separate proof for `for` — correctness follows from `while` and `seq` correctness. Backend emitters can pattern-match `for_` to emit idiomatic target code.

### 7. Decomposed proof modules (learned from LeanScribe's 880 LOC monolith)

Each frontend gets its own correctness file. Shared proof infrastructure (fuel mono, bridge lemmas, equation lemmas) lives in `Core/`. This prevents the monolith problem: adding a new frontend doesn't require touching existing proof files.

---

## Lessons Registry (from LeanScribe, applicable to Trust-Lean)

| ID | Lesson | Application |
|---|---|---|
| L-134 to L-138 | DAG framework | Build dependency DAG before coding. De-risk fundacionales first |
| L-069, L-077 | WF-recursive equation lemmas | `simp only [f]` not `rfl`/`unfold`. No inline match in WF-recursive |
| L-099, L-106 | Extract predicates to @[simp] functions | Required for evalStmt pattern matching |
| L-114 | Foundational properties first | Value injectivity/disjointness before any correctness proof |
| L-148 | foldl_invariant_mem | For loop reasoning with bounded indices |
| L-172 | `match h :` for boolean predicates | Avoid splitter crash in by_cases |
| L-173 | Bool.false_eq_true + ite_false in simp set | Essential for boolean proof goals |
| L-200 | dite vs ite for clean hypotheses | Always `if h : cond` (Prop), not `if cond == val` (BEq) |
| L-203 to L-206 | Fuel-based totality patterns | evalStmt model, pigeonhole for termination |
| L-243 to L-248 | LeanScribe Fase 2 lessons | Bridge lemmas, BinOp meta-lemma, Outcome design |
| L-252 | DecidableEq via deriving | For Value, Outcome, BinOp |
| L-265 to L-269 | LeanScribe Fase 2.5 lessons | `have` with explicit type for let-binding opacity, fuel as recursion bound not resource |

---

## Axiom Budget

| Axiom | Source | Acceptable? |
|---|---|---|
| `propext` | Lean 4 stdlib | Yes (proposition extensionality) |
| `Quot.sound` | Lean 4 stdlib | Yes (quotient soundness) |
| `Classical.choice` | `by_cases` tactic | Advisory — prefer `match` on `Bool` where possible (per LeanScribe L-267) |

**Target**: 0 custom axioms, 0 sorry across all `CodeGenSound` instances.

---

## Risk Analysis

| Risk | Probability | Impact | Mitigation |
|---|---|---|---|
| Value type complicates all proofs (4 cases per match) | HIGH | MEDIUM | Start with 2 variants only (Int, Bool). Add more incrementally |
| Typeclass instance search slow in Lean 4 | MEDIUM | LOW | Use explicit instance passing if needed |
| LeanScribe API changes break Trust-Lean | LOW | HIGH | Pin LeanScribe at v3.0.0 tag. Never depend on `private` definitions |
| Correctness proof for ImpStmt (while + assignments) harder than expected | MEDIUM | HIGH | De-risk with sorry sketch before implementation. Reuse LeanScribe's while proof pattern |
| `ExtHashMap` API insufficient for proofs | MEDIUM | MEDIUM | Fallback to pure function env (proven in LeanScribe) |
| Rust backend ownership model too complex | HIGH | MEDIUM | Start with subset of Rust (no borrows, just `let mut` + stack variables) |

---

## Version Plan (high level)

| Version | Contents | Depends on |
|---|---|---|
| **v0.1** | Core IR (Value + extended Stmt + Outcome) + evalStmt + fuel_mono | Mathlib |
| **v0.2** | CodeGenerable/CodeGenSound typeclasses + ArithExpr instance (wraps LeanScribe) | v0.1 + LeanScribe v3.0 |
| **v0.3** | BoolExpr instance + ImpStmt frontend | v0.2 |
| **v0.4** | C backend (BackendEmitter) | v0.1 |
| **v0.5** | Rust backend | v0.4 |
| **v1.0** | 3 frontends + 2 backends + 0 sorry + comprehensive tests | v0.3 + v0.5 |
| **v2.0+** | Domain-specific frontends (AMO, vr1cs, Merkle, PolyCom) | v1.0 |

---

## AMO-Lean Integration Strategy

### Context

Trust-Lean's first real-world application is complementing **amo-lean**, a verified optimizer for the FRI protocol. When integrated:
- **amo-lean** = Frontend (mathematical brain: MatExpr → SigmaExpr → ExpandedSigma)
- **Trust-Lean** = Backend (verified codegen engine: Stmt → C/Rust with proof)

The composition creates a **Verified Cryptographic Compiler End-to-End**:
```
MatExpr (pure math) → SigmaExpr (loop IR) → ExpandedSigma (scalar ops) → Stmt (Trust-Lean IR) → C/Rust
         amo-lean existing pipeline                                         BRIDGE         Trust-Lean
```

### AMO-Lean's Architecture (relevant to integration)

**Pipeline**: `MatExpr α m n → SigmaExpr → ExpandedSigma → C/Rust code`

**Key types** (from `AmoLean/Sigma/Basic.lean`, `AmoLean/Matrix/Basic.lean`):

```lean
-- High-level matrix expression (typed by dimensions)
inductive MatExpr (α : Type) : Nat → Nat → Type where
  | identity | zero | dft | ntt | twiddle | perm | kron | compose
  | add | smul | transpose | elemwise | mdsApply | addRoundConst | ...

-- Loop IR (Sigma-SPL from SPIRAL project)
inductive SigmaExpr where
  | compute : Kernel → Gather → Scatter → SigmaExpr
  | loop    : (n : Nat) → (loopVar : LoopVar) → SigmaExpr → SigmaExpr
  | seq     : SigmaExpr → SigmaExpr → SigmaExpr
  | par     : SigmaExpr → SigmaExpr → SigmaExpr
  | temp    : (size : Nat) → SigmaExpr → SigmaExpr
  | nop     : SigmaExpr

-- Expanded scalar operations (SSA form)
abbrev ScalarBlock = List ScalarAssign
structure ScalarAssign where
  target : ScalarVar    -- e.g., x0, y1, t3
  value  : ScalarExpr   -- e.g., add (x 0) (x 1)

-- Memory model
structure Memory (α : Type) where
  data : Array α
abbrev LoopEnv := LoopVar → Nat
```

**Fields**: Works over `[Field α]` generically. Concrete instances: Goldilocks (UInt64), BabyBear (UInt32).

**Gather/Scatter**: Read/write n elements from/to Memory with affine index patterns (`base + stride * loopVar`).

**Key observation**: `ExpandedSigma` already expands all Kernels to `ScalarBlock` (list of SSA assignments). This is structurally very close to Trust-Lean's `Stmt.assign + Stmt.seq`.

### Integration Strategy: ExpandedSigma → Stmt (NOT SigmaExpr → Stmt)

**Critical design decision**: The bridge operates at the `ExpandedSigma` level, not `SigmaExpr`.

**Why this is superior to direct SigmaExpr → Stmt translation**:

| Aspect | SigmaExpr → Stmt (naive) | ExpandedSigma → Stmt (proposed) |
|---|---|---|
| Kernel handling | Must lower abstract kernels (DFT₂, NTT, Sbox) to Stmt | Already expanded to scalar ops |
| Gather/Scatter | Must translate index patterns to load/store | Already resolved to concrete index calculations |
| Proof complexity | Monolithic: kernel expansion + memory bridge + loop translation | Decomposed into 2 independent proofs |
| Reuse | Discards amo-lean's existing expansion infrastructure | Leverages `expandSigmaExpr` (already tested) |
| ScalarAssign → Stmt.assign | N/A (kernel is opaque) | Nearly 1:1 mapping |

**The proof decomposes into two independent parts**:
1. **In amo-lean** (already mostly done): `evalSigma ≡ evalExpandedSigma` — expanding kernels preserves semantics
2. **In Trust-Lean** (the bridge): `evalExpandedSigma ≡ evalStmt` — the translation to Stmt preserves semantics

### Translation Sketch

```lean
-- Phase 1: ScalarExpr → LowLevelExpr (trivial, structural)
def scalarExprToLLExpr : ScalarExpr → LowLevelExpr
  | .var v   => .varRef (toVarName v)
  | .const n => .litInt n
  | .neg e   => .unaryOp .neg (scalarExprToLLExpr e)
  | .add a b => .binOp .add (scalarExprToLLExpr a) (scalarExprToLLExpr b)
  | .sub a b => .binOp .sub (scalarExprToLLExpr a) (scalarExprToLLExpr b)
  | .mul a b => .binOp .mul (scalarExprToLLExpr a) (scalarExprToLLExpr b)

-- Phase 2: ScalarAssign → Stmt (trivial)
def scalarAssignToStmt (a : ScalarAssign) : Stmt :=
  .assign (toVarName a.target) (scalarExprToLLExpr a.value)

-- Phase 3: ScalarBlock → Stmt (fold over seq)
def scalarBlockToStmt : ScalarBlock → Stmt
  | []      => .skip
  | [a]     => scalarAssignToStmt a
  | a :: as => .seq (scalarAssignToStmt a) (scalarBlockToStmt as)

-- Phase 4: Gather → sequence of Stmt.load
-- Reads g.count elements from array at base + stride*i into local vars
def gatherToStmt (env : LoopVarMapping) (g : Gather) : Stmt :=
  List.range g.count |>.foldl (fun acc i =>
    let idx := evalIdxExpr env g.baseAddr + g.stride * i
    .seq acc (.load (inputVar i) (arrayRef) (.litInt idx))
  ) .skip

-- Phase 5: Scatter → sequence of Stmt.store
-- Writes local vars to array at base + stride*i
def scatterToStmt (env : LoopVarMapping) (s : Scatter) : Stmt :=
  List.range s.count |>.foldl (fun acc i =>
    let idx := evalIdxExpr env s.baseAddr + s.stride * i
    .seq acc (.store (arrayRef) (.litInt idx) (.varRef (outputVar i)))
  ) .skip

-- Phase 6: ExpandedSigma → Stmt (the main bridge)
def expandedSigmaToStmt : ExpandedSigma → Stmt
  | .scalar kernel gather scatter =>
      .seq (gatherToStmt gather)
           (.seq (scalarBlockToStmt kernel.body)
                 (scatterToStmt scatter))
  | .loop n loopVar body =>
      -- Trust-Lean has for_ : init → cond → step → body → Stmt
      .for_ (.assign (loopVarName loopVar) (.litInt 0))
             (.binOp .ltOp (.varRef (loopVarName loopVar)) (.litInt n))
             (.assign (loopVarName loopVar)
                (.binOp .add (.varRef (loopVarName loopVar)) (.litInt 1)))
             (expandedSigmaToStmt body)
  | .seq s1 s2 =>
      .seq (expandedSigmaToStmt s1) (expandedSigmaToStmt s2)
  | .par s1 s2 =>
      -- For sequential semantics, par = seq
      .seq (expandedSigmaToStmt s1) (expandedSigmaToStmt s2)
  | .temp size body =>
      -- Allocate temp array, execute body
      .seq (allocTemp size) (expandedSigmaToStmt body)
  | .nop => .skip
```

### Value Type Extension Required

Trust-Lean v0.1 has `Value = int Int | bool Bool`. For amo-lean integration:

```lean
inductive Value where
  | int    : Int → Value        -- v0.1: arithmetic expressions
  | bool   : Bool → Value       -- v0.1: boolean expressions
  | uint64 : UInt64 → Value     -- v1.1+: Goldilocks field elements
  | uint32 : UInt32 → Value     -- v1.1+: BabyBear field elements
  | array  : Array Value → Value -- v1.1+: Memory representation
```

**Key principle**: Field axioms (commutativity, associativity, inverses) live in amo-lean, NOT in Trust-Lean. Trust-Lean only needs to faithfully compile scalar operations over concrete machine types. The field correctness is established in amo-lean's `AlgebraicSemantics.lean` (generic over `[Field α]`).

### Memory Bridge Lemma

The critical bridge connects amo-lean's `Memory α` with Trust-Lean's `LowLevelEnv`:

```lean
-- Memory is represented as Value.array in Trust-Lean's environment
-- amo-lean's Memory.read corresponds to Trust-Lean's Stmt.load
-- amo-lean's Memory.write corresponds to Trust-Lean's Stmt.store

theorem memory_bridge_read (mem : Memory α) (idx : Nat) (llEnv : LowLevelEnv)
    (hmem : llEnv (.array "mem") = Value.array (mem.data.map toValue)) :
    toValue (mem.read idx) = evalLoad llEnv "mem" idx

theorem memory_bridge_write (mem : Memory α) (idx : Nat) (val : α) (llEnv : LowLevelEnv)
    (hmem : llEnv (.array "mem") = Value.array (mem.data.map toValue)) :
    let mem' := mem.write idx val
    let llEnv' := execStore llEnv "mem" idx (toValue val)
    llEnv' (.array "mem") = Value.array (mem'.data.map toValue)
```

### End-to-End Correctness Chain

When complete, the following chain is machine-checked:

```
1. evalMatExprAlg ≡ evalSigmaAlg
   (amo-lean: lowering_algebraic_correct — induction on MatExpr)

2. evalSigmaAlg ≡ evalExpandedSigma
   (amo-lean: kernel expansion preserves semantics)

3. evalExpandedSigma ≡ evalStmt (expandedSigmaToStmt ...)
   (Trust-Lean bridge: CodeGenSound instance)

4. evalStmt ≡ C/Rust code emitted
   (Trust-Lean: BackendEmitter — trusted pretty-printer, outside TCB)

∴ By transitivity: Pure Mathematics ≡ Emitted C/Rust Code
```

### Phased Integration Plan

| Phase | Version | Contents | Depends on |
|---|---|---|---|
| **Build Trust-Lean core** | v0.1–v1.0 | Framework with Int\|Bool, 3 frontends, 2 backends | — |
| **Extend Value types** | v1.1 | +Value.uint64, Value.uint32, Value.array + evalStmt for load/store with arrays | v1.0 |
| **Build bridge** | v1.2 | ExpandedSigma → Stmt translation + CodeGenSound proof | v1.1 + amo-lean |
| **Full integration** | v2.0 | CodeGenerable/CodeGenSound for SigmaExpr (composing expand + bridge) | v1.2 |

### Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Value.array complicates proofs (nested induction) | HIGH | Start with fixed-size arrays; add dynamic later |
| evalStmt_fuel_mono may not extend to load/store with arrays | MEDIUM | Verify with sorry sketch before building on it |
| amo-lean's ExpandedSigma API changes | LOW | Pin amo-lean version, define thin wrapper interface |
| Gather/Scatter index arithmetic proof (affine expressions) | MEDIUM | Use omega tactic; indices are affine (linear) |
| Memory aliasing (gather reads overlapping with scatter writes) | MEDIUM | Trust-Lean's store/load has no aliasing by construction (functional env) |
