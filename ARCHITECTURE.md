# Trust-Lean: Architecture

## Current Version: v1.2.0


### CBackend Industrial

**Contents**: Upgrade del CBackendEmitter a grado industrial: sanitización higiénica, paréntesis agresivos, llaves obligatorias, store/load fix, headers autocontenidos, propiedades formales

**Files**:
- `TrustLean/Backend/Common.lean`
- `TrustLean/Backend/CBackend.lean`
- `TrustLean/Backend/CBackendProperties.lean`
- `TrustLean/Tests/CBackendIntegration.lean`

#### DAG (v1.2.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N9.1 Sanitización y Helpers | FUND | — | completed ✓ |
| N9.2 CBackend Refactor | CRIT | N9.1 | completed ✓ |
| N9.3 Propiedades Formales CBackend | PAR | N9.2 | completed ✓ |
| N9.4 Integration Tests + Regression | PAR | N9.2 | completed ✓ |
| N9.5 Zero Sorry + Final Audit | HOJA | N9.3, N9.4 | completed ✓ |

#### Formal Properties (v1.2.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N9.1 | sanitizeIdentifier output is never a C99 keyword | INVARIANT | P0 |
| N9.1 | sanitizeIdentifier output is a valid C identifier | INVARIANT | P0 |
| N9.1 | sanitizeIdentifier is idempotent | INVARIANT | P1 |
| N9.2 | stmtToC produces balanced braces | INVARIANT | P1 |
| N9.2 | stmtToC is deterministic (pure function) | EQUIVALENCE | P0 |
| N9.3 | exprToC fully parenthesizes all binary sub-expressions | INVARIANT | P0 |
| N9.4 | No regressions in v1.0.0 Pipeline.emit | PRESERVATION | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Sanitización y Helpers**: N9.1 — closed 2026-02-21
- [x] **CBackend Refactor**: N9.2 — closed 2026-02-21
- [x] **Properties + Tests**: N9.3, N9.4 — closed 2026-02-21
- [x] **Zero Sorry Audit**: N9.5 — closed 2026-02-21

---

## Previous Versions

### v1.1.0

### Fase 1: Core IR + Semántica

**Contents**: Foundation layer: Value sum type, 12-constructor Stmt IR, fuel-based evaluator, store/load lemmas with @[simp], and the critical evalStmt_fuel_mono gate theorem. Maps to DESIGN_SPEC v0.1.

**Files**:
- `TrustLean/Core/Value.lean`
- `TrustLean/Core/Stmt.lean`
- `TrustLean/Core/Eval.lean`
- `TrustLean/Core/Foundation.lean`
- `TrustLean/Core/FuelMono.lean`

#### DAG (v1.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N1.1 Value + LowLevelExpr | FUND | — | completed ✓ |
| N1.2 Stmt IR (12 constructors) | FUND | N1.1 | completed ✓ |
| N1.3 Evaluator (fuel-based) | CRIT | N1.1, N1.2 | completed ✓ |
| N1.4 Foundation Lemmas | CRIT | N1.3 | completed ✓ |
| N1.5 evalStmt_fuel_mono (GATE) | CRIT | N1.4 | completed ✓ |

#### Formal Properties (v1.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N1.1 Value + LowLevelExpr | evalBinOp on matching types produces Some result | SOUNDNESS | P0 |
| N1.1 Value + LowLevelExpr | evalBinOp add/mul is commutative | EQUIVALENCE | P1 |
| N1.3 Evaluator | evalStmt skip returns normal with unchanged env | INVARIANT | P0 |
| N1.3 Evaluator | evalStmt seq with skip is left-identity | EQUIVALENCE | P1 |
| N1.3 Evaluator | evalStmt with fuel 0 returns outOfFuel for non-skip | INVARIANT | P0 |
| N1.4 Foundation Lemmas | store then load at same index roundtrips | INVARIANT | P0 |
| N1.4 Foundation Lemmas | store at index i does not affect load at j ≠ i | INVARIANT | P0 |
| N1.5 evalStmt_fuel_mono | fuel monotonicity: more fuel preserves normal results | SOUNDNESS | P0 |
| N1.5 evalStmt_fuel_mono | break_/continue_/return_ outcomes are fuel-independent | INVARIANT | P1 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Stubs ejecutables en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Bloque 1: Value Foundation**: N1.1 — closed 2026-02-20
- [x] **Bloque 2: Stmt IR**: N1.2 — closed 2026-02-20
- [x] **Bloque 3: Evaluator**: N1.3 — closed 2026-02-20
- [x] **Bloque 4: Foundation Lemmas**: N1.4 — closed 2026-02-20
- [x] **Bloque 5: FuelMono Gate**: N1.5 — closed 2026-02-20

### Fase 2: Typeclasses + ArithExpr Frontend

**Contents**: Typeclass infrastructure (CodeGenerable/CodeGenSound/BackendEmitter) and first frontend (ArithExpr) as proof-of-concept of the full compilation+verification pipeline. Maps to DESIGN_SPEC v0.2.

**Files**:
- `TrustLean/Typeclass/CodeGenerable.lean`
- `TrustLean/Typeclass/CodeGenSound.lean`
- `TrustLean/Frontend/ArithExpr/Syntax.lean`
- `TrustLean/Frontend/ArithExpr/Compile.lean`
- `TrustLean/Frontend/ArithExpr/Correctness.lean`

#### DAG (v1.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N2.1 Typeclass Infrastructure | CRIT | N1.5 | completed ✓ |
| N2.2 ArithExpr Frontend (GATE) | CRIT | N2.1 | completed ✓ |

#### Formal Properties (v1.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N2.1 Typeclass Infrastructure | CodeGenerable.compile produces well-typed Stmt | SOUNDNESS | P0 |
| N2.2 ArithExpr Frontend | ArithExpr compile soundness: eval commutes with compilation | SOUNDNESS | P0 |
| N2.2 ArithExpr Frontend | Constant folding preserves semantics | PRESERVATION | P1 |

> **Nota**: Stubs ejecutables en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Bloque 6: Typeclasses**: N2.1 — closed 2026-02-20
- [x] **Bloque 7: ArithExpr Gate**: N2.2 — closed 2026-02-20

### Fase 3: Extended Frontends

**Contents**: BoolExpr and ImpStmt frontends. ImpStmt handles control flow (while, for_, break/continue/return) and is the most complex frontend. Both produce CodeGenSound proofs. Maps to DESIGN_SPEC v0.3.

**Files**:
- `TrustLean/Frontend/BoolExpr/Syntax.lean`
- `TrustLean/Frontend/BoolExpr/Compile.lean`
- `TrustLean/Frontend/BoolExpr/Correctness.lean`
- `TrustLean/Frontend/ImpStmt/Syntax.lean`
- `TrustLean/Frontend/ImpStmt/Compile.lean`
- `TrustLean/Frontend/ImpStmt/Correctness.lean`

#### DAG (v1.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N3.1 BoolExpr Frontend | PAR | N2.2 | completed ✓ |
| N3.2 ImpStmt Frontend | CRIT | N2.2 | completed ✓ |

#### Formal Properties (v1.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N3.1 BoolExpr Frontend | BoolExpr compile soundness | SOUNDNESS | P0 |
| N3.1 BoolExpr Frontend | Short-circuit: false ∧ _ does not evaluate right operand | OPTIMIZATION | P1 |
| N3.2 ImpStmt Frontend | ImpStmt compile soundness for control flow | SOUNDNESS | P0 |
| N3.2 ImpStmt Frontend | while with false condition is skip | EQUIVALENCE | P1 |

> **Nota**: Stubs ejecutables en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Bloque 8: BoolExpr**: N3.1 — closed 2026-02-20
- [x] **Bloque 9: ImpStmt**: N3.2 — closed 2026-02-21

### Fase 4: Backends

**Contents**: C and Rust backends via BackendEmitter typeclass. Common emission utilities, then C (v0.4) and Rust (v0.5). String emission with structural correctness.

**Files**:
- `TrustLean/Backend/Common.lean`
- `TrustLean/Backend/CBackend.lean`
- `TrustLean/Backend/RustBackend.lean`

#### DAG (v1.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N4.1 Common + C Backend | PAR | N2.2 | completed ✓ |
| N4.2 Rust Backend | HOJA | N4.1 | completed ✓ |

#### Formal Properties (v1.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N4.1 Common + C Backend | stmtToC produces balanced braces | INVARIANT | P0 |
| N4.1 Common + C Backend | stmtToC on skip produces empty/semicolon | INVARIANT | P1 |
| N4.2 Rust Backend | stmtToRust produces balanced braces | INVARIANT | P0 |

> **Nota**: Stubs ejecutables en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Bloque 10: C Backend**: N4.1 — closed 2026-02-21
- [x] **Bloque 11: Rust Backend**: N4.2 — closed 2026-02-21

### Fase 5: Integration + Consolidation

**Contents**: End-to-end pipeline wiring, integration tests, zero-sorry audit, and preparation for amo-lean bridge (ExpandedSigma→Stmt). Maps to DESIGN_SPEC v1.0.

**Files**:
- `TrustLean/Pipeline.lean`
- `TrustLean/Tests/Integration.lean`

#### DAG (v1.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N5.1 Pipeline + Integration Tests | HOJA | N3.1, N3.2, N4.2 | completed ✓ |
| N5.2 Zero Sorry Audit | HOJA | N5.1 | completed ✓ |

#### Formal Properties (v1.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N5.1 Pipeline + Integration | End-to-end: DSL source → backend output preserves semantics | SOUNDNESS | P0 |
| N5.2 Zero Sorry Audit | Zero sorry across all modules | SOUNDNESS | P0 |

> **Nota**: N5.2 verified mechanically (grep), not SlimCheck.

#### Bloques

- [x] **Bloque 12: Pipeline**: N5.1 — closed 2026-02-21
- [x] **Bloque 13: Zero Sorry Audit**: N5.2 — closed 2026-02-21

### Fase 6: Bridge Foundation

**Contents**: Wrapper types for amo-lean constructs (ScalarExpr, ScalarVar, IdxExpr, ExpandedSigma, etc.), VarName mapping with constructor-based partitioning, bridge predicate (two-part: scalarBridge + loopBridge), denotational semantics (evalScalarExpr, evalIdxExpr, evalExpandedSigma), and expression-level translation (scalarExprToLLExpr, idxExprToLLExpr) with correctness proofs. The GATE node proves expression translation is a homomorphism. Maps to DESIGN_SPEC § AMO-Lean Integration Strategy.

**Files**:
- `TrustLean/Bridge/Types.lean`
- `TrustLean/Bridge/Semantics.lean`
- `TrustLean/Bridge/ExprTranslation.lean`

**Design decisions** (from QA review):
- **Wrapper types** (not direct lake dependency): Bridge defines its own types mirroring amo-lean, enabling independent compilation. Future v2.0 may use direct imports.
- **Two-part bridge predicate**: `scalarBridge : (ScalarVar → Int) → LowLevelEnv → Prop` + `loopBridge : (LoopVar → Nat) → LowLevelEnv → Prop`. Separation enables modular proofs.
- **VarName mapping**: Constructor-based partitioning — scalar→`.user "s_{name}_{idx}"`, loop→`.loopVar v`, temp→`CodeGenState.freshVar`. Injectivity is FREE from constructor disjointness.
- **Sequential interpretation of .par**: `evalExpandedSigma(.par s1 s2) = evalExpandedSigma(.seq s1 s2)`. Documented as v1.1.0 simplification; true parallelism deferred to v2.0.
- **Value.int sufficient**: ScalarExpr evaluates to Int; field axioms live in amo-lean, not Trust-Lean.

#### DAG (v1.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N6.1 Bridge Types + Semantics | FUND | N1.5 | completed ✓ |
| N6.2 Expression Translation + Proofs (GATE) | CRIT | N6.1 | completed ✓ |

#### Formal Properties (v1.1.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N6.1 Bridge Types + Semantics | evalScalarExpr deterministic on well-typed env | SOUNDNESS | P0 |
| N6.1 Bridge Types + Semantics | evalExpandedSigma(.par) = evalExpandedSigma(.seq) | EQUIVALENCE | P0 |
| N6.1 Bridge Types + Semantics | VarName mapping injective (constructor disjointness) | INVARIANT | P0 |
| N6.1 Bridge Types + Semantics | evalScalarExpr(.lit n) = n independent of environment | INVARIANT | P1 |
| N6.2 Expression Translation | scalarExprToLLExpr correctness: evalLLExpr ∘ translate = evalScalarExpr | SOUNDNESS | P0 |
| N6.2 Expression Translation | idxExprToLLExpr correctness: evalLLExpr ∘ translate = evalIdxExpr | SOUNDNESS | P0 |
| N6.2 Expression Translation | Translation preserves structure (homomorphism for binary ops) | PRESERVATION | P1 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Stubs ejecutables en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Bloque 14: Bridge Types + Semantics**: N6.1 — closed 2026-02-21
- [x] **Bloque 15: Expression Translation Gate**: N6.2 — closed 2026-02-21

### Fase 7: Statement Translation

**Contents**: Statement-level translation functions. Scalar operations (scalarAssignToStmt, scalarBlockToStmt) use explicit recursion over List (not foldl) for clean induction. Memory operations (gatherToStmt, scatterToStmt) use induction on count:Nat with stride-based index computation. The main bridge function (expandedSigmaToStmt) threads CodeGenState for fresh variable naming and handles all 6 ExpandedSigma constructors via structural recursion.

**Files**:
- `TrustLean/Bridge/ScalarTranslation.lean`
- `TrustLean/Bridge/MemoryTranslation.lean`
- `TrustLean/Bridge/Compile.lean`

**Design decisions** (from QA review):
- **Explicit recursion > foldl**: `| [] => .skip | a::as => .seq (compile a) (rec as)`. Standard induction with `generalizing`.
- **CodeGenState threading**: `expandedSigmaToStmt : ExpandedSigma → CodeGenState → Stmt × CodeGenState`. Prevents temp variable collision in nested `.temp` blocks.
- **Fuel composition via max**: Sequential composition uses `Nat.max` (not `+`) for fuel bounds, consistent with v1.0.0 convention.
- **Loop fuel accounting**: Per-iteration fuel = init + cond_check + body + step (not just body).

#### DAG (v1.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N7.1 Scalar Statement Translation + Proofs | PAR | N6.2 | completed ✓ |
| N7.2 Memory Translation + Proofs | PAR | N6.2 | completed ✓ |
| N7.3 Main Bridge Function (Compile) | CRIT | N7.1, N7.2 | completed ✓ |

#### Formal Properties (v1.1.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N7.1 Scalar Statement Translation | scalarAssignToStmt correctness: post-env at target = evalScalarExpr of source | SOUNDNESS | P0 |
| N7.1 Scalar Statement Translation | scalarBlockToStmt correctness: sequential execution matches block evaluation | SOUNDNESS | P0 |
| N7.1 Scalar Statement Translation | Empty block translates to .skip | EQUIVALENCE | P1 |
| N7.2 Memory Translation | gatherToStmt correctness: loads match source array at computed indices | SOUNDNESS | P0 |
| N7.2 Memory Translation | scatterToStmt correctness: stores match values at computed indices | SOUNDNESS | P0 |
| N7.2 Memory Translation | Single-element gather/scatter correctness | INVARIANT | P1 |
| N7.3 Main Bridge Function | expandedSigmaToStmt terminates (structural recursion) | INVARIANT | P0 |
| N7.3 Main Bridge Function | All 6 constructors handled exhaustively | SOUNDNESS | P0 |
| N7.3 Main Bridge Function | Fuel bound computable from ExpandedSigma structure | INVARIANT | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Stubs ejecutables en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **Bloque 16: Scalar + Memory Translation** (AGENT_TEAM): N7.1, N7.2
- [ ] **Bloque 17: Main Bridge Function**: N7.3

### Fase 8: Correctness + Integration

**Contents**: The capstone correctness theorem `expandedSigmaToStmt_correct` proving the full simulation diagram: for any well-typed ExpandedSigma program, the compiled Stmt evaluates (with sufficient fuel) to an environment that agrees with the denotational semantics via the bridge predicate. Integration tests and zero-sorry audit across all v1.1.0 modules.

**Files**:
- `TrustLean/Bridge/Correctness.lean`
- `TrustLean/Bridge.lean`
- `TrustLean/Tests/BridgeIntegration.lean`

#### DAG (v1.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N8.1 Bridge Correctness Proof | CRIT | N7.3 | completed ✓ |
| N8.2 Integration Tests + Zero Sorry | HOJA | N8.1 | completed ✓ |

#### Formal Properties (v1.1.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N8.1 Bridge Correctness | expandedSigmaToStmt_correct: full simulation diagram | SOUNDNESS | P0 |
| N8.1 Bridge Correctness | Bridge predicate preservation through execution | PRESERVATION | P0 |
| N8.1 Bridge Correctness | Fuel sufficiency: computed bound is sufficient | INVARIANT | P0 |
| N8.2 Integration + Zero Sorry | Zero sorry across all modules (v1.0.0 + v1.1.0) | SOUNDNESS | P0 |
| N8.2 Integration + Zero Sorry | No regressions in v1.0.0 functionality | INVARIANT | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Stubs ejecutables en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Bloque 18: Bridge Correctness**: N8.1
- [x] **Bloque 19: Integration + Zero Sorry**: N8.2 — closed 2026-02-21

---

## Version History

| Version | Date | Highlights |
|---------|------|------------|
| **v1.1.0** | Feb 2026 | Current: ExpandedSigma → Stmt bridge (amo-lean integration) |
| **v1.0.0** | Feb 2026 | Core IR (12 constructors) + 3 frontends + 2 backends + pipeline |



---

## Lessons (current)

Project-specific lessons learned during current version.
Generalized lessons should be migrated to `~/Documents/claudio/lecciones/lean4/`.
