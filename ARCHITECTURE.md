# Trust-Lean: Architecture

## Current Version: v4.0.0

### Scope

MicroRust targets the same imperative subset as MicroC: scalars, arrays, loops, conditionals, function calls. Ownership, borrowing, lifetimes, traits, and generics are out of scope. The emitted Rust uses only owned values (`let mut x: i64`).

### Design Decisions (v4.0.0)

1. **Shared AST (no rename)**: `MicroCStmt`/`MicroCExpr`/`MicroCEnv` and ALL evaluators (`evalMicroC`, `evalMicroC_int64`, `evalMicroC_uint32/64`, `evalMicroC_withCalls`) are language-neutral. Rust wrapping arithmetic = MicroC wrapping arithmetic (verified: both use `wrapInt64`/`wrapUInt32`/`wrapUInt64`). MicroRust imports these directly. Type aliases `MicroRustStmt := MicroCStmt` etc. in `Defs.lean` for readability.
2. **TrustLean/MicroRust/ directory**: New files for Rust-specific layers. Imports `TrustLean.MicroC.*` for shared infrastructure. No MicroC files modified.
3. **varNameToRust**: Uses `sanitizeIdentifierRust` (53 Rust keywords, `_tl_` prefix). Proven not_keyword, nonempty, valid, idempotent in Common.lean (v3.2).
4. **VarNameInjectiveRust**: Same pattern as MicroC — assumed as hypothesis in simulation, not proved universally. `sanitizeIdentifierRust` is non-injective (L-616) but injective on practical variable sets.
5. **microRustBridge**: `∀ v, env v = mcEnv (varNameToRust v)`. Same structure as `microCBridge` but with Rust sanitizer.
6. **WellFormedBaseRust**: `sanitizeIdentifierRust name = name` (vs `sanitizeIdentifier` for C). Both `"mem"` passes both sanitizers (verified by `native_decide`).
7. **Rust syntax in PrettyPrint/Parser**: No parens `if`/`while`, postfix `as i64`/`as i32` casts, `as usize` array index, `true`/`false` booleans. Fully parenthesized expressions (same as MicroC).
8. **Two independent chains**: Chain A (semantic: Translation → Bridge → Simulation) and Chain B (syntactic: PrettyPrint → Parser → Roundtrip) share no definitions until Integration. Can interleave execution.
9. **12 modules reused at zero cost**: AST, Eval, FuelMono, Int64, Int64Eval, Int64Agreement, Unsigned, UnsignedEval, UnsignedAgreement, UnsignedFuelMono, CallTypes, CallEval (3,524 LOC, 46% of MicroC).

### Fase 7: MicroRust Translation + Bridge + Simulation

**Contents**: Semantic core: translate Stmt to MicroRust (shared AST, Rust identifiers), bridge predicate, and master simulation theorem stmtToMicroRust_correct.

**Files**:
- `TrustLean/MicroRust/Defs.lean`
- `TrustLean/MicroRust/Translation.lean`
- `TrustLean/MicroRust/Bridge.lean`
- `TrustLean/MicroRust/Simulation.lean`
- `TrustLean/MicroRust/CallSimulation.lean`
- `TrustLean/MicroRust/UnsignedSimulation.lean`

#### DAG (v4.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N24.1 MicroRust Defs + Translation (varNameToRust, stmtToMicroRust) | FUND | — | pending |
| N24.2 microRustBridge + Correspondence Lemmas | FUND | N24.1 | pending |
| N24.3 stmtToMicroRust_correct (GATE Simulation Theorem) | CRIT | N24.1, N24.2 | pending |
| N24.4 CallSimulation + UnsignedSimulation for MicroRust (Lifting) | PAR | N24.3 | pending |

#### Formal Properties (v4.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N24.1 | stmtToMicroRust total on all Stmt constructors | INVARIANT | P0 |
| N24.1 | exprToMicroRust consistent with exprToMicroC (same AST output) | EQUIVALENCE | P0 |
| N24.1 | varNameToRust uses sanitizeIdentifierRust (not sanitizeIdentifier) | INVARIANT | P0 |
| N24.2 | microRustBridge preserved through environment updates | PRESERVATION | P0 |
| N24.2 | exprToMicroRust_bridge: expression evaluation respects bridge | SOUNDNESS | P0 |
| N24.3 | stmtToMicroRust_correct: forward simulation for all non-OOF outcomes | SOUNDNESS | P0 |
| N24.3 | WellFormedArrayBasesRust: store/load bases well-formed for Rust sanitizer | INVARIANT | P0 |
| N24.3 | Non-vacuity: concrete program simulation succeeds | SOUNDNESS | P0 |
| N24.4 | stmtToMicroRust_correct_withCalls: lifting to call-aware evaluator | SOUNDNESS | P0 |
| N24.4 | stmtToMicroRust_correct_uint32/64: lifting to unsigned evaluators | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **MicroRust Defs + Translation**: N24.1
- [ ] **Bridge + Correspondence**: N24.2
- [ ] **Simulation (GATE)**: N24.3
- [ ] **Call + Unsigned Simulation**: N24.4

### MicroRust Pretty-Printer + Parser + Roundtrip

**Contents**: Syntactic chain: Rust-syntax emission, Lean.Data.Parsec parser, and full roundtrip theorem parseMicroRust(microRustToString s) = some s.

**Files**:
- `TrustLean/MicroRust/PrettyPrint.lean`
- `TrustLean/MicroRust/Parser.lean`
- `TrustLean/MicroRust/RoundtripExpr.lean`
- `TrustLean/MicroRust/RoundtripStmt.lean`
- `TrustLean/MicroRust/RoundtripMaster.lean`

#### DAG (v4.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N25.1 microRustToString Pretty-Printer (Rust syntax) | PAR | — | pending |
| N25.2 parseMicroRust Parser (Rust syntax) | PAR | — | pending |
| N25.3 Expression Roundtrip (WFExprRust induction) | CRIT | N25.1, N25.2 | pending |
| N25.4 Statement Roundtrip + Master (WFStmtRust induction + master_roundtrip_rust) | CRIT | N25.3 | pending |

#### Formal Properties (v4.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N25.1 | microRustToString produces balanced braces | INVARIANT | P0 |
| N25.1 | microRustToString uses Rust syntax (no parens if/while, as casts) | INVARIANT | P0 |
| N25.2 | parseMicroRust terminates on all inputs | INVARIANT | P0 |
| N25.3 | parseMicroRustExpr(microRustExprToString e) = some e for WFExprRust | EQUIVALENCE | P0 |
| N25.4 | parseMicroRust(microRustToString s) = some s for WFStmtRust | EQUIVALENCE | P0 |
| N25.4 | master_roundtrip_rust: capstone roundtrip theorem | EQUIVALENCE | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **PrettyPrint + Parser (AGENT_TEAM)**: N25.1, N25.2
- [ ] **Expression Roundtrip**: N25.3
- [ ] **Statement Roundtrip + Master (GATE)**: N25.4

### Integration + Audit

**Contents**: End-to-end integration tests, non-vacuity witnesses, compatibility verification with MicroC pipeline, zero sorry audit, v4.0.0 tag.

**Files**:
- `TrustLean/MicroRust/Integration.lean`

#### DAG (v4.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N26.1 Integration Tests + Non-Vacuity + Compatibility | HOJA | N24.3, N24.4, N25.4 | pending |
| N26.2 Zero Sorry Audit + spec_audit + v4.0.0 Tag | HOJA | N26.1 | pending |

#### Formal Properties (v4.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N26.1 | Smoke tests: all 12 constructors produce valid Rust | SOUNDNESS | P0 |
| N26.1 | Non-vacuity: end-to-end with nested control flow | SOUNDNESS | P0 |
| N26.1 | Compatibility: stmtToMicroRust on same Stmt as stmtToMicroC produces semantically equivalent MicroC programs | EQUIVALENCE | P1 |
| N26.2 | Zero sorry across entire project | SOUNDNESS | P0 |
| N26.2 | spec_audit: 0 T1, 0 T1.5 | SOUNDNESS | P0 |
| N26.2 | wiring_check: 0 W1 | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **Integration + Audit**: N26.1, N26.2

---

## Previous Versions

### v3.2.0

### Design Decisions (v3.2.0)

1. **Extension-only architecture**: All v3.2 features add `RustBackendProperties.lean` and extend `Common.lean`. No C/MicroC files modified. Zero regression risk.
2. **`_tl_` prefix for Rust sanitization (not `r#`)**: Reuse same prefix pattern as C backend for cross-backend consistency. `r#` is Rust-specific and complicates string analysis (`#` is not alphanumeric). The `_tl_` prefix never appears in any keyword list (proved by `rustKeywords_no_tl_prefix`).
3. **Hybrid induction+decide for balanced braces**: General theorem by structural induction on 12 Stmt constructors (scalable). Concrete examples by `decide` for validation. Same strategy as CBackendProperties.
4. **isValidRustIdent = isValidCIdent**: Rust identifiers follow same ASCII rules (alphanumeric + underscore). Conservative subset — Trust-Lean only generates ASCII identifiers from its own AST. Unicode UAX#31 out of scope.
5. **53 Rust keywords (39 strict + 14 reserved)**: Per Rust 2021 edition, Rust Reference S2.1. Weak keywords (union, macro_rules, raw, safe) excluded — they are valid identifiers in most contexts.
6. **countChar moved to Common.lean**: Shared infrastructure for both C and Rust balanced braces proofs. Previously in CBackendProperties.lean.
7. **Wrapping arithmetic deferred to v3.3**: v3.2 scope = formal properties of code emission. `.wrapping_add()` emission requires semantic changes to stmtToRust, separate phase.
8. **Ownership/borrowing = non-goal**: Trust-Lean emits only owned values (`let mut x: i64`). No `&`, `&mut`, lifetimes. Ownership-trivial subset per RustBelt framework.

### Fase 4: Rust Sanitization Foundation

**Contents**: Extend Common.lean with Rust keyword table, sanitizeIdentifierRust, isValidRustIdent, countChar shared infrastructure.

**Files**:
- `TrustLean/Backend/Common.lean`

#### DAG (v3.2.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N21.1 Rust Keywords + Shared countChar Infrastructure | FUND | — | completed ✓ |
| N21.2 Sanitization Theorems (not_keyword, nonempty, valid, idempotent) | CRIT | N21.1 | completed ✓ |

#### Formal Properties (v3.2.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N21.1 | rustKeywords contains all 53 strict+reserved Rust keywords | INVARIANT | P0 |
| N21.1 | sanitizeIdentifierRust is total (no partial, no sorry) | INVARIANT | P0 |
| N21.1 | isValidRustIdent accepts only ASCII alphanumeric + underscore | INVARIANT | P0 |
| N21.1 | countChar_empty and countChar_append shared in Common.lean | INVARIANT | P1 |
| N21.2 | sanitizeIdentifierRust output never in rustKeywords | SOUNDNESS | P0 |
| N21.2 | sanitizeIdentifierRust output is nonempty | INVARIANT | P0 |
| N21.2 | sanitizeIdentifierRust output passes isValidRustIdent | SOUNDNESS | P0 |
| N21.2 | sanitizeIdentifierRust is idempotent (relies on rustKeywords_no_tl_prefix) | EQUIVALENCE | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **B21: Keywords + countChar Infrastructure**: N21.1 — closed 2026-03-27
- [x] **B22: Sanitization Theorems**: N21.2 — closed 2026-03-27

### RustBackendProperties

**Contents**: Formal properties for Rust code emission: expression correctness, balanced braces (hybrid induction+decide), structural properties, Rust-specific idioms.

**Files**:
- `TrustLean/Backend/RustBackendProperties.lean`

#### DAG (v3.2.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N22.1 Expression Emission Properties (determinism, litInt, litBool) | PAR | N21.2 | completed ✓ |
| N22.2 Balanced Braces (stmtBracePairs + general theorem + examples) | CRIT | N21.1 | completed ✓ |
| N22.3 Structural Properties (for desugaring, header, control flow braces) | PAR | N21.1 | completed ✓ |
| N22.4 Rust-Specific Properties (cast postfix, no parens, let mut, usize) | PAR | N21.2 | completed ✓ |

#### Formal Properties (v3.2.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N22.1 | exprToRust is deterministic (rfl) | EQUIVALENCE | P0 |
| N22.1 | stmtToRust is deterministic (rfl) | EQUIVALENCE | P0 |
| N22.1 | exprToRust litInt nonneg = toString n | SOUNDNESS | P0 |
| N22.1 | exprToRust litInt neg = parenthesized toString n | SOUNDNESS | P0 |
| N22.1 | exprToRust litBool true = true (not 1) | SOUNDNESS | P0 |
| N22.1 | exprToRust litBool false = false (not 0) | SOUNDNESS | P0 |
| N22.2 | stmtBracePairsRust per-constructor (5 simp lemmas) | INVARIANT | P0 |
| N22.2 | 8 concrete balanced braces examples (by decide) | SOUNDNESS | P0 |
| N22.2 | General balanced braces theorem by structural induction on 12 Stmt constructors | SOUNDNESS | P0 |
| N22.2 | stmtToRust_ite_has_open_brace: countChar >= 2 | INVARIANT | P0 |
| N22.2 | stmtToRust_while_has_open_brace: countChar >= 1 | INVARIANT | P0 |
| N22.3 | stmtToRust_for_eq_desugar: for = init + while | EQUIVALENCE | P0 |
| N22.3 | generateRustHeader_no_helper: no power helper when disabled | SOUNDNESS | P0 |
| N22.3 | countChar infrastructure (3 shared lemmas) | INVARIANT | P1 |
| N22.4 | Rust cast uses postfix as syntax | SOUNDNESS | P0 |
| N22.4 | stmtToRust if/while without parentheses around condition | SOUNDNESS | P0 |
| N22.4 | exprToRust litBool outputs keyword (true/false member check) | SOUNDNESS | P0 |
| N22.4 | stmtToRust array access includes usize cast | SOUNDNESS | P1 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **B23: Expression + Structural + Rust-Specific**: N22.1, N22.3, N22.4 — closed 2026-03-27
- [x] **B24: Balanced Braces**: N22.2 — closed 2026-03-27

### Integration + Audit

**Contents**: Integration tests, non-vacuity witnesses, zero sorry audit, spec_audit, wiring_check, v3.2.0 tag.

**Files**:
- `TrustLean/Tests/RustBackendIntegration.lean`

#### DAG (v3.2.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N23.1 Integration Tests + Non-Vacuity Witnesses | HOJA | N22.1, N22.2, N22.3, N22.4 | completed ✓ |
| N23.2 Zero Sorry Audit + spec_audit + v3.2.0 Tag | HOJA | N23.1 | completed ✓ |

#### Formal Properties (v3.2.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N23.1 | Smoke tests: all 12 Stmt constructors produce valid Rust | SOUNDNESS | P0 |
| N23.1 | Non-vacuity: end-to-end with nested control flow | SOUNDNESS | P0 |
| N23.2 | Zero sorry across entire project | SOUNDNESS | P0 |
| N23.2 | spec_audit: 0 T1, 0 T1.5 | SOUNDNESS | P0 |
| N23.2 | wiring_check: 0 W1 | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **B25: Integration + Audit**: N23.1, N23.2 — closed 2026-03-27


### v2.0.0

### Design Decisions (v2.0.0)

1. **MicroC AST = C-level identifiers (String)**: MicroC uses `String` for variable names (C identifiers). Translation via `varNameToC`. Flat namespace — no shadowing, no nested scopes beyond control flow bodies sharing parent env. De Bruijn / locally-nameless deferred to v3.0 if scoping added.
2. **No `for_` in MicroC AST**: Desugared to `seq init (while cond (seq body step))` during `stmtToMicroC`. Simplifies evaluator + proofs (only need to handle `while`).
3. **Functional environment**: `MicroCEnv := String → Value`. Same model as existing `LowLevelEnv` but String-keyed.
4. **Fuel = depth bound (max composition)**: Same model as `evalStmt`. Composición: `max(s1,s2)` for seq/ite, `n+1 + n*(body+1)` for while.
5. **No short-circuit `&&`/`||`**: Both operands evaluated. Semantically equivalent for pure expressions (no side effects in MicroC expr sublanguage). Document as v2.0.0 simplification; address in v3.0 if side-effecting expressions added.
6. **Int = Lean `Int` (unbounded)**: No int64_t wrapping semantics. Overflow deferred to v3.0.
7. **Full parenthesization (canonical form)**: `microCToString` always parenthesizes binary exprs (like existing `exprToC`). Eliminates precedence ambiguity. Makes grammar LL(1) and roundtrip proof straightforward.
8. **`Lean.Data.Parsec` built-in**: Zero external dependencies. `ws` after every token for whitespace tolerance. Non-goals: comments, `#include`, preprocessor directives, liberal parsing.
9. **No pointer arithmetic**: Arrays use abstract indices (same as Trust-Lean Core IR). No heap, no malloc/free.
10. **Compatibility theorem**: `microCToString(stmtToMicroC stmt) = stmtToC level stmt` — MicroC pipeline produces identical C code to existing backend. **Riskiest theorem** — de-risk with sketch in B4.

### MicroC Foundations

**Contents**: Greenfield MicroC AST (11 stmt + 7 expr constructors, String identifiers), fuel-based evaluator (evalMicroC), and fuel monotonicity gate theorem. Mirrors existing Core IR patterns but operates on C-level identifiers.

**Files**:
- `TrustLean/MicroC/AST.lean`
- `TrustLean/MicroC/Eval.lean`
- `TrustLean/MicroC/FuelMono.lean`

#### DAG (v2.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N10.1 MicroC AST + Properties | FUND | — | completed ✓ |
| N10.2 MicroC Evaluator | CRIT | N10.1 | completed ✓ |
| N10.3 evalMicroC_fuel_mono (GATE) | CRIT | N10.2 | completed ✓ |

#### Formal Properties (v2.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N10.1 | MicroCStmt has DecidableEq | INVARIANT | P0 |
| N10.1 | MicroCExpr has DecidableEq | INVARIANT | P0 |
| N10.1 | MicroCStmt.size is always positive | INVARIANT | P1 |
| N10.2 | evalMicroC skip = (env, .normal) | SOUNDNESS | P0 |
| N10.2 | evalMicroC assign updates exactly one variable | SOUNDNESS | P0 |
| N10.2 | evalMicroCExpr is deterministic | EQUIVALENCE | P0 |
| N10.2 | evalMicroC while with false condition terminates normally | SOUNDNESS | P0 |
| N10.3 | evalMicroC fuel monotonicity: more fuel preserves non-outOfFuel results | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **MicroC AST**: N10.1 — closed 2026-03-10
- [x] **MicroC Evaluator**: N10.2 — closed 2026-03-10
- [x] **Fuel Monotonicity Gate**: N10.3 — closed 2026-03-10

### Translation + Simulation

**Contents**: stmtToMicroC translation from Trust-Lean Stmt IR to MicroC AST, microCBridge environment correspondence, and capstone simulation proof: evalStmt env fuel stmt ≡ evalMicroC env' fuel' (stmtToMicroC stmt). Includes compatibility sketch de-risk.

**Files**:
- `TrustLean/MicroC/Translation.lean`
- `TrustLean/MicroC/Bridge.lean`
- `TrustLean/MicroC/Simulation.lean`

#### DAG (v2.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N11.1 stmtToMicroC Translation | PAR | N10.1 | completed ✓ |
| N11.2 microCBridge + Correspondence | FUND | N10.1 | completed ✓ |
| N11.3 Simulation Per-Case Lemmas | CRIT | N10.3, N11.1, N11.2 | completed ✓ |
| N11.4 stmtToMicroC_correct (GATE) | CRIT | N11.3 | completed ✓ |

#### Formal Properties (v2.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N11.1 | stmtToMicroC is total on well-formed Stmt | INVARIANT | P0 |
| N11.1 | stmtToMicroC preserves structure (seq->seq, ite->ite) | PRESERVATION | P1 |
| N11.2 | varNameToC is injective (bridge well-defined) | INVARIANT | P0 |
| N11.2 | microCBridge preserved through environment updates | PRESERVATION | P0 |
| N11.3 | While loop simulation covers all 6 outcome paths | SOUNDNESS | P0 |
| N11.4 | stmtToMicroC_correct: evalStmt = evalMicroC . stmtToMicroC | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **Translation + Bridge**: N11.1, N11.2
- [x] **Simulation Lemmas**: N11.3 — closed 2026-03-10
- [x] **Simulation Capstone**: N11.4 — closed 2026-03-10

### Pretty-Printer + Parser + Roundtrip

**Contents**: microCToString pretty-printer (fully parenthesized, canonical form), parseMicroC parser (Lean.Data.Parsec, ws-tolerant), and capstone roundtrip theorem: parseMicroC(microCToString s) = some s. Comments and liberal parsing are explicit non-goals.

**Files**:
- `TrustLean/MicroC/PrettyPrint.lean`
- `TrustLean/MicroC/Parser.lean`
- `TrustLean/MicroC/Roundtrip.lean`

#### DAG (v2.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N12.1 microCToString Pretty-Printer | PAR | N10.1 | completed ✓ |
| N12.2 parseMicroC Parser | PAR | N10.1 | completed ✓ |
| N12.3 Expression Roundtrip + Structural Props | CRIT | N12.1, N12.2 | completed ✓ |
| N12.4 parseMicroC_roundtrip (GATE) | CRIT | N12.3 | completed ✓ |

#### Formal Properties (v2.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N12.1 | microCToString produces balanced braces | INVARIANT | P0 |
| N12.1 | microCToString produces balanced parentheses | INVARIANT | P0 |
| N12.1 | microCToString on non-skip produces non-empty string | INVARIANT | P1 |
| N12.2 | parseMicroC terminates on all inputs | INVARIANT | P0 |
| N12.3 | parseMicroCExpr(microCExprToString e) = some e | EQUIVALENCE | P0 |
| N12.4 | parseMicroC(microCToString s) = some s (roundtrip) | EQUIVALENCE | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Pretty-Printer + Parser**: N12.1, N12.2 — closed 2026-03-10
- [x] **Expression Roundtrip**: N12.3 — closed 2026-03-11
- [x] **Statement Roundtrip Capstone**: N12.4 — closed 2026-03-11

### Integration + Audit

**Contents**: End-to-end pipeline wiring (microCToString ∘ stmtToMicroC = stmtToC compatibility theorem), non-vacuity joint witnesses, oracle-style #eval tests, and zero-sorry mechanical audit across all v2.0.0 modules.

**Files**:
- `TrustLean/MicroC.lean` (root import)
- `TrustLean/MicroC/Integration.lean` (compatibility + non-vacuity + pipeline tests)

#### DAG (v2.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N13.1 End-to-End Pipeline + Compatibility | HOJA | N11.4, N12.4, N12.1, N11.1 | completed ✓ |
| N13.2 Non-Vacuity + Oracle Tests | HOJA | N13.1 | completed ✓ |
| N13.3 Zero Sorry Audit | HOJA | N13.2 | completed ✓ |

#### Formal Properties (v2.0.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N13.1 | microCToString . stmtToMicroC = stmtToC (compatibility) | EQUIVALENCE | P0 |
| N13.2 | Non-vacuity: all gate theorem hypotheses are jointly satisfiable | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Integration + Audit**: N13.1, N13.2, N13.3 — closed 2026-03-11


### v1.2.0

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
| **v3.1.0** | Mar 2026 | (planned) UInt32/UInt64 unsigned eval, bitwise ops, type casting, Plonky3 field bridges |
| **v3.0.0** | Mar 2026 | Int64 overflow, call semantics, full inductive roundtrip |
| **v2.0.0** | Mar 2026 | MicroC verified semantics: 10 modules, 139 decls, 0 sorry. Simulation proof, fuel monotonicity, roundtrip parser, operator compatibility, 10 pipeline oracle tests |
| **v1.2.0** | Feb 2026 | CBackend industrial: sanitization, aggressive parens, mandatory braces |
| **v1.1.0** | Feb 2026 | ExpandedSigma → Stmt bridge (amo-lean integration) |
| **v1.0.0** | Feb 2026 | Core IR (12 constructors) + 3 frontends + 2 backends + pipeline |



---

## Lessons (current)

Project-specific lessons learned during current version.
Generalized lessons should be migrated to `~/Documents/claudio/lecciones/lean4/`.
