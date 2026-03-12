# Insights: Trust-Lean v3.0 — Int64 Overflow + Full Roundtrip + Call Semantics

**Fecha**: 2026-03-09
**Dominio**: lean4
**Estado del objeto**: upgrade (v2.0.0 → v3.0.0)

## 1. Analisis del Objeto de Estudio

### Resumen

Trust-Lean v2.0.0 es un framework de generacion de codigo verificado con 10 modulos MicroC, 139 declaraciones, 154 teoremas project-wide, 0 sorry, y 101 build jobs. La v3.0 extiende MicroC con tres features ortogonales:

1. **Int64 overflow semantics**: Reemplazar `Int` (unbounded) con aritmetica two's complement wrapping (mod 2^64)
2. **Full inductive roundtrip proof**: Cerrar la prueba inductiva `∀ s, WFStmt s → parseMicroC(microCToString s) = some s` para todos los constructores
3. **Call semantics**: Reemplazar el stub `evalMicroC(.call => none)` con invocacion real de funciones

### Keywords

Int64, two's complement, modular arithmetic, overflow wrapping, roundtrip proof, parser correctness, printer correctness, invertible syntax, mutual induction, WFExpr, WFStmt, call semantics, function environment, fuel-based evaluation, parameter passing, CompCert Clight, CH2O, Fiat Crypto

### Estado

Upgrade — extiende v2.0.0 con 3 features ortogonales. Base solida (0 sorry, spec audit clean).

### Gaps

- Tipo Int64 no existe aun en el proyecto (usar `UInt64` de Lean 4 o tipo custom `Int64 := Fin (2^64)`)
- Pruebas roundtrip incompletas: solo skip, break, continue, return_none, operators, booleans. Faltan: assign, store, load, call, seq, ite, while, binOp, unaryOp, litInt, varRef, arrayAccess
- Call semantics totalmente stub (`.call => none`)
- Mutual induction entre WFExpr y WFStmt no explorada formalmente

### Dependencias

- Feature 1 (Int64) afecta: AST.lean, Eval.lean, Simulation.lean, FuelMono.lean
- Feature 2 (Roundtrip) afecta: Roundtrip.lean, PrettyPrint.lean, Parser.lean
- Feature 3 (Call) afecta: AST.lean, Eval.lean, FuelMono.lean, Simulation.lean
- Features 1 y 3 comparten archivos criticos (Eval, Simulation, FuelMono) — planificar orden cuidadosamente

### Estimacion

- 1,400-1,850 LOC nuevas/modificadas
- 38-54 teoremas nuevos
- 3,500-4,000 LOC total del proyecto post-v3.0

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Titulo | Categoria | Relevancia |
|----|--------|-----------|------------|
| L-612 | natToChars transparent for Lean reducer | Tecnica reutilizable | CRITICA — roundtrip natToChars composition |
| L-305 | Nested induction with hypothesis threading | Tecnica reutilizable | CRITICA — mutual induction WFExpr/WFStmt |
| L-580 | AST desugaring preserves semantics proof | Tecnica reutilizable | Feature 3 (call desugaring) |
| L-578 | Desugaring architectural patterns | Tecnica reutilizable | Feature 3 (call as desugar step) |
| L-604 | fuel+1 safe for evaluation | Tecnica reutilizable | Features 1+3 (fuel monotonicity) |
| L-330 | loopGo_succ pattern for fuel proofs | Tecnica reutilizable | Feature 3 (call fuel threading) |
| L-607 | Parser combinator compositional proofs | Tecnica reutilizable | Feature 2 (roundtrip) |
| L-576 | Bridge predicate extension patterns | Tecnica reutilizable | Feature 3 (bridge + call env) |
| L-382 | Fin arithmetic without Mathlib | Tecnica reutilizable | Feature 1 (Int64 como Fin) |
| L-291 | beq_iff_eq for BEq/Prop conversion | Tecnica reutilizable | Feature 2 (parser equality) |
| L-338 | native_decide vs explicit proofs tradeoff | Tecnica reutilizable | Feature 2 (roundtrip proofs) |
| L-288 | omega limitations with multiplication | Tecnica reutilizable | Feature 1 (overflow bounds) |
| L-292 | Type class resolution order | Aplicable | Feature 1 (BEq/DecidableEq Int64) |
| L-198 | Nonlinear arithmetic without ring | Aplicable | Feature 1 (modular arithmetic) |
| L-268 | Function environment patterns | Aplicable | Feature 3 (function lookup) |

### Anti-patrones a evitar

1. **No probar string equality end-to-end** (B10 lesson): Probar operator-level compatibility, no `print_A(translate(x)) = print_B(x)` completo
2. **No usar identity passes** en pipeline: Cada operacion formal debe corresponder a una operacion operacional real
3. **No diferir nodos fundacionales**: Int64 type + wrapping arithmetic son fundacionales — de-risk primero
4. **No usar rfl directo con funciones**: `MicroCEnv = String → Value` no tiene DecidableEq — usar `by unfold ...; rfl`
5. **No intentar mutual `structural` recursion**: Lean 4 v4.16.0 mutual structural no siempre termina — usar `decreasing_by` o well-founded

### Tecnicas criticas (Top 5)

1. **L-612**: `@[reducible]` o `@[inline]` en `natToChars` para que `rfl`/`native_decide` reduzcan en roundtrip proofs
2. **L-305**: Para mutual induction WFExpr/WFStmt, usar `induction` con `generalizing` sobre las sub-expresiones, threading hypotheses manually
3. **L-604**: `fuel+1` pattern ensures non-zero fuel in recursive calls — essential for FuelMono extension
4. **L-330**: `loopGo_succ` pattern: unfold one step of fuel-based loop, apply IH to remaining fuel
5. **L-580+L-578**: Call can be modeled as desugaring to seq of assignments + body + return extraction

## 3. Bibliografia Existente Relevante

### Documentos clave

| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| CompCert Clight semantics | verificacion/ | Int64 overflow + call semantics — canonical reference |
| CH2O: C Standard Formalized in Coq (Krebbers 2015) | verificacion/ | **NEW** — most complete C integer overflow formalization |
| Fiat Crypto (Erbsen et al. 2019) | verificacion/ | **NEW** — machine word arithmetic, verified extraction |
| Mechanized Semantics IMP (Leroy 2019) | verificacion/ | **NEW** — fuel-based evaluation, canonical pedagogical reference |
| Invertible Syntax Descriptions (Rendel-Ostermann 2010) | verificacion/ | **NEW** — roundtrip by construction (parser+printer from single description) |
| Bidirectional Grammars (Morrisett et al. 2017) | verificacion/ | **NEW** — machine-checked roundtrip proofs in Coq |
| Software Foundations (Pierce et al.) | fundamentos/ | IMP call semantics, small-step vs big-step |
| Certified Programming with Dependent Types (Chlipala) | fundamentos/ | Mutual induction, fuel-based interpreters |
| CertiCoq papers | verificacion/ | Closure-converted calls, bounded evaluation |
| Verified C Compiler (Leroy) | verificacion/ | Integers.v integer representation |

### Grafo de conceptos relacionados

- `CompCert.Integers` → `Int64 type` → `wrapping arithmetic` → `two's complement`
- `fuel-based evaluation` → `monotonicity` → `call fuel threading`
- `invertible syntax` → `roundtrip proof` → `mutual induction` → `WFExpr/WFStmt`
- `function environment` → `call semantics` → `parameter passing` → `return handling`
- `MicroC AST` → `printer` → `parser` → `roundtrip` (existing chain to extend)

### Pathways

1. **Clight → Int64**: CompCert's `Integers.v` defines `Int.repr`, `Int.signed`, `Int.unsigned`. CH2O extends with strict aliasing. For Trust-Lean v3.0: simpler model (just `Fin (2^64)` with wrapping ops).
2. **ITrees → Call semantics**: Interaction trees model callstates, but overkill for non-recursive calls. Simpler: function lookup table + fuel threading.
3. **Invertible syntax → Roundtrip**: Rendel-Ostermann pattern eliminates roundtrip proofs by construction, but requires redesigning printer/parser together. For v3.0: stick with separate proofs by induction (less refactoring).
4. **Fiat Crypto → Machine words**: Verified arithmetic on bounded integers. Relevant for overflow proof obligations.

### Gaps bibliograficos (ahora cubiertos)

- ~~C integer overflow formalization~~ → CH2O (Krebbers) downloaded
- ~~Roundtrip proof techniques~~ → Rendel-Ostermann + Morrisett downloaded
- ~~Machine word verification~~ → Fiat Crypto downloaded
- ~~Fuel-based semantics reference~~ → Leroy IMP downloaded
- Remaining gap: Lean 4 `UInt64` internal implementation (covered by Init.Data.UInt.Basic in stdlib)

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Proyecto fuente | Resultado |
|------------|----------------|-----------|
| Bridge predicate pattern (operational ↔ algebraic) | AMO-Lean (FRI) | 189 theorems, 7 bridges |
| Fuel-based evaluation with monotonicity | Trust-Lean v2.0 | evalMicroC_fuel_mono proven |
| Desugaring for complex constructs (for_ → while+seq) | Trust-Lean v2.0 | for_desugar_compat by rfl |
| Oracle #eval tests alongside formal proofs | Trust-Lean v2.0 | 49 roundtrip oracle tests |
| Operator-level compatibility (not full string eq) | Trust-Lean v2.0 B10 | binOp_compat, unaryOp_compat by rfl |
| WellFormed predicates for parser preconditions | Trust-Lean v2.0 | WFExpr/WFStmt defined |
| Incremental module structure (AST → Eval → FuelMono → Sim) | Trust-Lean v2.0 | Clean DAG, no cycles |
| FunctionInterface structure pattern | VeriHE pipeline | Separates interface from implementation |
| Non-recursive precondition (runtime invariant) | Trust-Lean v2.0 (VarNameInjective) | Documented as precondition, not theorem |
| Spec audit at block close | Trust-Lean v2.0 | 0 T1/T1.5 at completion |

### Decisiones arquitecturales clave

1. **Int64 representation**: Use `Int64 := { val : Int // -2^63 ≤ val ∧ val < 2^63 }` (signed, subtype of Int) rather than Lean's `UInt64` (unsigned). Reason: C `int64_t` is signed, and we need signed comparison operators. Alternative: `UInt64` + reinterpret cast — but complicates proofs.

   **UPDATE after research**: Consider using `Int % (2^64)` with `toSigned` function for display. CompCert uses `Int.repr : Z → int` with modular reduction. CH2O uses layered approach. Simplest for Trust-Lean: keep `Int` internally, add `wrapInt64 : Int → Int := fun n => n % (2^64) - if n % (2^64) ≥ 2^63 then 2^64 else 0`. This avoids changing the type but adds wrapping at operation boundaries.

2. **Call semantics scope**: Non-recursive calls only. Function environment: `Map String MicroCFuncDef` where `MicroCFuncDef := { params : List String, body : MicroCStmt }`. Parameter passing: by value (assign params → eval body → extract return). No closures, no recursion.

3. **Fuel for calls**: Calls consume 1 fuel unit. Inner body evaluation uses remaining fuel. `evalMicroC_fuel_mono` extends naturally. Pattern: `fuel' ≥ fuel → result fuel = some r → result fuel' = some r`.

4. **Roundtrip proof strategy**: Structural induction on `WFStmt`/`WFExpr` with mutual induction. Key challenge: `natToChars` composition in `litInt` case. Use L-612 pattern (make helper transparent). Oracle tests remain as regression suite.

5. **Feature ordering**: (1) Int64 first (foundational type change), (2) Call semantics second (extends Eval), (3) Roundtrip last (needs updated printer/parser for calls, can leverage all other changes).

### Benchmarks de referencia

| Proyecto | Metrica | Valor |
|----------|---------|-------|
| Trust-Lean v2.0.0 | Theorems | 154 (0 sorry) |
| Trust-Lean v2.0.0 | Build jobs | 101 |
| Trust-Lean v2.0.0 | LOC | ~2,200 |
| VeriHE | Theorems for type change propagation | ~20 theorems per type refactor |
| OptiSat | Pipeline soundness chain | 190 theorems |
| VerifiedExtraction | Integration theorems | 203 (0 sorry) |

### Errores evitados

1. **No usar `native_decide` para function-type equality** (B10 lesson) — `String → Value` has no `DecidableEq`
2. **No intentar full string equality across generators** (B10 lesson) — operator-level compat is the right target
3. **No dejar sanitizeIdentifier como universal theorem** (B10 lesson) — it's a runtime precondition
4. **No ignorar non-vacuity** — every gate theorem needs concrete witness

## 5. Nueva Bibliografia Encontrada

### Papers descargados

| Titulo | URL | Carpeta | Relevancia |
|--------|-----|---------|------------|
| Invertible Syntax Descriptions (Rendel-Ostermann 2010) | Haskell Symposium | verificacion/ | Roundtrip by construction pattern |
| Bidirectional Grammars for Machine Code (Morrisett et al. 2017) | JAR | verificacion/ | Machine-checked roundtrip in Coq |
| CH2O: C Standard Formalized in Coq (Krebbers 2015) | PhD thesis | verificacion/ | Most complete C integer formalization |
| Fiat Crypto (Erbsen et al. 2019) | IEEE S&P | verificacion/ | Machine word arithmetic verification |
| Mechanized Semantics IMP (Leroy 2019) | College de France | verificacion/ | Fuel-based evaluation canonical ref |

### Papers ya existentes

- CompCert Clight papers (various Leroy publications)
- Software Foundations (Pierce et al.)
- Certified Programming with Dependent Types (Chlipala)

## 6. Insights de Nueva Bibliografia

### CH2O (Krebbers 2015)

- **Key insight**: C integer semantics require 3 layers: (1) mathematical integers, (2) implementation-defined integers (size, signedness), (3) undefined behavior on overflow. Trust-Lean v3.0 can simplify to just layers 1-2 since we define wrapping (not UB).
- **Pattern**: `int_typed (x : Z) (τ : int_type) := x ∈ int_range τ` where `int_range` depends on signedness and width.
- **Applicability**: Direct — defines signed/unsigned ranges, wrapping, promotion rules.

### Fiat Crypto (Erbsen et al. 2019)

- **Key insight**: Machine word arithmetic is verified by proving equivalence between unbounded Z operations and bounded word operations. Pattern: `word_op w = Z_op (to_Z w) mod 2^n`.
- **Pattern**: `IsEquiv` predicate relating abstract (unbounded) and concrete (bounded) evaluation.
- **Applicability**: Direct model for Trust-Lean's Int64 approach: `evalMicroC_int64 ≡ wrapInt64 ∘ evalMicroC_unbounded` for overflow-free programs.

### Rendel-Ostermann (2010) — Invertible Syntax

- **Key insight**: A single "syntax description" generates both parser and printer, making roundtrip a free theorem. But requires redesigning both parser and printer from scratch.
- **Decision**: NOT applicable for v3.0 — too much refactoring. Keep separate parser/printer with inductive proof. Consider for v4.0.

### Morrisett et al. (2017) — Bidirectional Grammars

- **Key insight**: Coq formalization of roundtrip for x86 instruction encoding/decoding. Uses `inversion` lemmas per constructor. Directly applicable pattern for WFStmt induction.
- **Pattern**: For each constructor C, prove `parse(print(C args)) = Some (C args)` independently, then combine by structural induction.
- **Applicability**: Direct — this is exactly the strategy for v3.0 Feature 2.

### Leroy (2019) — Mechanized Semantics IMP

- **Key insight**: Canonical reference for fuel-based evaluation in Coq. Fuel monotonicity pattern identical to Trust-Lean's. Function calls in IMP use "environment" model (function name → parameter list + body).
- **Pattern**: `cexec fuel env s = Some (t, env') → fuel' ≥ fuel → cexec fuel' env s = Some (t, env')`.
- **Applicability**: Direct for call semantics design and fuel_mono extension.

## 7. Sintesis de Insights

### Hallazgos clave (Top 10)

1. **Int64 como wrapping sobre Int, no tipo nuevo**: Usar `wrapInt64 : Int → Int` que aplica modulo y signed reinterpretation. Evita cambiar el tipo base de `MicroCValue`, minimiza cascade en Simulation.lean. Solo envolver operaciones aritmeticas.

2. **IsEquiv theorem pattern (Fiat Crypto)**: Para programas sin overflow, probar `evalMicroC_wrapped env s = evalMicroC_unbounded env s`. Para programas con overflow, la wrapping semantics es correcta por definicion. Dos teoremas, no uno.

3. **Mutual induction via well-founded recursion**: WFExpr y WFStmt son mutuamente recursivos. En Lean 4 v4.16.0, usar `mutual ... end` con `decreasing_by` o convertir a un solo inductivo con sum type. L-305 pattern applies.

4. **natToChars transparency es critica (L-612)**: El caso `litInt` del roundtrip requiere `parseMicroC(natToChars n) = some n`. Si `natToChars` no es `@[reducible]`, `rfl`/`native_decide` no reducen. Hacer transparente O probar lema auxiliar `natToChars_roundtrip`.

5. **Call semantics sin recursion es suficiente para v3.0**: Non-recursive calls with function lookup table. Design: `MicroCFuncEnv := String → Option MicroCFuncDef`, `MicroCFuncDef := { params : List String, body : MicroCStmt }`. Call = assign params + eval body + extract return.

6. **Fuel monotonicity se extiende naturalmente a calls**: El call case de `evalMicroC_fuel_mono` sigue el mismo patron que while: unfold one step, apply IH to body with `fuel - 1`, compose results.

7. **Roundtrip per-constructor strategy (Morrisett)**: Probar un lema por constructor de WFStmt/WFExpr, luego combinar por induction. Esto modulariza la prueba y permite progreso incremental.

8. **Orden de features: Int64 → Call → Roundtrip**: Int64 es foundational (cambia tipo), Call extiende evaluacion, Roundtrip necesita printer/parser actualizados para calls. Roundtrip al final porque necesita que printer/parser ya manejen los nuevos constructores.

9. **Bridge predicate extension for calls**: `microCBridge` necesita extension para mapear function environments. Pattern de AMO-Lean (L-576): agregar campo al bridge, probar bridge_default para el caso base.

10. **49 oracle tests como regression suite**: Los #eval tests existentes deben seguir pasando tras v3.0. Agregar nuevos para Int64 wrapping y call invocation.

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigacion |
|--------|-------------|---------|------------|
| Int64 cascade en Simulation.lean | Alta | Alto | Usar wrapping solo en Eval, no cambiar tipo base |
| Mutual induction WFExpr/WFStmt no termina | Media | Alto | Fallback: well-founded recursion o size measure |
| natToChars roundtrip composition compleja | Media | Medio | L-612: hacer transparent + lema auxiliar |
| Call fuel interaction con while loops | Baja | Alto | Fuel=max pattern (no sum), test con nested while+call |
| Parser ambiguity con call arguments | Baja | Medio | WFExpr precondition + parenthesization |

### Recomendaciones para planificacion

1. **Fase 1: Fundaciones** — Int64 type + wrapping ops + basic theorems. De-risk: probar `wrapInt64_idempotent` y `wrapInt64_preserves_add` primero.
2. **Fase 2: Call Semantics** — AST extension + Eval + FuelMono + Simulation. De-risk: call fuel_mono case first.
3. **Fase 3: Roundtrip** — Extend printer/parser for calls + close inductive proof for ALL constructors. De-risk: litInt case (natToChars roundtrip) first.
4. **Fase 4: Integration** — Update all oracle tests, spec audit, non-vacuity witnesses for new theorems.
5. **Feature ordering is critical**: Int64 first because it changes value representation. Call second because it extends eval. Roundtrip last because it needs updated printer/parser.

### Recursos prioritarios

1. **CH2O (Krebbers 2015)** — Integer overflow formalization patterns
2. **Morrisett et al. 2017** — Per-constructor roundtrip proof strategy
3. **Leroy 2019 IMP** — Fuel-based call semantics canonical reference
4. **L-612, L-305, L-604** — Critical Lean 4 technique lessons
5. **Trust-Lean v2.0 insights** (`trust_lean_roundtrip_insights.md`) — B7-B10 lessons

## 8. Teoremas Extraidos

Seccion omitida (--depth standard)

## 9. Formalizacion Lean 4

Seccion omitida (--depth standard)

## 10. Libreria Generada

Seccion omitida (--depth standard)
