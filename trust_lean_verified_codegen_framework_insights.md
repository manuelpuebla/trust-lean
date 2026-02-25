# Insights: Trust-Lean — Verified Codegen Framework for Lean 4

**Fecha**: 2026-02-20
**Dominio**: lean4
**Estado del objeto**: upgrade (sucesor de LeanScribe v3.0.0)
**Agentes ejecutados**: 6 (Input Analyzer, Lecciones, Bibliografía, LeanScribe Archive, GitHub Research, Proyectos Previos)

---

## 1. Análisis del Objeto de Estudio

Trust-Lean es un framework de compilación verificada para Lean 4 que generaliza LeanScribe (compilador verificado concreto: `Expr Int + BoolExpr → Stmt → C`) en una plataforma extensible basada en typeclasses. La arquitectura: múltiples DSL frontends → Core IR compartido (Stmt, 12 constructores) → múltiples backends (C, Rust), con pruebas machine-checked de preservación semántica.

**Keywords**: verified compilation, fuel-based semantics, typeclass extensibility, DSL framework, Core IR, bridge lemmas, CodeGenerable, CodeGenSound, BackendEmitter, Clight, CertiCoq, fiat-crypto, CompCert, SSA, outcome propagation, equation lemmas, fuel monotonicity, denotational semantics, operational semantics

**Estado de LeanScribe** (base heredable):
- 3,095 LOC, 72 teoremas, 42 @[simp] lemmas, 81 tests
- 0 sorry, 0 axiomas custom (solo propext, Quot.sound, Classical.choice advisory)
- Build 1.4s warm, elaboration Correctness.lean 6.1s
- Fases 1-3 COMPLETAS (Expr→C, Stmt IR, BoolExpr, break/store/load, short-circuit)

**Gaps identificados**:
1. Value type heterogéneo (Int|Bool) complica proofs con 4 cases por match
2. Typeclass instance search potencialmente lento en Lean 4
3. Correctness proof para ImpStmt (while + state mutation + Value) es ~2x complejidad LeanScribe
4. Rust backend ownership model (lifetimes, borrows) es alto riesgo
5. ExtHashMap API puede ser insuficiente para proof chains profundas
6. No hay semántica formal del target language (Clight, MIR) para backends verificados

---

## 2. Lecciones Aplicables

### Lecciones críticas (Top 10 para Trust-Lean)

| ID | Título | Impacto | Aplicación |
|---|---|---|---|
| **L-265** | Fuel model: recursion bound, NOT resource | CRÍTICO | `max` (no +) para composición. Error aquí invalida toda semántica |
| **L-135** | Clasificación de nodos DAG | CRÍTICO | Clasificar FUND/CRIT/PARALELO/HOJA. Fundacionales NUNCA defer |
| **L-134** | DAG como herramienta de planificación | CRÍTICO | Construir DAG ANTES de codificar |
| **L-114** | Nunca defer foundational proofs | CRÍTICO | Value injectivity/disjointness ANTES de correctness |
| **L-243** | Generalizar induction hypothesis early | ALTO | En lowerExpr_correct, acumular state requiere generalización |
| **L-99/106** | Evitar inline match en recursión | ALTO | Extraer predicados a @[simp] funciones separadas |
| **L-143** | Verificar monotonía en TODOS constructores | ALTO | Un constructor que viola invalida la propiedad |
| **L-200** | dite vs ite para hypotheses limpias | ALTO | `if h : cond` (Prop) siempre, no `if cond == val` (BEq) |
| **L-118** | Simp sets dedicados por dominio | MEDIO | @[trust_lean_simp] para acelerar pruebas |
| **L-253** | Recursive typeclass instance = circular ref | MEDIO | Definir función standalone ANTES de instancia |

### Anti-patrones a evitar

1. **Inline match en recursión** (L-99/106): Causa "constant already declared" kernel error → Extraer a funciones separadas
2. **Monotonía asumida sin verificar todos constructores** (L-143): Un solo constructor que viola invalida propiedad
3. **Cadenas frágiles de rw para aritmética** (L-160): Usar `omega` en su lugar
4. **Diferir foundational proofs** (L-114/135): Size/shape preservation son PRECONDICIONES
5. **ite con BEq en lugar de dite con Prop** (L-200): Genera hipótesis sucias
6. **Fuel como recurso consumido** (L-265): Fuel = depth bound, composición = max
7. **Recursión dentro de instancia typeclass** (L-253): Definir `def` separado primero
8. **Confiar en LLM QA sobre código verificado** (L-269): Kernel verification > LLM analysis

### Técnicas reutilizables

| Técnica | Patrón | Lección |
|---|---|---|
| DAG topológico | Construir DAG → orden topológico → bottom-up | L-134/135/216 |
| Bridge lemmas | Conectar representaciones internas/externas | L-146/209 |
| Simp sets dedicados | @[domain_simp] + `simp only [domain_simp]` | L-118 |
| dsimp before rw | Reduce projections antes de rewrite | L-150 |
| Generalización temprana | Generalizar hypothesis state en inducción | L-243 |
| Predicados separados | Extraer inline match a funciones con @[simp] | L-99/106 |
| have explícito | Fuerza unificación cuando simp falla | L-267 |
| omega para aritmética | Reemplazar cadenas de `rw` | L-160 |
| beq_iff_eq bridge | Conversión sistemática Bool ↔ Prop | L-209 |

---

## 3. Bibliografía Existente Relevante

### Documentos clave en la biblioteca

| Documento | Relevancia para Trust-Lean |
|---|---|
| **Accelerating Verified-Compiler (Gross et al.)** | Framework Coq para compiladores verificados con rewrite rules. Fiat-Crypto speedups 1000x. NbE, let-lifting, PHOAS |
| **Formally Verified NTT (Trieu 2025)** | Formalización NTT en Rocq con code synthesis a C. Usa Fiat-Crypto + Bedrock2 |
| **Arquitectura Lean 4 Metaprogramming** | Jerarquía monádica completa, Expr representation, De Bruijn indices |
| **AMO-Lean Roadmap hacia zkVM** | FRI compiler verificado → generador de primitivas criptográficas |
| **Act: Tensor Accelerator ISA** | Equality saturation + constraint programming para compiler backends con soundness |
| **HEC: Equivalence Verification** | Framework verificación equivalencia funcional via e-graphs + MLIR |
| **CIRCOM paper** | DSL para circuitos aritméticos → R1CS. Referencia directa para futuros frontends |

### Gaps bibliográficos

1. **Clight Semantics Formalization** — No indexado, necesario para verified C backend
2. **CompCert IL Stack completo** — Falta análisis profundo de RTL→LTL→Linear→ASM
3. **Typeclass-based codegen patterns en Lean 4** — No hay referencia existente
4. **Fuel-based semantics theory** — Solo tenemos implementación, no teoría formal
5. **Fiat-Crypto architecture deep-dive** — Pipeline completo Spec→Gallina→Bedrock2→C

---

## 4. Insights de LeanScribe Archive (Estrategias Ganadoras)

### Del archivo `BoolExpr_insights.md`

- **§7.1 Phantom types → proof explosion**: Decisión de usar sum type (`Value = Int | Bool`) en lugar de type-indexed AST. Constructor injectivity/disjointness viene gratis del kernel
- **IMP pattern**: 2 inductivos separados (Expr + BoolExpr) con evaluadores y proofs separados
- **Value-based lowering**: BoolExpr compila a 0/1 Int values, no a control flow directo

### Del archivo `LeanScribe_findings.md`

- **evalStmt fuel model**: Fuel SOLO decrementa en while/for. Assign/seq/ite/skip NO consumen fuel
- **Fuel monotonicity restricción**: `evalStmt_fuel_mono` es FALSE para `.outOfFuel`. Counterexample: `while(false) skip` con fuel 0 vs 1
- **Bridge lemma pattern**: `assignmentsToStmt_correct` conecta List Assignment → Stmt, permitiendo reusar TODA la infraestructura de Fase 1 en Fase 2
- **BinOp meta-lemma**: Reduce ~75 LOC/operador a ~10 LOC. `rfl` prueba `hdenote` porque `evalBinOp .add` y `Expr.denote .add` ambos reducen a `+` definicionalmente

### Del archivo `LeanScribe_phase2_insights.md`

- **Correctness decomposition**: lowerToStmt → lowerExpr → (assigns, resultExpr) → assignmentsToStmt → evalStmt → evalProgram → transitivity
- **evalStmt_fuel_mono proof technique**: Structural induction on stmt + nested induction on fuel for while case
- **Generic BinOp meta-lemma**: Cada caso BinOp = 2 LOC (vs ~60 antes)

### Del archivo `RUBRICA_FASE_2.5.md`

- **Benchmarks alcanzados**: 0 sorry, 60+ theorems, 42 @[simp], 56 tests, build <5s, elaboration <15s
- **Classical.choice**: Introducido por `by_cases`, advisory — eliminar con pattern match on Bool
- **Gemini QA false positive**: Gemini criticó `max` fuel composition como "unsound" — el kernel ya verificó, la crítica es incorrecta

### Métricas finales LeanScribe v3.0.0

| Métrica | Valor |
|---|---|
| LOC total | 3,095 |
| Teoremas | 72 (30 theorems + 42 @[simp]) |
| Sorry | **0** |
| Axiomas custom | **0** |
| Tests | 81 PASS, 0 FAIL |
| Build (warm) | 1.4s |
| Elaboration | 6.1s |
| Fases completadas | 4 de 4 |

---

## 5. Análisis Comparativo con Proyectos Externos (GitHub Research)

### Fiat-Crypto (MIT CSAIL) — Referencia principal

| Aspecto | Fiat-Crypto | Trust-Lean |
|---|---|---|
| IR | PHOAS (Parametric Higher-Order Abstract Syntax) | Stmt (first-order, Clight-inspired) |
| Pipeline | Spec → PHOAS → BoundsPipeline (passes) → Common IR → Backends | DSL → CodeGenerable.lower → Stmt → BackendEmitter |
| Backends | 5+ (C, Rust, Go, Java, Zig) — trusted pretty-printers | 2 planned (C, Rust) — trusted pretty-printers |
| Proof strategy | Compositional pass verification + Common IR | Typeclass-based CodeGenSound + bridge lemmas |
| Validation | Test suites externas (BoringSSL, Dalek) | LeanScribe como test oracle |

**Lección clave**: Common IR layer unifica backends. Trust-Lean debe asegurar que `Backend/Common.lean` sea suficientemente expresivo.

### CompCert/Clight — Semántica de referencia

- **Outcome propagation rules 23-25**: Trust-Lean adopta este patrón para while con break/continue/return
- **Big-step source, small-step target**: Trust-Lean usa big-step (fuel) en ambos lados — simplifica pero limita reasoning sobre divergencia
- **8 intermediate languages**: CompCert usa muchas más ILs que Trust-Lean. Simplicidad de Trust-Lean es ventaja para proofs

### CertiCoq — Fuel semantics

- **Dual semantics (fuel + trace)**: Fuel para divergencia, trace para conteo de operaciones. Trust-Lean podría añadir traces para análisis de complejidad (stretch goal)
- **ANF como forma canónica**: Para optimizations futuras, considerar ANF intermediate form
- **7-pass pipeline**: Cada pass verificado independientemente, compuesto por transitividad

### Bedrock2 — Verified low-level compilation

- **Omnisemantics pattern**: `(Env → Prop) → Prop` para reasoning non-determinístico
- **End-to-end verified**: Source → RISC-V binary verificado. Trust-Lean podría aspirar a esto para un backend
- **Establish/preserve/use**: Patrón para backend verification

### Jasmin — High-assurance cryptography

- **Translation validation**: OCaml oracle (untrusted) + Coq validator (verified). Patrón útil para optimizations complejas
- **Constant-time verification**: CRÍTICO para futuros crypto DSLs (AMO, vr1cs)
- **Inline assembly**: Para performance de crypto primitives

### Vale — Verified assembly

- **Embed target language en prover**: Clight/MIR embedded en Lean para verified backends (long-term)
- **VC generation verificado**: Hoare logic para assembly

---

## 6. Estrategias de Proyectos Previos

### AMO-Lean (Automatic Mathematical Optimizer)

| Estrategia | Resultado | Aplicación a Trust-Lean |
|---|---|---|
| E-graph saturation con reglas verificadas | 91.67% reduction, 568M elem/s | Future optimization pass en Trust-Lean pipeline |
| CodeGen SIMD (Fase 3 en progreso) | 32.3x speedup Lean→C | Backend optimization patterns |
| 120/120 tests pass | Alta confianza | Mínimo 100 tests para Trust-Lean v1.0 |

### LeanScribe (predecessor directo)

| Estrategia | Resultado | Aplicación |
|---|---|---|
| Fuel-based big-step semantics | evalStmt_fuel_mono proven | Adoptado directamente |
| Bridge lemma pattern | Reusar toda Fase 1 en Fase 2 | Generalizado en CodeGenSound |
| IMP pattern (2 inductivos) | Proofs modulares | Cada frontend = proofs independientes |
| BinOp meta-lemma | 2 LOC/operador vs 60 | Generalizado en CodeGenSound obligation |
| DAG-driven development | 4 fases, 0 sorry | Methodology para Trust-Lean |
| Incremental IR extension | Fase 3 no rewrote existing proofs | Core IR extensible pattern |

### SuperTensor-lean

- Usa Mathlib al mismo commit hash — confirma compatibilidad Lean 4 v4.26.0

---

## 7. Síntesis de Insights

### Hallazgos clave (Top 10)

1. **Trust-Lean está arquitectónicamente validado**: Las decisiones core (fuel semantics, typeclasses, outcomes) coinciden con state-of-the-art (CompCert, CertiCoq, Fiat-Crypto). No hay que cambiar la arquitectura.

2. **LeanScribe provee una base probada extraordinaria**: 72 teoremas, 0 sorry, 3,095 LOC. Los primeros 2 frontends son wrappers directos. El costo de generalización es principalmente en Value (Int→Value) y proof decomposition.

3. **Value type es el riesgo #1**: Cada match ahora tiene 4 cases (Int, Bool). Fiat-Crypto maneja esto con Common IR abstractions; Trust-Lean debe crear @[simp] lemmas para `Value.asInt`, `Value.asBool` agresivamente.

4. **Fuel composition con `max` es correcto y validado**: LeanScribe lo probó, CompCert/CertiCoq lo confirman. Gemini QA dio falso positivo. `max` (no +) es la regla.

5. **Common IR layer (Backend/Common.lean) es crítico**: Fiat-Crypto unifica 5 backends con Common IR. Trust-Lean debe invertir en esta capa para que C y Rust backends compartan máximo código.

6. **Proof decomposition por frontend elimina el monolito**: LeanScribe's 880 LOC monolith fue su mayor deuda. Trust-Lean la resuelve con Correctness/{ArithCorrect, BoolCorrect, ImpCorrect}.lean.

7. **ImpStmt es el de-risk más importante**: Frontend 3 es el primer frontend NUEVO (no wrapper de LeanScribe). While + assignments + Value heterogéneo. GATE sketch con sorry ANTES de implementación completa.

8. **Constant-time verification es essential para crypto DSLs**: Jasmin lo demuestra. Cuando Trust-Lean añada AMO/vr1cs frontends, necesitará property de constant-time.

9. **Translation validation es el path hacia optimizations**: Jasmin pattern (oracle + validator) permite optimizations complejas sin probar el optimizer, solo el resultado.

10. **Test oracle pattern (LeanScribe) da safety net**: Para inputs que LeanScribe maneja, Trust-Lean DEBE dar resultados idénticos. Regression automática.

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigación |
|---|---|---|---|
| Value type proof explosion | ALTA | MEDIO | @[simp] agresivos para asInt/asBool, empezar solo con Int+Bool |
| ImpStmt while proof harder than expected | MEDIA | ALTO | GATE sketch con sorry, reusar LeanScribe while pattern |
| Typeclass inference lenta | MEDIA | BAJO | Explicit instance passing como fallback |
| LeanScribe API break | BAJA | ALTO | Pin @v3.0.0, never depend on private defs |
| Rust backend ownership | ALTA | MEDIO | Start con subset: no borrows, solo `let mut` + stack |
| ExtHashMap insufficient | MEDIA | MEDIO | Fallback a pure function env (proven) |

### Recomendaciones para planificación

1. **Fase 1 (v0.1): Core IR + Semantics** — FUNDACIONAL
   - Value.lean, IR.lean, Env.lean, Eval.lean, FuelMono.lean
   - Priorizar @[simp] lemmas para Value type
   - evalStmt_fuel_mono debe ser el primer teorema probado

2. **Fase 1 (v0.2): Typeclasses + First Frontend** — CRÍTICO
   - CodeGenerable.lean, CodeGenSound.lean
   - ArithExpr frontend (wrapper de LeanScribe) como GATE/de-risk
   - Si ArithExpr CodeGenSound falla → problema sistémico

3. **Fase 2 (v0.3): BoolExpr + ImpStmt** — HARDEST
   - ImpStmt GATE sketch con sorry ANTES de full proof
   - De-risk ImpStmt while con sorry → medir complejidad → decidir
   - BoolExpr frontend (wrapper) debería ser directo

4. **Fase 2 (v0.4-0.5): Backends**
   - C backend primero (herencia directa de LeanScribe)
   - Common.lean antes de Rust (evitar duplicación)
   - Rust: subset mínimo (no borrows)

5. **v1.0: Integration + 0 sorry**
   - Mínimo 100 tests (LeanScribe tiene 81)
   - LeanScribe regression suite completa
   - #print axioms en todos los CodeGenSound instances

### Recursos prioritarios (consultar durante implementación)

| Recurso | Path/Referencia | Uso |
|---|---|---|
| LeanScribe Correctness.lean | `../LeanScribe/LeanScribe/Correctness.lean` | Patrón de prueba para bridge lemmas, fuel_mono |
| LeanScribe BoolExpr_insights.md | `../LeanScribe/archive/BoolExpr_insights.md` | IMP pattern, phantom types, Value design |
| Lecciones L-265 (fuel model) | `query_lessons.py --lesson L-265` | max composition, NOT additive |
| Lecciones L-243 (generalize IH) | `query_lessons.py --lesson L-243` | Induction hypothesis generalization |
| Lecciones L-135 (DAG classification) | `query_lessons.py --lesson L-135` | FUND/CRIT/PARALELO/HOJA |
| Fiat-Crypto pipeline | `github.com/mit-plv/fiat-crypto` | Common IR, multi-backend architecture |
| CompCert Clight semantics | CompCert documentation | Outcome propagation rules 23-25 |
| CertiCoq fuel pattern | CertiCoq documentation | Dual semantics (fuel + trace) |
