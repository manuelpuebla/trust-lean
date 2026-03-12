# Insights: Camino 3 — MicroC Verified Semantics + Roundtrip Parser for Trust-Lean

**Fecha**: 2026-03-10
**Dominio**: lean4 / verificación formal / compiladores
**Estado del objeto**: Upgrade (extensión de Trust-Lean v1.2.0)
**Profundidad**: deep (bibliografía online + extracción de teoremas)

---

## 1. Análisis del Objeto de Estudio

### Resumen

**Camino 3** extiende Trust-Lean v1.2.0 con un subsistema de semántica formal para C verificado: MicroC, un subconjunto de C99 con ~24 nodos AST, semántica fuel-based (`evalMicroC`), traducción verificada (`stmtToMicroC`), y un **teorema de roundtrip** `parseMicroC(microCToString s) = some s` que cierra la cadena formal desde matemática pura hasta código C.

### Estado actual de Trust-Lean v1.2.0

| Métrica | Valor |
|---------|-------|
| LOC (core) | 5,284 |
| Archivos .lean | 40 |
| Teoremas | 92 |
| @[simp] lemmas | 217 |
| Sorry | 0 |
| Axiomas custom | 0 |
| Fases completadas | 9 (v1.0.0–v1.2.0) |
| Toolchain | v4.26.0 + Mathlib |

### Arquitectura existente

```
Layer 1: Core IR + Semántica (Eval.lean, FuelMono.lean)
         └─ Stmt: 12 constructores, Value: int|bool, Outcome: 5 variantes
         └─ evalStmt_fuel_mono: gate theorem (250 LOC, 0 sorry)

Layer 2: Frontends (ArithExpr, BoolExpr, ImpStmt)
         └─ CodeGenerable + CodeGenSound typeclasses

Layer 3: Backends (CBackend, RustBackend)
         └─ BackendEmitter typeclass, 34 propiedades formales
         └─ stmtToC: balanced braces, parenthesized exprs, sanitized identifiers

Layer 4: Bridge (amo-lean → Stmt)
         └─ expandedSigmaToStmt_correct: simulación completa (490 LOC, 0 sorry)
```

### Keywords técnicos

Fuel-based semantics, MicroC AST, evalMicroC, stmtToMicroC, roundtrip parser, Clight/CompCert, pretty-printer, parser combinators, simulation diagram, operator precedence, control flow semantics, memory model, bridge predicates, injectivity, alpha-equivalence, decidable equality, fuel composition, translation validation

### Gaps identificados

1. **No existe MicroC AST** — greenfield subsystem
2. **No existe C memory model formal** — solo load/store abstractos
3. **No existe roundtrip parser** — Trust-Lean solo emite, nunca parsea
4. **No existe semántica de operadores C** — precedencia/asociatividad no modelada
5. **Scoping de variables** — Trust-Lean asume variables pre-declaradas
6. **Overflow de int64_t** — semántica de wrapping no formalizada
7. **Short-circuit evaluation** — `&&`/`||` no modelados formalmente
8. **Parser combinator framework** — no seleccionado aún para Lean 4

---

## 2. Lecciones Aplicables

### Lecciones reutilizables (26 encontradas)

#### Cluster: Fuel-Based Semantics (CRÍTICO — diseñar PRIMERO)

| ID | Título | Impacto |
|----|--------|---------|
| **L-305** | Nested induction (structural + fuel) for while-loop correctness | Outer structural en Stmt, inner fuel en while. Template directo para evalMicroC |
| **L-265** | Fuel model: depth bound, NOT consumed resource | Composición via `max`, NO `+`. Violarlo invalida monotonicity |
| **L-325** | Fuel bound composition via max for sequential semantics | `seq: max(s1,s2)`, `while: n+1 + n*(body+1)` |
| **L-288** | Fuel independence forms base cases for fuel monotonicity | Non-loops (skip, assign, store, load) = base cases para FuelMono |
| **L-292** | Generalize fuel monotonicity to ALL non-outOfFuel outcomes | Probar una vez para todo `oc ≠ outOfFuel`, especializar después |
| **L-289** | While loop: 6 outcome patterns for complete coverage | false-exit, normal re-enter, continue re-enter, break exit, return propagate, outOfFuel propagate |
| **L-268** | One-step unrolling theorems for while loops | Probar single unroll, no N-iteration |
| **L-470** | Fuel-based mutual recursion: fuel as LAST argument | Para evalMicroCExpr + evalMicroCStmt en mutual block |

#### Cluster: Roundtrip Parser (CRÍTICO — diseñar forward primero)

| ID | Título | Impacto |
|----|--------|---------|
| **L-368** | Roundtrip as bridge: cuando directo es difícil, buscar intermedio C | `print ∘ parse` bridges parser-evaluator composition |
| **L-358** | Backward roundtrip easier but forward is what rubric demands | Forward (hypothesis propagation) es harder. Planear esfuerzo para forward |
| **L-359** | Injectivity of partial conversions requires forward roundtrip | Probar forward roundtrip; derivar inyectividad por inversa |

#### Cluster: Memory Model + Bridge Predicates

| ID | Título | Impacto |
|----|--------|---------|
| **L-290** | Functional environment model yields clean equational proofs | `VarName→Value` con DecidableEq → simp resuelve todo |
| **L-315** | Three-part bridge: scalarBridge + loopBridge + memBridge | Preservation modular por bridge component |
| **L-306** | Bridge predicate + injectivity for environment correspondence | `∀ v, llEnv(user(vn v)) = int(env v)`. Necesita inyectividad de vn |
| **L-121** | Alineación semántica explícita | Bridge lemmas entre semánticas fuente/destino. Obligatorio para lowering |

#### Cluster: Proof Patterns + Architecture

| ID | Título | Impacto |
|----|--------|---------|
| **L-337** | Correctness proofs: compositional via helper lemmas | Factor cada constructor en lemma separado; componer inductivamente |
| **L-318** | Structural homomorphism in expression translation | Inducción estructural + bridge predicates. Homomorphisms son rfl |
| **L-415** | Proof-Carrying Data Structures for Composable Correctness | Bundle transformation + proof en struct. Composición trivial via transitivity |
| **L-512** | Three-Tier Bridge: Shell(partial/IO) + Core(total/pure) + Bridge(theorem) | Crear alternativas verificadas, no refactorizar producción |
| **L-572** | Three-Tier Bridge pattern: translation validation closes Tier1-Tier2 gap | BEq en outputs → identity → satisfaction transfer |
| **L-453** | CompCert multi-pass for partial defs | Abstraer partial defs via hipótesis explícitas. Callers discharge |
| **L-300** | wellTyped predicate restricts CodeGenSound to typed domains | Evita casos imposibles; bridge usa witness para extraer valores |
| **L-308** | BackendEmitter architecture for code generation | Typeclass: emitStmt, emitFunction, emitHeader. 12 constructores obligatorios |
| **L-346** | for_ desugaring: semantically consistent with IR evaluator | Documentar desugaring explícitamente per Clight approach |

### Anti-patrones a evitar

1. **Fuel composition como `+`** — viola monotonicity; usar `max` para seq/ite
2. **Probar backward roundtrip primero** — falsa economía; forward es lo que importa
3. **Incomplete while-loop case analysis** — los 6 outcome paths son obligatorios
4. **Unfold partial defs en proofs** — abstraer con hipótesis explícitas
5. **Identity passes (`:= id`)** — deuda técnica disfrazada de completitud
6. **Diferir propiedades fundacionales** — de-risk con sketch ANTES de auxiliares

---

## 3. Bibliografía Existente Relevante

### Documentos clave en biblioteca local (20+)

| Documento | Carpeta | Relevancia |
|-----------|---------|-----------|
| **CompCert - Formally Verified Optimizing Compiler** (Leroy 2016) | verificacion | Simulación, Clight, arquitectura de compilador verificado |
| **Mechanized Semantics for Clight** (Blazy & Leroy 2009) | verificacion | Referencia definitiva para big-step operational semantics de C |
| **Compositional Optimizations for CertiCoq** (Paraskevopoulou 2021) | verificacion | Fuel-based semantics + step-indexed logical relations |
| **HELIX: Formal Verification of High Perf Program Generation** (Zaliva 2018) | verificacion | DSL-to-imperative translation con formal verification |
| **Verified Translation Functional-Imperative in HELIX** (Zaliva 2020) | verificacion | Multi-stage translation con memory safety properties |
| **Verified Compiler for Functional Tensor Language** (Liu et al. 2024) | verificacion | Verified lowering: functional arrays → imperative C loops |
| **PureCake Verified Compiler** (Kanabar et al. 2023) | verificacion | Multi-pass + Interaction Trees + applicative bisimulation |
| **Interaction Trees** (Xia et al. 2020) | verificacion | Compositional model for compiler correctness; weak bisim |
| **Verifying Peephole Rewriting in SSA IRs** (Bhat et al. 2024) | verificacion | LeanMLIR: intrinsic well-typedness en Lean 4 |
| **HEC: Equivalence Checking via Equality Saturation** (Yin et al. 2025) | verificacion | Translation validation: E-graphs + MLIR frontend |
| **Two-Phase Memory Model** (Beck et al. 2024) | verificacion | Reconciling pointer-integer casts y finite space en LLVM |
| **lean-egg Equality Saturation** (Rossel et al. 2026) | verificacion | Tactic de equality saturation en Lean 4 |

### Gaps bibliográficos (resueltos en Wave 2)

Todos los 9 gaps fueron cubiertos con búsqueda online (ver Sección 5).

---

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras (10)

| Estrategia | Proyecto fuente | Resultado |
|-----------|----------------|-----------|
| **Bridge predicate pattern** | Trust-Lean v1.1.0 | 80-120 LOC/bridge, 0 sorry, reutiliza 90% infraestructura |
| **Fuel monotonicity gate theorem** | Trust-Lean v1.0.0 | 250 LOC, inducción strong fuel + structural Stmt |
| **Statement-oriented compile_correct** | HELIX/Trust-Lean | 6 cases × ~40 LOC/case, no CodeGenSound |
| **Semantic lifting via layers** | SPIRAL/Trust-Lean | Algebraic → operational → computational, bridges independientes |
| **Translation validation (oracle + witness)** | HELIX/Trust-Lean | Bridge proof = oracle, witness ~200 LOC |
| **Gather/Scatter as load/store sequences** | Trust-Lean v1.0.0 | ~60 LOC cada uno, inducción en count |
| **Carrier type abstraction** | HELIX/amo-lean | Field arithmetic en amo-lean, Trust-Lean opera sobre Int |
| **Zero-sorry mandate** | VR1CS/OptiSat/Trust-Lean | Staged proofs evitan bloques masivos |
| **Typeclass extensibility** | Trust-Lean v1.1.0 | Multiple backends via instances, sin duplicación |
| **Explicit induction on fuel + stmt** | Trust-Lean FuelMono | Nested induction handles 12 constructores + loop case |

### Benchmarks de referencia

| Métrica | Trust-Lean v1.0 | Trust-Lean v1.1 | Proyección v2.0 (MicroC) |
|---------|:---:|:---:|:---:|
| Total LOC | 2,917 | 5,284 | 7,500–8,500 |
| Teoremas | 179 | 92+ | 140–180 |
| Sorry | 0 | 0 | **0** (obligatorio) |
| Build time (warm) | 4m | 4m | <8m |

### Errores críticos evitados (14)

1. **Phantom types on Value** — 2x proof size; usar sum type `int|bool`
2. **Monotonía asumida sin verificar constructores** — invalidates gate theorem
3. **Fuel composición como +** — semánticamente incorrecto
4. **Recursive typeclass instance** — circular reference
5. **simp[*] en pruebas críticas** — impredecible entre versiones Lean
6. **Diferir fundacionales** — 2-3 week slip; rework correctness proofs
7. **Identity passes** — 0 valor probatorio real
8. **Body fuel consumption off-by-one** — body usa fuel `n+1`, recursión `n`
9. **Bridge predicate not preserved through updates** — proof collapse at assignment
10. **Gather/Scatter index unchecked** — out-of-bounds en código generado
11. **Fuel overflow en nested loops** — product of bounds > Nat range
12. **Field arithmetic creep** — ops de campo SOLO en amo-lean
13. **Missing case en ExpandedSigma** — gap de cobertura silencioso
14. **Confusión `get?` vs `getElem?`** — bracket notation es getElem?, no get?

---

## 5. Nueva Bibliografía Encontrada (Wave 2)

### Papers encontrados: 15/15 (9 gaps + 3 bonus + 3 descubrimientos)

#### Gap 1: Narcissus — Verified Encoder/Decoder Framework
- **Autores**: Delaware, Suriyakarn, Pit-Claudel, Ye, Chlipala
- **Venue**: ICFP 2019
- **URLs**: [arXiv](https://arxiv.org/abs/1803.04870) | [GitHub](https://github.com/mit-plv/fiat/tree/narcissus-icfp2019)
- **Relevancia**: Arquitectura de referencia para roundtrip parse/print. Combinator-based approach + tactic-driven synthesis. Transferible directamente a MicroC.

#### Gap 2: EverParse — Verified Secure Zero-Copy Parsers
- **Autores**: Ramananandro, Delignat-Lavaud, Fournet, Swamy, Chajed, Kobeissi, Protzenko
- **Venue**: USENIX Security 2019
- **URLs**: [Project](https://project-everest.github.io/everparse/) | [GitHub](https://github.com/project-everest/everparse)
- **Relevancia**: Framework industrial en F*. Core: parsing = inverse of serialization. "3D" frontend permite definiciones C-style. Modelo para parser verificado con code generation a C.

#### Gap 3: Danielsson — Correct-by-Construction Pretty-Printing
- **Autor**: Nils Anders Danielsson
- **Venue**: DTP 2013
- **URL**: [Paper](https://www.cse.chalmers.se/~nad/publications/danielsson-correct-pretty.pdf)
- **Relevancia**: **REFERENCIA ARQUITECTURAL PRIMARIA** para roundtrip `parse ∘ print = id`. Formaliza en Agda: given unambiguous grammar, pretty-print + parse = identity. Técnicas de tipos dependientes para precedencia y fixity transferibles a MicroC.

#### Gap 4: Pancake/CakeML — Verified C-Like Language
- **Autores**: Åman Pohjola, Syeda, Tanaka, Winter et al.
- **Venue**: PLOS 2023
- **URLs**: [Paper](https://cakeml.org/plos23.pdf) | [Project](https://cakeml.org/pancake)
- **Relevancia**: **PRECEDENTE MÁS CERCANO a MicroC**. C-like sin type system estático, semántica funcional big-step, compiler verificado sobre CakeML backend. Solo 3 data kinds (words, code pointers, structs). Template directo para `evalMicroC`.

#### Gap 5: Lean 4 Parser Combinators
- **Opciones**:
  - `Lean.Data.Parsec` (built-in): sin dependencias, ideal para verificación
  - `Megaparsec.lean` ([GitHub](https://github.com/lurk-lab/Megaparsec.lean)): mejor error reporting
  - `lean4-parser` ([GitHub](https://github.com/fgdorais/lean4-parser)): standalone
- **Recomendación**: Usar `Lean.Data.Parsec` built-in para verificación; Megaparsec para testing/dev.

#### Gap 6: Alive2 — Translation Validation for LLVM
- **Autores**: Lopes, Lee, Hur, Liu, Regehr
- **Venue**: PLDI 2021 (Distinguished Paper)
- **URLs**: [PDF](https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf) | [GitHub](https://github.com/AliveToolkit/alive2)
- **Relevancia**: Bounded translation validation via SMT. Metodología aplicable a `stmtToMicroC` como alternativa a proof completo. Formalizó UB model de LLVM. Encontró 47 bugs en LLVM.

#### Gap 7: CSmith — Finding Bugs in C Compilers
- **Autores**: Yang, Chen, Eide, Regehr
- **Venue**: PLDI 2011
- **URLs**: [PDF](https://users.cs.utah.edu/~regehr/papers/pldi11-preprint.pdf) | [GitHub](https://github.com/csmith-project/csmith)
- **Relevancia**: Oracle testing: generar MicroC programs aleatorios, compilar por pipeline verificado, comparar resultados. Key insight: generar programas well-formed sin UB.

#### Gap 8: YARPGen — Random Testing for C/C++ Compilers
- **Autores**: Livinskii, Babokin, Regehr
- **Venue**: OOPSLA 2020
- **URLs**: [PDF](https://users.cs.utah.edu/~regehr/yarpgen-oopsla20.pdf) | [GitHub](https://github.com/intel/yarpgen)
- **Relevancia**: Extiende CSmith con "generation policies" para mayor diversidad. MicroC tiene constructos específicos que necesitan generación dirigida. 220+ bugs en GCC/LLVM/ICC.

#### Gap 9: Lean4Lean — Verified Typechecker for Lean
- **Autor**: Mario Carneiro
- **Venue**: arXiv 2024
- **URLs**: [arXiv](https://arxiv.org/abs/2403.14064) | [GitHub](https://github.com/digama0/lean4lean)
- **Relevancia**: Re-implementación verificada del type checker de Lean 4. Patrones para mutual recursion, fuel/gas para terminación, environment management. Template para `evalMicroC`.

#### Gap 10: SPLean — Separation Logic in Lean 4
- **Autores**: VERSE Lab (Ilya Sergey, NUS)
- **URL**: [GitHub](https://github.com/verse-lab/splean)
- **Relevancia**: Framework de separation logic para heap verification. Tactics: `xsimp`, `xstep`. Alternativa más madura: **iris-lean** ([GitHub](https://github.com/leanprover-community/iris-lean)).

#### Bonus 1: Fiat Crypto — Verified C for Cryptographic Arithmetic
- **Autores**: Erbsen, Philipoom, Gross, Sloan, Chlipala
- **Venue**: IEEE S&P 2019
- **URLs**: [Paper](http://adam.chlipala.net/papers/FiatCryptoSP19/) | [GitHub](https://github.com/mit-plv/fiat-crypto)
- **Relevancia**: Pipeline spec→C verificado, integrado en BoringSSL de Google. Patrón: specification → verified transformation → C output = exactamente lo que MicroC necesita.

#### Bonus 2: CertiCoq / Paraskevopoulou PhD Thesis
- **Autor**: Zoe Paraskevopoulou (Princeton, advised by Appel)
- **Año**: 2020
- **URLs**: [Thesis](https://zoep.github.io/thesis_final.pdf) | [CertiCoq](https://github.com/CertiCoq/certicoq)
- **Relevancia**: Fuel-based logical relations para terminación y divergence preservation. λANF pipeline: cada pass verificado independientemente, compuesto end-to-end. Template para `stmtToMicroC` proof structure.

#### Bonus 3: Monniaux — CompCert TCB Analysis
- **Autores**: Monniaux, Boulme
- **Venue**: ESOP 2022
- **URL**: [arXiv](https://arxiv.org/abs/2201.10280)
- **Relevancia**: **MOTIVACIÓN para el roundtrip parser**: Monniaux identifica el parser C como componente no-verificado significativo en CompCert. Si MicroC tiene parser verificado (roundtrip theorem), elimina el parser del TCB — algo que CompCert no logra.

---

## 6. Insights de Nueva Bibliografía

Sección omitida (no se descargaron PDFs; se recopilaron URLs y summaries vía búsqueda online).

---

## 7. Síntesis de Insights

### Hallazgos clave (Top 10)

1. **Pancake es el precedente más cercano a MicroC**: C-like sin type system, functional big-step semantics, compiled via CakeML. Estudiar su diseño de semántica es prioritario antes de codear.

2. **Danielsson es la referencia arquitectural para roundtrip**: `parse ∘ print = id` formalizado en Agda con tipos dependientes. La técnica de codificar precedencia en el grammar combinator type se transfiere directamente a MicroC.

3. **El roundtrip parser elimina el parser del TCB de CompCert**: Monniaux (ESOP 2022) identifica el parser como gap significativo en CompCert. MicroC con roundtrip theorem cierra este gap — **novedad respecto a CompCert**.

4. **Fuel semantics deben diseñarse ANTES de todo**: Las lecciones L-265/L-325/L-288/L-289/L-292 forman un cluster tightly-coupled. Fuel = depth bound (max composition), no resource counter. 6 outcome paths en while son obligatorios.

5. **`Lean.Data.Parsec` es suficiente para el parser**: No necesitamos Megaparsec ni dependencias externas. El built-in Parsec provee monadic combinators. Para proofs, su simplicidad es ventaja.

6. **Bridge predicate pattern ya probado en Trust-Lean**: scalarBridge + loopBridge, injectivity free de constructor disjointness. Extender a `microCBridge` para MicroC↔Stmt correspondence.

7. **Narcissus + EverParse dan el framework conceptual**: Ambos derivan encoder+decoder de una spec común. Para MicroC: definir gramática como spec, derivar `microCToString` y `parseMicroC` como dual. Roundtrip es consecuencia.

8. **CertiCoq's fuel-based logical relations** aplican directamente a evalMicroC. Paraskevopoulou demuestra que fuel-indexed relations preservan terminación Y divergencia. Template para simulation proof.

9. **Oracle testing (CSmith/YARPGen pattern)** complementa la verificación formal: generar MicroC programs aleatorios, ejecutar por evalStmt y evalMicroC, comparar. Detecta bugs que la formalización no cubre (ej. overflow edge cases).

10. **iris-lean / SPLean no son necesarios para v1**: MicroC v1 opera con functional environment (VarName→Value), sin heap. Separation logic solo sería necesaria si extendemos a punteros en v2+.

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|:---:|:---:|-----------|
| Parser combinators insuficientes para C precedence | Media | Alto | Implementar Pratt parser o precedence climbing sobre Parsec |
| Roundtrip no cierra por canonicalization issues | Media | Alto | Definir canonical form primero; roundtrip solo sobre canonical |
| evalMicroC diverge de evalStmt en edge cases | Baja | Alto | Oracle tests + non-vacuity examples exhaustivos |
| Overflow de int64_t semántica no modelada | Media | Medio | Decidir: wrapping (como C) o unbounded (como Lean Int). Documenter |
| Short-circuit && / \|\| complejiza proof | Baja | Medio | Modelar como if-then-else desugaring (como Clight) |
| Build time explodes con MicroC modules | Baja | Medio | Módulos pequeños (~200 LOC), imports incrementales |

### Recomendaciones para planificación

1. **Estudiar Pancake + Danielsson ANTES de codear**: Son los dos precedentes más directos. Dedicar 1-2 días a leer papers.

2. **Diseñar MicroC AST como reflejo exacto de stmtToC output**: No inventar; leer CBackend.lean y derivar nodos MicroC que matchean 1:1 con su output string.

3. **Fase 0 (Foundations)**: MicroC AST + evalMicroC + fuelMono proof. Probar fuel monotonicity ANTES de bridge.

4. **Fase 1 (Translation)**: stmtToMicroC + simulation proof. Reutilizar bridge predicate pattern de v1.1.0.

5. **Fase 2 (Roundtrip)**: microCToString + parseMicroC + roundtrip theorem. Definir canonical form first.

6. **Fase 3 (Testing)**: Oracle tests (CSmith-style), non-vacuity examples, integration con AMO-Lean.

7. **Usar `Lean.Data.Parsec` built-in** — sin dependencias externas, simplicidad para proofs.

8. **Zero-sorry en cada fase** — no diferir.

### Recursos prioritarios (Top 5)

1. **Danielsson 2013** — Correct-by-construction pretty-printing ([PDF](https://www.cse.chalmers.se/~nad/publications/danielsson-correct-pretty.pdf))
2. **Pancake (PLOS 2023)** — C-like verified language ([PDF](https://cakeml.org/plos23.pdf))
3. **Narcissus (ICFP 2019)** — Verified encoder/decoder ([arXiv](https://arxiv.org/abs/1803.04870))
4. **Monniaux & Boulme (ESOP 2022)** — CompCert TCB analysis ([arXiv](https://arxiv.org/abs/2201.10280))
5. **Paraskevopoulou thesis** — Fuel-based logical relations ([PDF](https://zoep.github.io/thesis_final.pdf))

### Deep Analysis: Viabilidad de formalización

Los 26 lecciones + 20 documentos existentes + 15 papers online encontrados cubren **todos** los aspectos técnicos del proyecto:

- **Fuel semantics**: Cubierto por Trust-Lean existente (FuelMono.lean) + CertiCoq
- **Simulation proofs**: Template en Bridge/Correctness.lean (490 LOC, 0 sorry)
- **Roundtrip parser**: Danielsson + Narcissus + EverParse proveen el framework conceptual
- **MicroC AST design**: Pancake + Clight como precedentes directos
- **Testing**: CSmith + YARPGen metodología transferible
- **Lean 4 infrastructure**: Lean.Data.Parsec + Lean4Lean patterns

**Estimación de esfuerzo**: 2,200–2,800 LOC adicionales, 50–80 teoremas nuevos. Factible como extensión de Trust-Lean en 6-10 semanas.

---

## 8. Teoremas Extraídos

### Teoremas core del proyecto (extraídos de análisis + bibliografía)

#### Grupo 1: MicroC AST & Tipos (Foundations)

| # | Nombre | Statement informal | Dificultad |
|---|--------|-------------------|-----------|
| T1 | `MicroCStmt.DecidableEq` | MicroC statements have decidable equality | trivial |
| T2 | `MicroCExpr.DecidableEq` | MicroC expressions have decidable equality | trivial |
| T3 | `microC_stmt_size_pos` | Size of any MicroC statement is positive | easy |

#### Grupo 2: MicroC Evaluation (Fuel Semantics)

| # | Nombre | Statement informal | Dificultad |
|---|--------|-------------------|-----------|
| T4 | `evalMicroC_fuel_mono` | More fuel never changes evalMicroC result | hard |
| T5 | `evalMicroC_skip` | evalMicroC on skip is identity | trivial |
| T6 | `evalMicroC_assign_correct` | Assignment updates exactly one variable | easy |
| T7 | `evalMicroC_while_false_exit` | While with false condition terminates normally | easy |
| T8 | `evalMicroC_while_break` | Break in while body terminates loop normally | medium |
| T9 | `evalMicroC_while_continue` | Continue in while body re-enters loop | medium |
| T10 | `evalMicroC_while_return` | Return in while body propagates upward | medium |
| T11 | `evalMicroC_seq_assoc` | Sequential composition is associative | medium |
| T12 | `evalMicroCExpr_deterministic` | Expression evaluation is deterministic | easy |

#### Grupo 3: Translation (stmtToMicroC)

| # | Nombre | Statement informal | Dificultad |
|---|--------|-------------------|-----------|
| T13 | `stmtToMicroC_total` | Translation is total on well-formed Stmt | easy |
| T14 | `stmtToMicroC_preserves_structure` | seq maps to seq, ite maps to ite, etc. | easy |
| T15 | `stmtToMicroC_correct` | **CAPSTONE**: evalStmt ≡ evalMicroC ∘ stmtToMicroC | hard |
| T16 | `stmtToMicroC_assign_case` | Assignment case of simulation diagram | medium |
| T17 | `stmtToMicroC_ite_case` | If-then-else case of simulation diagram | medium |
| T18 | `stmtToMicroC_while_case` | While loop case of simulation diagram | hard |
| T19 | `stmtToMicroC_for_case` | For loop (desugaring to while) case | medium |
| T20 | `stmtToMicroC_call_case` | Function call case of simulation | medium |

#### Grupo 4: Pretty-Printer (microCToString)

| # | Nombre | Statement informal | Dificultad |
|---|--------|-------------------|-----------|
| T21 | `microCToString_deterministic` | Pretty-printing is deterministic | trivial |
| T22 | `microCToString_nonempty` | Non-skip statements produce non-empty strings | easy |
| T23 | `microCToString_balanced_braces` | Output has balanced braces | medium |
| T24 | `microCToString_balanced_parens` | Output has balanced parentheses | medium |
| T25 | `microCToString_injective` | Injective on canonical forms | hard |

#### Grupo 5: Parser (parseMicroC)

| # | Nombre | Statement informal | Dificultad |
|---|--------|-------------------|-----------|
| T26 | `parseMicroC_total` | Parser terminates on all inputs | easy |
| T27 | `parseMicroC_some_implies_valid` | Successful parse produces valid AST | medium |
| T28 | `parseMicroC_roundtrip` | **CAPSTONE**: parseMicroC(microCToString s) = some s | hard |
| T29 | `parseMicroC_expr_roundtrip` | Expression roundtrip sub-theorem | medium |
| T30 | `parseMicroC_stmt_roundtrip` | Statement roundtrip sub-theorem | medium |

### Por grupo temático

| Grupo | Cantidad | Trivial | Easy | Medium | Hard |
|-------|:---:|:---:|:---:|:---:|:---:|
| AST & Tipos | 3 | 2 | 1 | 0 | 0 |
| Evaluation | 9 | 1 | 3 | 4 | 1 |
| Translation | 8 | 0 | 2 | 4 | 2 |
| Pretty-Printer | 5 | 1 | 1 | 2 | 1 |
| Parser | 5 | 0 | 1 | 2 | 2 |
| **Total** | **30** | **4** | **8** | **12** | **6** |

### Orden de dependencias

```
T1, T2 (AST DecidableEq)
  └─ T3 (size_pos)
  └─ T5, T6 (evalMicroC base cases)
     └─ T12 (expr deterministic)
     └─ T7, T8, T9, T10 (while outcome cases)
        └─ T11 (seq assoc)
        └─ T4 (fuel_mono) ← GATE THEOREM
           └─ T13, T14 (translation basics)
              └─ T16, T17, T19, T20 (simulation per-case)
              └─ T18 (while simulation) ← HARDEST CASE
                 └─ T15 (stmtToMicroC_correct) ← CAPSTONE 1
  └─ T21, T22 (pretty-printer basics)
     └─ T23, T24 (structural properties)
     └─ T25 (injectivity)
        └─ T26 (parser terminates)
           └─ T27 (parse implies valid)
           └─ T29, T30 (sub-roundtrips)
              └─ T28 (roundtrip) ← CAPSTONE 2
```

---

## 9. Formalización Lean 4

Sección pendiente — se ejecutará durante la fase de implementación via `/plan-project`. Los 30 teoremas están especificados con sus dependencias y dificultades estimadas. La formalización se hará como extensión de Trust-Lean (path: `TrustLean/Verified/`).

### Archivos proyectados

| Archivo | Grupo | Teoremas | LOC estimadas |
|---------|-------|:---:|:---:|
| `TrustLean/Verified/MicroC/AST.lean` | AST & Tipos | T1-T3 | 150-200 |
| `TrustLean/Verified/MicroC/Eval.lean` | Evaluation | T4-T12 | 350-450 |
| `TrustLean/Verified/MicroC/Translation.lean` | Translation | T13-T20 | 400-500 |
| `TrustLean/Verified/MicroC/PrettyPrint.lean` | Pretty-Printer | T21-T25 | 250-300 |
| `TrustLean/Verified/MicroC/Parser.lean` | Parser | T26-T30 | 300-400 |
| `TrustLean/Verified/MicroC/Bridge.lean` | Integration | (bridge predicates) | 200-300 |
| `Tests/MicroC/NonVacuity.lean` | Non-vacuity examples | — | 150-200 |
| **Total** | | **30** | **1,800-2,350** |

---

## 10. Librería Generada

Sección omitida — no se creó librería nueva. Los teoremas se formalizarán como extensión directa de Trust-Lean en `TrustLean/Verified/MicroC/`.

- **Nombre**: TrustLean.Verified.MicroC
- **Path**: ~/Documents/claudio/trust-lean/TrustLean/Verified/MicroC/
- **Mathlib**: sí (hereda de Trust-Lean v4.26.0)
- **Build**: pendiente (se ejecutará durante implementación)
- **Uso**: extensión in-place de Trust-Lean (NO librería separada)
