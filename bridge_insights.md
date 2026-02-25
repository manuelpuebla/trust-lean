# Insights: Trust-Lean v1.1.0 Bridge — ExpandedSigma → Stmt

**Fecha**: 2026-02-21
**Dominio**: lean4
**Estado del objeto**: upgrade (extensión de Trust-Lean v1.0.0 completado con 0 sorry)

## 1. Análisis del Objeto de Estudio

### Resumen

El objeto de estudio es el **bridge ExpandedSigma → Stmt**, un nuevo frontend de Trust-Lean que traduce los tipos de amo-lean (ExpandedSigma, ScalarExpr, ScalarAssign, ScalarBlock, Gather, Scatter) al Core IR de Trust-Lean (Stmt, LowLevelExpr, VarName). Este bridge es la piedra angular para integrar la pipeline algebraica verificada de amo-lean con la generación de código certificada de Trust-Lean, permitiendo una cadena completa de correctness desde matemática pura hasta código C/Rust ejecutable.

Implementa seis funciones de traducción composables:
- `scalarExprToLLExpr` — ScalarExpr → LowLevelExpr
- `scalarAssignToStmt` — ScalarAssign → Stmt
- `scalarBlockToStmt` — ScalarBlock (List ScalarAssign) → Stmt
- `gatherToStmt` — Gather → Stmt (sequence of loads)
- `scatterToStmt` — Scatter → Stmt (sequence of stores)
- `expandedSigmaToStmt` — ExpandedSigma → Stmt (main entry)

Más una prueba de correctness principal: `expandedSigmaToStmt_correct`.

### Keywords

Verified codegen, amo-lean integration, ExpandedSigma, ScalarExpr, Stmt IR, trust boundary, bridge semantics, kernel expansion, memory abstraction, gather/scatter operations, load/store compilation, field-generic arithmetic, Sigma-SPL lowering, FRI protocol optimization, CodeGenSound instance, fuel monotonicity

### Estado actual del proyecto

- **Trust-Lean v1.0.0**: COMPLETADO (2026-02-21)
- **LOC compiladas**: 2,917 (Core + 3 Frontends + 2 Backends + Pipeline)
- **Nodos completados**: 13/13 (todos PASS)
- **Sorry count**: 0 — zero-sorry guarantee
- **Theorems**: 179 probados (incluye evalStmt_fuel_mono crítico)
- **Frontends actuales**: ArithExpr, BoolExpr, ImpStmt
- **Backends**: C, Rust

### Tipos de amo-lean (exactos, desde `/amo-lean/AmoLean/Sigma/`)

```lean
-- From Expand.lean
structure ScalarVar where
  name : String
  idx : Nat
  deriving Repr, BEq, Hashable, Inhabited

inductive ScalarExpr where
  | var : ScalarVar → ScalarExpr
  | const : Int → ScalarExpr
  | neg : ScalarExpr → ScalarExpr
  | add : ScalarExpr → ScalarExpr → ScalarExpr
  | sub : ScalarExpr → ScalarExpr → ScalarExpr
  | mul : ScalarExpr → ScalarExpr → ScalarExpr
  deriving Repr, BEq, Inhabited

structure ScalarAssign where
  target : ScalarVar
  value : ScalarExpr
  deriving Repr, BEq, Inhabited

abbrev ScalarBlock := List ScalarAssign

structure ExpandedKernel where
  inputVars : List ScalarVar
  outputVars : List ScalarVar
  body : ScalarBlock
  deriving Repr, Inhabited

-- From Basic.lean
abbrev LoopVar := Nat

inductive IdxExpr where
  | const : Nat → IdxExpr
  | var : LoopVar → IdxExpr
  | affine : (base : Nat) → (stride : Nat) → LoopVar → IdxExpr
  | add : IdxExpr → IdxExpr → IdxExpr
  | mul : Nat → IdxExpr → IdxExpr
  deriving Repr, BEq, Inhabited

structure Gather where
  count : Nat
  baseAddr : IdxExpr
  stride : Nat
  deriving Repr, Inhabited

structure Scatter where
  count : Nat
  baseAddr : IdxExpr
  stride : Nat
  deriving Repr, Inhabited

inductive Kernel where
  | identity : Nat → Kernel
  | dft : Nat → Kernel
  | ntt : Nat → Nat → Kernel
  | twiddle : Nat → Nat → Kernel
  | scale : Kernel
  | butterfly : Kernel
  | sbox : Nat → Nat → Kernel
  | partialSbox : Nat → Nat → Nat → Kernel
  | mdsApply : String → Nat → Kernel
  | mdsInternal : Nat → Kernel
  | addRoundConst : Nat → Nat → Kernel
  | butterfly4 : Kernel
  deriving Repr, BEq, Inhabited

inductive ExpandedSigma where
  | scalar : ExpandedKernel → Gather → Scatter → ExpandedSigma
  | loop : (n : Nat) → (loopVar : LoopVar) → ExpandedSigma → ExpandedSigma
  | seq : ExpandedSigma → ExpandedSigma → ExpandedSigma
  | par : ExpandedSigma → ExpandedSigma → ExpandedSigma
  | temp : (size : Nat) → ExpandedSigma → ExpandedSigma
  | nop : ExpandedSigma
  deriving Repr, Inhabited
```

### Semántica de amo-lean (eval functions)

```lean
def eval (env : ScalarVar → Int) : ScalarExpr → Int
  | .var v => env v
  | .const n => n
  | .neg e => -(eval env e)
  | .add e1 e2 => eval env e1 + eval env e2
  | .sub e1 e2 => eval env e1 - eval env e2
  | .mul e1 e2 => eval env e1 * eval env e2

def eval (env : LoopVar → Nat) : IdxExpr → Nat
  | const n => n
  | var v => env v
  | affine base stride v => base + stride * env v
  | add e1 e2 => eval env e1 + eval env e2
  | mul c e => c * eval env e
```

### Gaps identificados

| # | Gap | Severidad | Detalle |
|---|-----|-----------|---------|
| 1 | **Value type extension** | ALTA | Trust-Lean v1.0 solo tiene `int Int \| bool Bool`. Bridge necesita `uint64`, `uint32`, `array Value` para campos Goldilocks/BabyBear |
| 2 | **Memory bridge formalization** | ALTA | Teoremas `memory_bridge_read`/`memory_bridge_write` esbozados en DESIGN_SPEC pero no especifican serialización `Memory α → Value.array` |
| 3 | **allocTemp missing** | MEDIA | Caso `.temp` de ExpandedSigma requiere allocate temporal arrays. Stmt no tiene primitivo `allocTemp` |
| 4 | **Affine index compilation** | MEDIA | IdxExpr (base + stride*loopVar) debe compilar a LowLevelExpr. No formalizado |
| 5 | **Fuel for loops** | MEDIA | ExpandedSigma.loop(n) → Stmt.for_ requiere fuel ≥ n. Sin análisis de terminación |
| 6 | **evalExpandedSigma formal** | BAJA | DESIGN_SPEC asume existencia de `evalExpandedSigma` en amo-lean pero no define semántica exacta |

### Dependencias

1. **Teoría de números**: Aritmética modular (campos Goldilocks/BabyBear), propiedades de inversos multiplicativos
2. **Lean 4 formal verification**: Inducción sobre tipos inductivos, fuel-based termination, typeclass design
3. **Semantics preservation**: Commuting diagrams (`evalExpandedSigma ≡ evalStmt ∘ expandedSigmaToStmt`)
4. **Memory model**: Functional environment (LowLevelEnv := VarName → Value), store/load @[simp] lemmas
5. **Signal processing**: Σ-SPL de SPIRAL project (loop, compute, gather, scatter)

---

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Título | Aplicación directa |
|----|--------|---------------------|
| **L-306** | Bridge predicate + injectivity for environment correspondence | CRÍTICA: patrón fundamental para mapeo entre ambientes de ExpandedSigma y Stmt |
| **L-307** | Statement-oriented frontends bypass CodeGenSound typeclass | DIRECTA: amo-lean es statement-oriented, necesita compile_correct con preservación de puente |
| **L-283** | Store/load @[simp] lemmas essential for amo-lean integration | FUNDACIONAL: todos los 12 Stmt constructores incluyendo store/load cubiertos |
| **L-288** | Fuel independence forms base cases for fuel monotonicity induction | Casos base para pruebas de monotonía en bridge |
| **L-292** | Generalize fuel monotonicity to all non-outOfFuel outcomes | Estrategia de prueba: generalizar primero, especializar después |
| **L-297** | Three-part codegen contract: termination + result + frame | Contract verificado aplicable a compile_correct del bridge |
| **L-300** | wellTyped predicate pattern restricts CodeGenSound | Prevenir edge cases en traducción de tipos |
| **L-305** | Nested induction (structural + fuel) for while-loop correctness | Si bridge maneja loops con fuel |
| **L-290** | Functional environment model yields clean equational proofs | Simplificación para environment updates |
| **L-276** | Propositional equality in env update enables cleaner rewriting | Usar `=` en lugar de BEq `==` en updates |
| **L-277** | LowLevelEnv total function validated over Option Value | Justificación para environment model |
| **L-296** | Explicit instance names resolve typeclass projection ambiguity | CRÍTICA para cross-project imports con autoImplicit false |
| **L-253** | Recursive typeclass instance causes circular reference | Definir como `def` standalone primero, luego instancia |
| **L-257** | ExtractableSound as standalone Prop better than typeclass law | Desacoplar interfaces operacionales de obligaciones de verificación |
| **L-291** | Parameterized IH helpers enable proof reuse | Reutilizar IH entre casos recursivos |
| **L-144** | Precondiciones precisas > monotonía general | Alternativa cuando monotonía general es falsa |
| **L-308** | Backend Emitter Architecture for Code Generation | Reutilizable: backends son pretty-printers fuera de TCB |

### Anti-patrones a evitar

| Anti-patrón | Lección | Impacto |
|-------------|---------|---------|
| **Asumir monotonía sin verificar TODOS los constructores** | L-143 | evalSigmaAlg NO es monótona en writeMem.size por `.temp`. Verificar 12+6 constructores |
| **Referenciar función recursiva dentro de su propia instancia** | L-253 | Circular reference. Definir `def compile_aux` ANTES de instance |
| **Confundir `get?` con `getElem?`** | L-220 | Bracket notation `g[key]?` es `getElem?`, no `get?` |
| **Omitir nombre explícito de instance con autoImplicit false** | L-296 | `[inst : CodeGenerable α]` no `[CodeGenerable α]` |
| **Usar `simp` completo en proofs críticas** | L-305 | Impredecible entre versiones. Usar `simp only [lista]` |
| **Diferir propiedades fundacionales** | L-114 | NUNCA defer FUNDACIONAL. De-risk con sketch ANTES |

### Técnicas reutilizables clave

**1. Bridge Predicate Pattern (L-306)**
```lean
-- Correspondencia entre ambientes
∀ v, llEnv (user (vn v)) = int (env v)

-- Preservación en actualizaciones
bridge_after_assign : ∀ vn name value env,
  bridge vn env → bridge vn (env.update name value)

-- Injectivity
inj_vn : ∀ v1 v2, vn v1 = vn v2 → v1 = v2
```

**2. Statement-Oriented compile_correct (L-307)**
```lean
theorem compile_correct (stmt : Stmt) :
  ∀ env lle,
    bridge env lle →
    ∃ fuel lle',
      evalStmt fuel lle (compile stmt) = some (.normal, lle') ∧
      bridge (updateEnv env stmt) lle'
```

**3. Three-Part Codegen Contract (L-297)**
```lean
-- (1) Terminación: ∃ fuel, evalStmt fuel env code = some (.normal, result)
-- (2) Resultado: evalExpr result resultVar = some (denote expr env)
-- (3) Frame: ∀ v, result (user (varNames v)) = env v
```

---

## 3. Bibliografía Existente Relevante

### Documentos clave

| Documento | Relevancia | Contribución al bridge |
|-----------|------------|------------------------|
| **CompCert** (Leroy et al. 2016) | CRÍTICA | Simulation methodology para bridge lemmas. CompCert→Clight como template |
| **Accelerating Verified Compiler** (Gross et al. 2022) | CRÍTICA | Fiat-Crypto pipeline: reglas de reescritura algebraicas + extraction. 1000x speedup |
| **Compositional Optimizations CertiCoq** (Paraskevopoulou 2021) | CRÍTICA | Logical relations con relational invariants para multi-pass verification |
| **Verified Code Transpilation LLMLIFT** (Bhatia et al. 2024) | ALTA | Levantamiento verificado GPL→DSL con invariantes de loop |
| **Modelado Formal Rust y Compilación Verificada** | ALTA | Arquitectura Hacspec→Lean→Rust verificado |
| **Lean-egg** (Rossel et al. 2026, POPL) | ALTA | Equality saturation tactic en Lean: conditional rewrites, proof reconstruction |
| **Bridging Syntax/Semantics in E-Graphs** (Rossel 2024) | ALTA | Binders en e-graphs, De Bruijn, dynamic rewrites |
| **HEC** (Yin et al. 2025) | ALTA | Equivalence checking post-transformación via e-graphs + MLIR |
| **Clight Semantics** (Blazy, Leroy 2009) | MEDIA | Big-step operational semantics en Coq. Template para ExpandedSigma formal spec |
| **NTT Verification** (Trieu 2025) | MEDIA | Fiat-Crypto framework: Barrett/Montgomery reduction |
| **AMO-Lean zkVM** | ALTA | FRI compiler verificado, Poseidon/Rescue, integración CUDA/GPU |

### Grafo de conceptos relacionados

```
CompCert (Coq verified compiler)
        ↓
Clight Semantics (big-step)
        ↓
╔════════════════════════════════════╗
║  Verified Compilation Bridge       ║
║  (composition + correctness)       ║
╚════════════════════════════════════╝
       ↙              ↖
Rewrite Rules      Equality Saturation
(algebraic)        (e-graphs + egg)
      ↓                   ↓
Fiat Cryptography    Lean-egg Tactic
(Coq synthesis)      (POPL 2026)
      ↓                   ↓
      └────────┬──────────┘
               ↓
╔═════════════════════════════════╗
║  Trust-Lean v1.1 Bridge         ║
║  ExpandedSigma → Stmt           ║
║  Cross-DSL translation          ║
║  + correctness proofs           ║
╚═════════════════════════════════╝
               ↓
    ┌──────────┼──────────┐
    ↓          ↓          ↓
 C Backend  Rust Backend  zkVM
                        (AMO-Lean)
```

### Gaps bibliográficos

| Tema | Cobertura | Gap |
|------|-----------|-----|
| Bridge Lemmas (Statement ↔ ExpandedSigma) | Parcial | CompCert tiene simulation lemmas, pero NO específicamente para constraint languages |
| Constraint System Semantics | Media | AIR formalizado, pero NO big-step semantics comparable a Clight |
| Optimized Circuit Lowering | Baja | ROVER para RTL, AMO-Lean para FRI — NO bridge genérico verificado |
| GPU Correctness in Compilation | Media | AMO-Lean tiene CUDA backend, pero NO formal verification de GPU codegen |

---

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Proyecto fuente | Resultado | Aplicación al bridge |
|-----------|-----------------|-----------|----------------------|
| **Bridge Lemma Pattern** | LeanScribe v3.0 | `assignmentsToStmt_correct` conecta List Assignment con Stmt IR, reutiliza TODA infraestructura Fase 1 | Crear lemma puente para ExpandedSigma→Stmt sin reprobar inducción. Reduce LOC ~30% |
| **Typeclass Extensibility** | LambdaSat v0.1 | -20.3% LOC pero +14.6% teoremas. +43.9% densidad | Bridges como instances sin recompilar IR |
| **Fuel max Composition** | LeanScribe + CompCert | Probado: max (no +) es correcto. Gemini QA fue falso positivo | Mantener `max` para composición en bridges |
| **Separación Algebraic/Implementation** | SuperTensor v0.4→v0.5 | 5 sorry cerrados. Proof más legible | Capa 1: algebraic (ring), Capa 2: implementation (foldl+invariant) |
| **Translation Validation** | VR1CS v1.2-1.3 | E-graph REMOVIDO de TCB. 7 congruence theorems | Bridge puede ser oracle, witness checker es pequeño |
| **Zero-Sorry Mandate** | VR1CS, LambdaSat, SuperTensor | 0 sorry en 16K-21K LOC cada uno | Trust-Lean v1.1.0 DEBE cerrar en 0 sorry |

### Decisiones arquitecturales aplicables

| Decisión | Justificación | Aplicación |
|----------|---------------|------------|
| **Common IR Layer** | Fiat-Crypto unifica 5+ backends via Common IR | ExpandedSigma→Stmt→{C, Rust}. Sin duplication |
| **Sum Type IR (no phantom types)** | Phantom types → proof explosion (10+ goals por match) | Mantener Value = int Int \| bool Bool |
| **Proof-First Order** | @[simp] lemmas anotadas durante dev, no retrofit | Definir tipos → probar fuel_mono → ENTONCES CodeGenSound |
| **Zero-Sorry Viability** | VR1CS 16K LOC 0 sorry, LambdaSat 6K 0 sorry | v1.1.0 DEBE mantener 0 sorry |
| **No Hardcoding Domain Logic** | Conv no es matmul reducible (SuperTensor) | Si ExpandedSigma tiene ops sin equivalencia Stmt, marcar `.custom` |

### Benchmarks de referencia

| Métrica | LeanScribe | VR1CS v1.3 | Trust-Lean v1.0 | Target v1.1 |
|---------|:---:|:---:|:---:|:---:|
| LOC total | 3,095 | 14,600 | 2,917 | 4,500–5,500 |
| Sorry | 0 | 0 | 0 | **0** |
| Theorems | 72 | ~301 | 179 | **220–260** |
| @[simp] lemmas | 42 | — | ~60 | **80–100** |
| Build time | ~2m | ~8m | ~4m | **<6m** |
| Bridge lemma LOC | 60–80 | — | — | **80–120** |

### Errores evitados

| Error | Lección | Aplicación |
|-------|---------|------------|
| Phantom types → proof explosion | LeanScribe pre-v1 | NO type-indexed Values en bridge |
| Asumir monotonía sin verificar | L-143 | Verificar TODOS los constructores antes |
| Diferir propiedades fundacionales | SuperTensor v0.2 | Value extension COMPLETA en primera fase |
| `simp` completo en proofs críticas | VR1CS fase 7 | `simp only [...]` SIEMPRE |
| Circular typeclass instances | L-253 | `def compile_aux` ANTES de instance |
| Fuel composición + vs max | LeanScribe debate | SIEMPRE `max` para secuencias |

---

## 5. Nueva Bibliografía Encontrada

### Papers descargados (5/5)

| # | Paper | Autores | Año | Path local | Relevancia |
|---|-------|---------|-----|------------|------------|
| 1 | **HELIX: A Case Study in Verified Code Generation for Signal Processing** | Vadim Zaliva, Franz Franchetti | 2018 (FHPC) | `biblioteca/verificacion/zaliva-helix-formal-verification-dsp-codegen-2018.pdf` (749KB) | **DIRECTA** — Σ-HCOL formalism es precedente exacto de ExpandedSigma |
| 2 | **HELIX: From Math to Verified Code** | Vadim Zaliva, Franz Franchetti | 2020 (VSTTE) | `biblioteca/verificacion/zaliva-helix-verified-translation-functional-imperative-vstte-2020.pdf` (379KB) | **DIRECTA** — Verificación de traducción funcional→imperativa |
| 3 | **A Verified Algebraic Representation of Cairo Program Execution** | Jeremy Avigad et al. | 2021 (arXiv:2109.14534) | `biblioteca/verificacion/avigad-verified-algebraic-cairo-execution-lean-2021.pdf` (266KB) | **ALTA** — Verificación en Lean de ejecución sobre campos finitos |
| 4 | **Semantics Lifting for FFT Signal Transforms** | Zhang et al. | 2025 (TPSA) | `biblioteca/verificacion/zhang-semantics-lifting-fft-spiral-2025.pdf` (568KB) | **ALTA** — Metodología de lifting semántico para SPIRAL |
| 5 | **Cairo — a Turing-complete STARK-friendly CPU Architecture** | Lior Goldberg et al. | 2021 (IACR ePrint 2021/1063) | `biblioteca/verificacion/goldberg-cairo-stark-friendly-cpu-2021.pdf` (411KB) | **MEDIA** — Arquitectura CPU STARK-friendly, modelo de memoria |

### Papers ya existentes en biblioteca

- **CompCert** (Leroy et al.) — ya indexado en `verificacion/`
- **Fiat-Crypto** (Gross et al.) — ya indexado en `verificacion/`
- **CertiCoq** (Paraskevopoulou) — ya indexado en `verificacion/`

### Papers encontrados pero no descargados

| Paper | Razón |
|-------|-------|
| BRIDGE (Weber et al. 2023) — Bridging syntax and semantics | Ya cubierto por Lean-egg (mismo grupo) |
| ProofBridge (formal systems interop) | No directamente relevante al bridge Sigma→Stmt |
| ethSTARK documentation | Documentación técnica, no paper formal |

### Resumen de búsqueda

Se realizaron 9 búsquedas web cubriendo:
1. Verified compilation bridges + IR en Lean 4
2. Sigma-SPL formal semantics + SPIRAL
3. Cairo STARK constraint system + AIR
4. HELIX formal verification DSP codegen (Coq)
5. Avigad verified algebraic Cairo execution (Lean)
6. Fiat-crypto pipeline verified extraction
7. HELIX verified translation functional→imperative
8. Semantics lifting FFT signal transforms
9. CompCert memory model bridging

El hallazgo más significativo es que **HELIX (Zaliva & Franchetti)** formaliza en Coq exactamente el mismo tipo de pipeline que amo-lean → Trust-Lean, incluyendo los operadores Gather/Scatter con la misma semántica.

---

## 6. Insights de Nueva Bibliografía

### 6.1 HELIX: Σ-HCOL como precedente formal de ExpandedSigma

**Paper**: Zaliva & Franchetti, FHPC 2018 + VSTTE 2020

**Descubrimiento clave**: El formalismo Σ-HCOL de HELIX es el **precedente teórico exacto** de ExpandedSigma en amo-lean.

**Pipeline HELIX** (verificado en Coq):
```
Mathematical Formula → OL → Σ-OL → i-Code → LLVM
                              ↕ (HELIX verifies)
                       HCOL → Σ-HCOL → h-Code → LLVM
```

**Mapeo directo Σ-HCOL → ExpandedSigma**:

| HELIX (Σ-HCOL) | amo-lean (ExpandedSigma) | Semántica |
|-----------------|--------------------------|-----------|
| `Scat_f ∘ K ∘ Gath_g` | `.scalar kernel gather scatter` | Sparse embedding: read → compute → write |
| `MR_{k,f,z}` (iterative map-reduce) | `.loop n loopVar body` | Iteración con acumulador |
| Composition `A ; B` | `.seq a b` | Ejecución secuencial |
| Direct sum `A ⊕ B` | `.par a b` | Ejecución paralela (partitioned) |

**Insights técnicos de HELIX para el bridge**:

1. **Carrier type abstraction**: HELIX abstrae el tipo carrier `R` con algebraic properties via MathClasses typeclasses. amo-lean hace lo mismo — Trust-Lean puede trabajar con `Int` y los axiomas de campo viven fuera.

2. **Setoid rewriting para semantic preservation**: HELIX usa setoid rewriting (no Leibniz equality) para probar equivalencia semántica entre niveles. Esto es relevante si amo-lean tiene tipos con propositional vs boolean equality.

3. **Translation validation approach**: SPIRAL genera la traza de reescritura, HELIX la verifica en Coq. Esto valida la estrategia de translation validation de Trust-Lean (L-298: bridge puede ser oracle, witness checker es pequeño).

4. **El patrón `Scat ∘ K ∘ Gath` es EXACTAMENTE el caso `.scalar`**: En HELIX, esta composición es el building block fundamental. En amo-lean, `ExpandedSigma.scalar kernel gather scatter` tiene la misma estructura: gather (read from input), kernel (compute), scatter (write to output).

### 6.2 Avigad et al.: Verificación de ejecución Cairo en Lean

**Paper**: arXiv:2109.14534 (2021)

**Contexto**: Verificación formal en **Lean 3** de que los datos satisfaciendo AIR (Algebraic Intermediate Representation) corresponden a una traza de ejecución válida de Cairo.

**Definiciones clave del paper**:
```lean
-- Cairo values son elementos de campo finito F
-- Memory: función pura F → F (read-only, no side effects)
def mem : F → F

-- Register state
structure register_state (F : Type*) :=
  (pc : F) (ap : F) (fp : F)

-- Next-state como relación proposicional (Prop, no función)
def instruction.next_state (i : instruction) (mem : F → F)
    (s t : register_state F) : Prop
```

**Insights para el bridge**:

1. **Memoria como función pura**: Cairo modela memoria como `F → F` — lectura sin side effects. Trust-Lean usa `LowLevelEnv := VarName → Value` con la misma filosofía. El bridge hereda este modelo limpio.

2. **Next-state como Prop (no función)**: Avigad define la transición como `Prop`, no como `def`. Esto es más flexible para verificación. Sin embargo, Trust-Lean usa `def evalStmt` (función), lo cual es más ejecutable. Para el bridge, la función es preferible (L-307: statement-oriented con función explícita).

3. **Lean's simplifier con tagged rewrite rules**: Avigad encontró que anotar reglas de reescritura con tags fue muy útil para `simp`. Esto confirma la estrategia de L-283 (@[simp] lemmas con nombres explícitos).

4. **`norm_num` para cálculos numéricos verificados**: Útil para probar identidades aritméticas concretas en ScalarExpr evaluation.

5. **Precedente de verificación Lean sobre campos finitos**: Aunque es Lean 3, demuestra que verificación formal sobre campos finitos es viable. amo-lean ya trabaja sobre campos — el bridge no necesita re-formalizar la aritmética de campo.

### 6.3 Zhang et al.: Semantics Lifting para SPIRAL (TPSA 2025)

**Paper**: Semantics Lifting for FFT Signal Transforms (2025)

**Insight principal**: Propone una metodología de "lifting semántico" donde la semántica de alto nivel (fórmulas matemáticas) se preserva al descender por capas de compilación. Relevante para la cadena amo-lean → Trust-Lean → C/Rust.

**Aplicación al bridge**: La cadena de lifting es:
```
amo-lean (algebraic semantics)
  → Trust-Lean (operational semantics: evalStmt)
    → C/Rust (computational semantics)
```

El bridge vive en la primera flecha. El paper confirma que preservar la semántica en cada paso (no end-to-end) es la metodología correcta.

### 6.4 Goldberg et al.: Cairo STARK-friendly CPU (IACR 2021/1063)

**Paper**: Describe la arquitectura Cairo — CPU minimalista diseñada para generar trazas STARK-friendly.

**Insights para el bridge**:
- Cairo's memory model (write-once, non-deterministic allocation) es más restrictivo que Trust-Lean's (functional environment).
- Las constraint equations de Cairo sobre AIR informan cómo formalizar constraints sobre Stmt execution.
- Relevancia indirecta: si amo-lean eventualmente genera constraints Cairo, Trust-Lean necesitará modelar write-once memory.

### 6.5 Conceptos nuevos incorporados al grafo

| Concepto | Fuente | Conexiones |
|----------|--------|------------|
| **Σ-HCOL** | HELIX | → ExpandedSigma, → Gather/Scatter, → verified codegen |
| **Sparse embedding (Scat ∘ K ∘ Gath)** | HELIX/SPIRAL | → ExpandedSigma.scalar, → memory model |
| **Translation validation** | HELIX + VR1CS | → bridge correctness, → oracle pattern |
| **Carrier type abstraction** | HELIX/MathClasses | → field-generic arithmetic, → amo-lean typeclasses |
| **Semantics lifting** | Zhang/SPIRAL | → compilation pipeline, → multi-level preservation |
| **Write-once memory** | Cairo/Goldberg | → constraint systems, → future Value extension |
| **Tagged rewrite rules** | Avigad/Cairo-Lean | → @[simp] strategy, → L-283 |

### 6.6 Conexiones descubiertas

```
HELIX (Σ-HCOL, Coq)
    ↕ isomorphism
amo-lean (ExpandedSigma, Lean 4)
    ↓ bridge
Trust-Lean (Stmt, Lean 4)
    ↓ backends
C / Rust / LLVM

HELIX translation validation ≈ Trust-Lean bridge correctness
HELIX setoid rewriting ≈ Trust-Lean @[simp] lemmas
Avigad Cairo-Lean (Lean 3) → precedent for Lean verification over finite fields
Cairo memory (F → F) ≈ Trust-Lean LowLevelEnv (VarName → Value)
```

### 6.7 Análisis profundo de indexación (Wave 3)

**Concepto graph actualizado**: 990 nodos, 718 edges (29 nuevos nodos de este batch).

#### Structural mapping completo (amo-lean / HELIX / SPIRAL)

| amo-lean (ExpandedSigma) | HELIX (Σ-HCOL, Coq) | SPIRAL (Sigma-SPL) |
|--------------------------|----------------------|---------------------|
| `.scalar kernel gather scatter` | `Scat_f ∘ K ∘ Gath_g` (compute) | compute |
| `.loop n v body` | `IUnion n f` (indexed family reduction) | Sigma-SPL sum |
| `.seq s1 s2` | `SHCompose` | sequential |
| `.par s1 s2` | `HTSUMUnion` | parallel |
| `.temp size body` | (implicit allocation) | temp buffer |
| `.nop` | `IdOp` | identity |

| Trust-Lean (Stmt) | HELIX (DHCOL) | SPIRAL (icode) |
|-------------------|---------------|----------------|
| `.assign` | `DSHAssign` | assignment |
| `.store` / `.load` | `DSHMemCopy` | array access |
| `.seq` | `DSHSeq` | sequence |
| `.while` / `.for_` | `DSHPower` / `DSHLoop` | iteration |
| `.ite` | (conditional) | conditional |
| `.skip` | (nop) | nop |

#### HELIX three-layer proof strategy (VSTTE 2020, p.19-21)

HELIX NO compila directamente de funcional a imperativo. Introduce una capa intermedia `MHCOL`:

```
Sigma-HCOL → MHCOL (memory layout mapping) → DHCOL (imperative control)
```

**Implicación para Trust-Lean**: Considerar una capa intermedia `VarMapping` que asigne `ScalarVar` (input/output/temp) a `VarName` concretos en el entorno de Stmt. Sin esta capa, la prueba de correctness combina dos concerns: (1) aplanamiento de estructura y (2) mapeo de memoria.

#### `DSH_pure` typeclass (HELIX VSTTE 2020)

HELIX define una typeclass `DSH_pure` para programas imperativos "puros":
1. **mem_stable**: no alloca/libera bloques de memoria
2. **mem_write_safe**: solo modifica el bloque de memoria del output pointer

Trust-Lean debería formalizar un análogo `PureStmt`: un `Stmt` generado de `ExpandedKernel` satisface `mem_stable` (no nuevas arrays) y `write_bounded` (solo escribe a variables/índices de output designados).

#### `SHCOL_DSHCOL_mem_block_equiv` (HELIX VSTTE 2020, p.21)

La equivalencia semántica entre capas es una relación ternaria:
- (a) Estado de memoria antes de DHCOL (`mb`)
- (b) Estado de memoria después de DHCOL (`ma`)
- (c) Valores de elementos cambiados por MHCOL (`md`)

Este es EXACTAMENTE el patrón para `bridge env lle → ∃ lle', evalStmt fuel lle (compile σ) = some (.normal, lle') ∧ bridge (eval env σ) lle'`.

#### Cairo permutation argument para Gather/Scatter (Goldberg 2021, §9.6-9.7)

Cairo usa columnas de producto acumulativo `c_j = prod_{i=0}^{j} (z - a_i)` para probar que dos secuencias son permutaciones. Aplicable a verificar que `Gather`/`Scatter` permutan correctamente índices de arrays. Scatter requiere **injectividad** (no colisiones de índices).

#### Cadena completa de dependencias descubierta

```
Cairo AIR (Goldberg 2021)
  → verified by Lean (Avigad 2021)
    → ExpandedSigma formalization (amo-lean)
      → Bridge compilation (Trust-Lean v1.1.0)
        → Stmt IR evaluation (Trust-Lean Core)
          → C/Rust backend emission (Trust-Lean Backend)
```

Cada flecha tiene (o puede tener) una prueba formal de preservación semántica.

---

## 7. Síntesis de Insights

### Hallazgos clave

**1. El bridge es un frontend statement-oriented (L-307), NO expression-oriented**
- ExpandedSigma es estructuralmente similar a ImpStmt (seq, loop, nop).
- NO usar CodeGenSound directamente; seguir el patrón de `compile_correct` con bridge predicate como postcondición.
- El teorema principal es: `∀ env lle, bridge env lle → ∃ fuel lle', evalStmt fuel lle (expandedSigmaToStmt σ) = some (.normal, lle') ∧ bridge (evalExpandedSigma env σ) lle'`

**2. HELIX Σ-HCOL es el precedente formal EXACTO del bridge** *(NUEVO — Wave 2)*
- El formalismo Σ-HCOL de HELIX (Coq) es isomorfo a ExpandedSigma (Lean 4).
- `Scat_f ∘ K ∘ Gath_g` = `ExpandedSigma.scalar kernel gather scatter` — misma semántica.
- HELIX verificó en Coq exactamente el tipo de pipeline que Trust-Lean necesita verificar en Lean 4.
- **Implicación**: la factibilidad del bridge está demostrada por el precedente HELIX.

**3. Gather/Scatter son secuencias de load/store — ya probados en Trust-Lean v1.0**
- `gatherToStmt` = sequence of `Stmt.load` (ya tiene @[simp] lemmas por L-283)
- `scatterToStmt` = sequence of `Stmt.store`
- Reutilización estimada: ≥90% de infraestructura existente
- HELIX confirma: Gather/Scatter son operadores primitivos de Σ-HCOL con semántica bien definida.

**4. ScalarExpr mapea casi 1:1 a LowLevelExpr**
- ScalarExpr tiene 6 constructores: var, const, neg, add, sub, mul
- LowLevelExpr tiene: litInt, litBool, varRef, binOp, unaryOp, powCall
- Traducción directa: `var → varRef`, `const → litInt`, `neg → unaryOp .neg`, `add → binOp .add`, `sub → binOp .sub`, `mul → binOp .mul`
- Correctness: inducción estructural simple sobre ScalarExpr

**5. IdxExpr (affine indexing) necesita compilación a LowLevelExpr**
- `IdxExpr.affine base stride v → litInt base + litInt stride * varRef v`
- No es difícil pero debe formalizarse con lemma de correctness
- Las 5 formas de IdxExpr (const, var, affine, add, mul) compilan por inducción

**6. El caso `.temp` de ExpandedSigma es el más delicado (L-143)**
- `.temp size body` reemplaza writeMem con `Memory.zeros size`
- Esto REDUCE writeMem.size — invalida monotonía general
- Estrategia: precondiciones precisas en call sites (L-144), no monotonía general
- En Trust-Lean: modelar como secuencia de assigns inicializando un bloque temporal

**7. Value type extension puede NO ser necesaria para v1.1**
- amo-lean's ScalarExpr evalúa a `Int` — que ya es `Value.int`
- Campos finitos (Goldilocks/BabyBear) son `Int` modular — la aritmética modular vive en amo-lean, NO en Trust-Lean
- **Principio clave** (DESIGN_SPEC): "Field axioms live in amo-lean, NOT in Trust-Lean. Trust-Lean only faithfully compiles scalar operations over concrete machine types."
- Implicación: v1.1 puede operar SOLO con `Value.int` existente. Value extension (uint64, array) diferible a v1.2
- Avigad et al. confirman: verificación Lean sobre campos finitos es viable sin extender el tipo Value.

**8. Fuel para loops tiene solución conocida (L-288, L-292)**
- `ExpandedSigma.loop n _ body` → `Stmt.for_` con fuel ≥ n
- `evalStmt_fuel_mono` (ya probado) garantiza que más fuel nunca cambia resultado
- Fuel provisionado como `n * fuel_body` con max composition

**9. La prueba de correctness sigue el patrón three-part contract (L-297)**
- (1) Terminación: ∃ fuel suficiente (provisionado por estructura de ExpandedSigma)
- (2) Resultado: bridge preserved después de ejecución
- (3) Frame: variables de usuario no modificadas

**10. Translation validation es la metodología correcta** *(NUEVO — Wave 2)*
- HELIX usa translation validation: SPIRAL genera la traza, HELIX verifica en Coq.
- Trust-Lean bridge hace lo mismo: amo-lean genera ExpandedSigma, Trust-Lean verifica la compilación a Stmt.
- Avigad et al. confirman: tagged rewrite rules + `norm_num` facilitan la verificación.
- Estrategia @[simp] de L-283 alineada con lo que funciona en la literatura.

**11. Carrier type abstraction elimina necesidad de campo genérico en Trust-Lean** *(NUEVO — Wave 2)*
- HELIX abstrae el tipo carrier `R` con MathClasses typeclasses.
- amo-lean hace lo mismo sobre campos finitos.
- Trust-Lean opera sobre `Int` (Value.int) — la abstracción de campo NO cruza al bridge.
- Separación limpia: amo-lean owns algebra, Trust-Lean owns compilation.

**12. Semantics lifting confirma verificación por capas (no end-to-end)** *(NUEVO — Wave 2)*
- Zhang et al. (TPSA 2025) formalizan lifting semántico para SPIRAL.
- La cadena es: algebraic → operational → computational.
- El bridge verifica UN paso (algebraic → operational). Backends son pretty-printers fuera del TCB.

**13. Cross-project import requiere lakefile dependency management**
- Trust-Lean necesitará `require amoLean from ./../amo-lean` en lakefile
- O alternativamente: definir tipos wrapper en Trust-Lean que duplican las definiciones de amo-lean
- La opción limpia es dependency directa; la opción robusta es wrapper types

**14. CompCert simulation methodology es el template correcto**
- Forward simulation: si amo-lean da un paso, Trust-Lean da un paso correspondiente
- Bisimulation no necesaria (bridge es one-way)
- Usar `bridge` predicate como invariante de simulación

### Riesgos identificados

| Riesgo | Severidad | Mitigación |
|--------|-----------|------------|
| amo-lean API changes rompen el bridge | MEDIA | Pin versión de amo-lean, thin wrapper interface |
| `.temp` constructor invalida invariantes | ALTA | Precondiciones precisas (L-144), NO monotonía general |
| Cross-project dependencies en lake | MEDIA | Test build con dependency antes de empezar |
| evalExpandedSigma no definida formalmente en amo-lean | BAJA | Definir en Trust-Lean side como spec function |
| Fuel insuficiente para loops anidados | MEDIA | fuel = product of loop bounds, comprobable |
| HELIX usó Coq, no Lean 4 — tactics difieren | BAJA | Las estrategias de proof (simulation, inducción) son transferibles; solo la syntaxis de tactic difiere |

### Recomendaciones para planificación

1. **Fase 1: Setup + ScalarExpr bridge** (FUNDACIONAL)
   - Configurar lakefile dependency o wrapper types
   - Implementar `scalarExprToLLExpr` + correctness (inducción directa, ~50 LOC)
   - Implementar `idxExprToLLExpr` + correctness (~40 LOC)
   - Estos son building blocks para todo lo demás

2. **Fase 2: Gather/Scatter + ScalarBlock** (INTERMEDIO)
   - `scalarAssignToStmt` + correctness (~30 LOC)
   - `scalarBlockToStmt` = foldl de assigns (~40 LOC)
   - `gatherToStmt` = sequence of loads (~60 LOC)
   - `scatterToStmt` = sequence of stores (~60 LOC)
   - Reutiliza store/load @[simp] lemmas existentes
   - Seguir patrón HELIX `Scat ∘ K ∘ Gath` para `.scalar` case

3. **Fase 3: expandedSigmaToStmt** (CRÍTICO)
   - 6 cases: scalar, loop, seq, par, temp, nop
   - `nop → skip`, `seq → Stmt.seq`, `par → Stmt.seq` (sequential execution)
   - `loop n v body → Stmt.for_` con fuel provisioning
   - `scalar kernel gather scatter → gatherToStmt ++ scalarBlockToStmt kernel.body ++ scatterToStmt`
   - `temp size body → init assigns ++ expandedSigmaToStmt body`

4. **Fase 4: Correctness proof** (HOJA CRÍTICA)
   - `expandedSigmaToStmt_correct` por inducción sobre ExpandedSigma
   - Usa bridge predicate (L-306) + three-part contract (L-297)
   - Statement-oriented pattern (L-307)
   - Translation validation approach (HELIX precedent)

5. **Fase 5: Integration + zero-sorry audit**
   - Tests de integración: ExpandedSigma → C/Rust via Pipeline.emit
   - Zero-sorry verification
   - Update ARCHITECTURE.md, BENCHMARKS.md

### Recursos prioritarios

| # | Recurso | Tipo | Para qué |
|---|---------|------|----------|
| 1 | **L-306** (Bridge predicate + injectivity) | Lección | Patrón fundamental del bridge predicate |
| 2 | **L-307** (Statement-oriented compile_correct) | Lección | Estructura del teorema principal |
| 3 | **DESIGN_SPEC.md § AMO-Lean Integration Strategy** | Doc proyecto | Sketch completo del bridge con código Lean |
| 4 | **HELIX Σ-HCOL papers** (Zaliva & Franchetti 2018, 2020) | Paper | Precedente formal exacto del bridge — Σ-HCOL ≅ ExpandedSigma |
| 5 | **Avigad et al.** (arXiv:2109.14534) | Paper | Verificación Lean sobre campos finitos — `norm_num` + tagged rewrites |
| 6 | **CompCert Clight Semantics** (Blazy, Leroy 2009) | Paper | Template para simulation methodology |
| 7 | **L-143** (evalSigmaAlg NO es monótona) | Lección | Anti-patrón crítico para `.temp` constructor |
| 8 | **Zhang et al.** (TPSA 2025) | Paper | Metodología semantics lifting para verificación por capas |
