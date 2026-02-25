# Insights: Trust-Lean v1.2.0 Verified CBackend

**Fecha**: 2026-02-21
**Dominio**: lean4
**Estado del objeto**: upgrade

## 1. Análisis del Objeto de Estudio

### Resumen

Trust-Lean v1.2.0 propone un upgrade industrial del CBackendEmitter existente (v1.0.0, 160 LOC) mediante: (1) sanitización higiénica de nombres C, (2) paréntesis agresivos para precedencia correcta, (3) llaves obligatorias en if/while/for, (4) soporte completo de store/load/array para bridge, (5) determinismo estricto, (6) headers autocontenidos, y (7) tail-recursive emission para programas grandes. El bridge v1.1.0 ya genera Stmt con store/load/while que el CBackend actual no soporta completamente.

### Keywords

C code generation, name sanitization, operator precedence, parenthesization, control flow emission, mandatory braces, memory operations store/load, deterministic output, tail recursion, C99 standards compliance, BackendEmitter typeclass, LowLevelExpr IR, pretty printing verified, hygienic naming, header generation

### Estado: upgrade

### Análisis del CBackend Actual

**Archivo**: `TrustLean/Backend/CBackend.lean` (160 LOC)

El CBackend maneja los 12 constructores de Stmt pero con gaps críticos:

| Gap | Descripción | Impacto |
|-----|-------------|---------|
| **store/load base no parentizado** | `exprToC base ++ "[" ++ ...` — si base es binOp, emite `a + b[idx]` en vez de `(a + b)[idx]` | C inválido |
| **Sin sanitización de nombres** | `varNameToStr` acepta cualquier String sin validar contra C keywords | Posible `int int = 5;` |
| **Sin paréntesis agresivos** | `exprToC` parentiza binOp/unaryOp pero no en todos los contextos | Precedencia incorrecta |
| **Sin propiedades formales** | Teoremas son triviales (rfl); no hay balanced braces, no hay correctness | Sin garantías |
| **Recursión no tail** | `stmtToC` recursiva, puede desbordar stack en programas >10K sentencias | Stack overflow |

### Dependencias

- Trust-Lean v1.1.0 completo (4825 LOC, 316 verified statements, 0 sorry)
- `BackendEmitter` typeclass (emitStmt, emitFunction, emitHeader)
- `Stmt` IR (12 constructores), `LowLevelExpr` (6 constructores), `VarName` (3 constructores)
- `Backend/Common.lean` (indentStr, varNameToStr, joinCode)

## 2. Lecciones Aplicables

### Lecciones reutilizables

**Arquitectura Backend**:
- **L-308**: Backend Emitter Architecture — BackendEmitter typeclass con emitStmt/emitFunction/emitHeader. Cada backend maneja 12 constructores. O(n+m) scaling.
- **L-310**: Pipeline Wiring via Generic Typeclasses — CodeGenerable + BackendEmitter + CodeGenSound = O(n+m) para n frontends × m backends.
- **L-309**: Rust vs C Idioms — Diferencias clave: indexing (usize cast), booleans, return, parámetros.
- **L-336**: Bridge-First Design — Probar isomorfismos PRIMERO, luego translation code.

**Correctness & Verification**:
- **L-297**: Three-part codegen contract: termination + result + frame property.
- **L-311**: Pipeline.sound como existencial triple.
- **L-312**: Zero sorry audit como gate final.
- **L-337**: Correctness composicional via helper lemmas.

**Determinismo & Naming**:
- **L-324**: Deterministic naming via constructor enum — elimina CodeGenState.
- **L-313**: Constructor-based VarName partitioning — disjointness gratis.

**simp & Proofs**:
- **L-283**: Store/load @[simp] lemmas esenciales para integración.
- **L-275**: Negative simp lemmas para Option-returning evaluators.
- **L-280**: Right-associative seq chains = correcto para assignmentsToStmt.

**Testing**:
- **L-119**: Test suite de casos borde dentro de formalización.
- **L-339**: Formal properties via rfl, no runtime tests.

### Anti-patrones a evitar

1. ❌ `simp [*]` genérico en correctness proofs → usar `simp only [explicit_set]`
2. ❌ Recursive typeclass self-reference → definir standalone def, luego instancia
3. ❌ Mezclar sintaxis/semántica en misma capa → separar evaluación de emisión
4. ❌ Left-associative seq chains → right-associate siempre
5. ❌ Diferir propiedades fundacionales → front-load injectivity/disjointness
6. ❌ Fuel como recurso consumido → fuel = depth bound only

## 3. Bibliografía Existente Relevante

### Documentos clave

| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| CompCert (Leroy et al., 2016) | verificacion/ | Arquitectura multi-fase, proof strategy para backends |
| Clight Semantics (Blazy-Leroy, 2009) | verificacion/ | Modelo memoria + semántica operacional C subset |
| Fiat Crypto Rewriting Engine (Gross et al., 2022) | verificacion/ | NbE + extraction pattern aplicable |
| CertiCoq Compositional (Paraskevopoulou-Appel, 2021) | verificacion/ | Pipeline Gallina→C verificado |
| HELIX DSP Codegen (Zaliva-Franchetti, 2018) | verificacion/ | DSL→Assembly verified pattern |
| Lean 4 System Description (de Moura-Ullrich, 2021) | verificacion/ | IR + code generator architecture |

### Gaps bibliográficos identificados

1. **Pretty printing verificada** — no hay papers sobre pretty printing formalmente verificada para C emission
2. **Sanitización C keywords en codegen** — sin referencia académica directa
3. **Determinismo de code generators** — gap abierto entre práctica y verificación formal
4. **Lean 4 → C verificado** — no existe compilador Lean→C verificado documentado

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Fuente | Resultado |
|------------|--------|-----------|
| Backends como pretty-printers fuera de TCB | LeanScribe, SuperTensor | CBackend trusted, correctness del Stmt upstream |
| Common backend layer (Common.lean) | LeanScribe | 30% reutilización, 0 inconsistencias |
| Fuel = depth bound, composition via max | Trust-Lean v1.0.0 | evalStmt_fuel_mono proven |
| Typeclass extensibility | Trust-Lean v1.0.0 | Nuevo backend = 1 instancia |
| Bridge lemmas como columna vertebral | LeanScribe, Trust-Lean v1.1.0 | Reduce proof LOC 50% |

### Decisiones arquitecturales aplicables

- **Value = Sum type (Int | Bool)**: elegido sobre type-indexed Expr. Mantener.
- **Fuel monotonicity restriction**: SOLO decrementar fuel en while/for, NO en assign/load/store.
- **Separar sintaxis de semántica**: `stmtToC : Stmt → String` es transformación sintáctica pura.

### Benchmarks de referencia

| Proyecto | LOC | Build Time | Teoremas | Sorry |
|----------|-----|-----------|----------|-------|
| LeanScribe v3.0.0 | 3,095 | 1.4s | 72 | 0 |
| Trust-Lean v1.0.0 | 2,917 | <3s | 179 | 0 |
| Trust-Lean v1.1.0 | 4,825 | <5s | 316 | 0 |
| **Target v1.2.0** | **~5,500** | **<6s** | **~350+** | **0** |

## 5. Nueva Bibliografía Encontrada

### Papers clave descubiertos

| Paper | URL | Relevancia para v1.2.0 |
|-------|-----|------------------------|
| **A Pretty Expressive Printer** (Li, Lasser, Crichton, 2023) | [arXiv:2310.01530](https://arxiv.org/abs/2310.01530) | **CRÍTICO**: Pretty printer con pruebas de correctitud **verificadas en Lean**. Referencia directa para emisión verificada. |
| **CakeML Verified Backend** (Tan et al., 2019) | [JFP 2019](https://cakeml.org/jfp19.pdf) | Modelo arquitectónico: 12 IRs + emission verificada a 5 arquitecturas. |
| **RustCompCert** (2025) | [arXiv:2602.07455](https://arxiv.org/abs/2602.07455) | Compilador Rust→ASM verificado via CompCert. Frontend verificado. |
| **Clight Semantics Updated** (Blazy-Leroy, FASE 2024) | [ACM DL](https://dl.acm.org/doi/10.1007/978-3-031-57259-3_1) | Versión moderna de Clight semantics. |
| **Hygienic Macro Expansion for Lean 4** (Ullrich-de Moura, 2020) | [arXiv:2001.10490](https://arxiv.org/abs/2001.10490) | Framework de scope tracking implementado en Lean 4. Base para sanitización. |
| **Formally Verified C from HCSP** (2024) | [arXiv:2402.15674](https://arxiv.org/abs/2402.15674) | Generación verificada de C con POSIX; prueba bisimulación. |
| **C to Safe Rust, Formalized** (Fromherz-Protzenko, 2024) | [arXiv:2412.15042](https://arxiv.org/abs/2412.15042) | Traducción C→Rust type-directed; aplicado a HACL*/EverParse. |
| **hax: Verifying Security-Critical Rust** (Bhargavan et al., 2025) | [IACR 2025/142](https://eprint.iacr.org/2025/142) | Code generation verificada con sanitización entre lenguajes. |
| **Lean 4 EmitC.lean** (leanprover) | [GitHub](https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/IR/EmitC.lean) | Referencia primaria: cómo Lean 4 emite C desde su IR. |

## 6. Insights de Nueva Bibliografía

**"A Pretty Expressive Printer" es la pieza clave faltante.** Es el único pretty printer con pruebas verificadas **en Lean** (no Coq). Su implementación PrettyExpressive podría servir como base para la emisión verificada del CBackendEmitter.

**CakeML Backend (2019) define el modelo arquitectónico.** 12 lenguajes intermedios y emisión verificada a 5 arquitecturas. Su estrategia de separar cada fase del backend en su propio compiler pass con prueba individual es directamente aplicable.

**La sanitización higiénica tiene fundamento teórico (Ullrich-de Moura 2020) pero no implementación para C keywords.** El framework de scope tracking existe en Lean 4, pero la sanitización específica de C99 keywords es ingeniería nueva.

**Lean 4 EmitC.lean** es la referencia de implementación más directa: muestra cómo Lean 4 mismo emite C desde su IR, incluyendo manejo de closures, reference counting, y calling conventions.

## 7. Síntesis de Insights

### Hallazgos clave

1. **El CBackend actual tiene un bug real en store/load**: `exprToC base ++ "["` no parentiza `base`, produciendo C inválido cuando base es una expresión compuesta. Fix obligatorio.

2. **"A Pretty Expressive Printer" (Lean, 2023) es referencia directa** para pretty printing verificada en Lean. Evaluar si se puede usar como dependencia o como patrón de diseño.

3. **El backend NO necesita estar en el TCB**: La correctness del Stmt viene del bridge (v1.1.0). El CBackend es trusted code que genera strings. Las propiedades verificables son estructurales (balanced braces, valid identifiers, determinismo), no semánticas.

4. **Sanitización = tabla finita de C keywords + prefijo `_tl_`**: No es un problema de investigación — es una tabla de 37 C99 keywords + 8 stdint.h types + ~10 stdlib names. Implementación directa con `HashSet String`.

5. **Paréntesis agresivos = fully-parenthesized output**: La estrategia más simple y correcta es parentizar TODA sub-expresión binaria: `((a) + (b))`. Sin ambigüedad, sin tabla de precedencia, sin bugs. El overhead de paréntesis redundantes es aceptable para código generado.

6. **Determinismo es gratis**: `stmtToC` es una función pura Lean sin IO, sin HashMap, sin state mutable. Es determinista por construcción. Basta con un `example` que lo demuestre.

7. **Tail recursion**: Para programas con >10K sentencias anidadas en .seq, refactorizar a acumulador. Pero evaluar si esto es un riesgo real con los programas que genera amo-lean.

8. **El RustBackend (159 LOC) tiene los mismos gaps** que el CBackend. Considerar upgrade conjunto o secuencial.

9. **v1.0.0 tests de regresión**: Los `Pipeline.emit` tests en Integration.lean y BridgeIntegration.lean cubren ArithExpr + BoolExpr. Deben seguir pasando.

10. **Scope del upgrade es acotado**: ~200-300 LOC nuevas (refactor CBackend + Common + tests), no una reescritura. El typeclass `BackendEmitter` no cambia.

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|-------------|---------|------------|
| Over-engineering del sanitizer | Alta | Medio | Tabla finita, no framework genérico |
| Regresión en Pipeline.emit | Media | Alto | Tests de regresión existentes |
| Stack overflow en seq profundo | Baja | Alto | Evaluar si amo-lean genera >10K seq |
| Paréntesis redundantes afectan legibilidad | Baja | Bajo | Código generado, no escrito por humanos |
| RustBackend queda inconsistente | Media | Medio | Upgrade secuencial C→Rust |

### Recomendaciones para planificación

1. **Scope v1.2.0 = CBackend upgrade only** (no Rust). Rust puede ser v1.3.0.
2. **Fase 1**: Refactorizar `Common.lean` con sanitización + parentización
3. **Fase 2**: Upgrade `CBackend.lean` usando nuevos helpers
4. **Fase 3**: Propiedades formales (balanced braces, valid identifiers, determinismo)
5. **Fase 4**: Integration tests (Pipeline.emit con bridge programs → gcc -Wall -Werror)
6. **Target**: ~5,500 LOC total, ~350+ theorems, 0 sorry, <6s build

### Recursos prioritarios

1. **L-308**: Backend Emitter Architecture — blueprint directo
2. **L-283**: Store/load @[simp] lemmas — esenciales para integration
3. **L-324**: Deterministic naming — patrón ya probado
4. **"A Pretty Expressive Printer"** (arXiv:2310.01530) — pretty printing verificada en Lean
5. **Lean 4 EmitC.lean** (GitHub) — referencia de implementación C emission
