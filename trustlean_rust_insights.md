# Insights: Trust-Lean v3.2 — Verified Rust Backend

**Fecha**: 2026-03-27
**Dominio**: lean4
**Estado del objeto**: upgrade (RustBackend.lean existe con 166 LOC, 3 theorems; falta RustBackendProperties)

## 1. Analisis del Objeto de Estudio

### Resumen

Trust-Lean v3.2 busca llevar el RustBackend al nivel del CBackend Industrial (v1.2.0): propiedades formales verificadas sobre el codigo emitido. El RustBackend actual (166 LOC, 3 simp lemmas triviales) emite Rust sintacticamente correcto pero **carece de 31+ propiedades formales** que el CBackend tiene (sanitizacion, balanced braces, determinismo, parentizacion). La ruta es replicar CBackendProperties.lean adaptando a Rust.

### Estado actual del RustBackend

| Metrica | RustBackend | CBackend | Gap |
|---------|------------|---------|-----|
| LOC | 166 | ~350 | -184 |
| Theorems | 3 (simp triviales) | 34 | -31 |
| Sanitizacion | NO | SI (tabla finita + prefix) | CRITICO |
| Balanced braces | NO verificado | 10 theorems + 8 examples | CRITICO |
| Expression props | 0 | 4 theorems | ALTO |
| Determinism | 0 (pero rfl by construction) | 2 theorems | MEDIO |
| Header props | 0 | 1 theorem | MEDIO |
| For desugaring | 0 | 1 theorem | MEDIO |

### Definiciones existentes en RustBackend.lean

1. **RustConfig** — `useMut : Bool`, `includePowerHelper : Bool`
2. **RustConfig.intType** — `"i64"`
3. **binOpToRust** — 12 BinOps cubiertos (+, -, *, ==, <, &&, ||, &, |, ^, <<, >>)
4. **unaryOpToRust** — 4 UnaryOps (-, !, as i64, as i32)
5. **exprToRust** — 6 LowLevelExpr constructores (fully parenthesized)
6. **stmtToRust** — 12 Stmt constructores (if/while sin parens = Rust idiomatico)
7. **buildRustParamList** — `"x: i64, y: i64"` (type-after-name)
8. **generateRustFunction** — `fn name(params) -> i64 { body }`
9. **generateRustHeader** — power helper con binary exponentiation
10. **BackendEmitter instance** — delega a stmtToRust/generateRustFunction/generateRustHeader

### Theorems existentes (3, todos @[simp])

- `stmtToRust_skip` — `stmtToRust level .skip = ""`
- `stmtToRust_break` — `stmtToRust level .break_ = indentStr level ++ "break;"`
- `stmtToRust_continue` — `stmtToRust level .continue_ = indentStr level ++ "continue;"`

### Keywords

verified codegen, Rust syntax, balanced braces, sanitization, determinism, expression parenthesization, array indexing usize, unary/binary operator coverage, statement desugaring, backend emitter typeclass, indentation structure, function signature generation, wrapping arithmetic, cast syntax, keyword table

### Gaps principales

1. **Sanitizacion de identificadores** — Sin proteccion contra 58 Rust keywords
2. **Balanced braces formales** — Sin theorems sobre `countChar '{' = countChar '}'`
3. **Expression emission properties** — Sin theorems sobre litInt/litBool encoding
4. **Wrapping arithmetic** — No emite `.wrapping_add()` etc. (Rust panic en overflow)
5. **Cast syntax** — Usa `(as i32)` prefix pero Rust es `x as i32` postfix
6. **Shift >= width** — Rust panic (a diferencia de C UB); necesita masking explicito

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Titulo | Resumen | Categoria |
|----|--------|---------|-----------|
| L-308 | Backend Emitter Architecture | Pretty-printers fuera del TCB con config + typeclass. Cada backend cubre 12 Stmt constructores. | ARQUITECTURA |
| L-309 | Rust Code Generation Idioms vs C | Diferencias: usize cast, bool literals, control flow sin parens, returns como expresion. Formalizar. | CODEGEN |
| L-310 | Pipeline Wiring via Typeclasses | CodeGenerable + BackendEmitter + CodeGenSound = escalabilidad O(n+m). Backend independiente. | ARQUITECTURA |
| L-297 | Three-part codegen contract | (1) terminacion, (2) result correctness, (3) frame preservation. Composable. | ESPECIFICACION |
| L-339 | Formal Properties via rfl | Propiedades by-construction: rfl zero-cost, compile-time, generaliza automaticamente. | TECNICA |
| L-343 | sanitizeIdentifier theorem gap | Funcion chequea cReservedIdentifiers pero theorem solo cubre c99Keywords. Fortalecer. | MEJORA |
| L-616 | sanitizeIdentifier non-injectivity | Sanitizers con prefijos crean colisiones inherentes. Documentar como precondicion. | ANALISIS |
| L-614 | Full string equality is false target | No buscar print_Rust(x) = print_C(x). Probar operator-level compatibility + oracle #eval. | PATRON |
| L-351 | Example-based verification insufficient | Ejemplos decide NO son prueba formal. Usar induccion estructural. | ANTI-PATRON |
| L-356 | Zero sorry audit | 0 sorry/axiom/admit en todo el proyecto. Cadena de correccion completa. | CONTROL |
| L-418 | Concrete defs beat typeclasses for single-instance | def concreto + theorems standalone > typeclass para unica instancia. | PATRON |
| L-296 | Explicit instance names | `[inst : TypeClass a]` + `inst.methodName` evita ambiguedad de proyeccion. | SOLUCION |

### Anti-patrones a evitar

1. **L-351**: Confiar en 8 ejemplos `decide` como prueba formal de balanced braces → usar induccion estructural
2. **L-614**: Buscar igualdad string exacta entre backends → probar operator-level compatibility
3. **L-343**: Theorem de sanitizacion que solo cubre subconjunto de keywords → cubrir tabla completa
4. **Mezclar sintaxis/semantica**: RustBackend NO debe probar comportamiento semantico (es responsabilidad del Bridge)
5. **`simp [*]` generico**: Usar `simp only [explicit_set]` para proofs deterministas

### Top 5 lecciones criticas

1. **L-309** (Rust vs C idioms) — Cada diferencia semantica debe ser un theorem, no documentacion
2. **L-308** (Backend architecture) — Replicar patron: emitter = pretty-printer fuera del TCB
3. **L-310** (Typeclass pipeline) — Backend es standalone, composable via Pipeline.sound
4. **L-351 + L-339** (Formal props, not examples) — Induccion estructural + rfl, no decide
5. **L-614** (Operator compatibility) — Probar binOp/unaryOp correctness, no string matching

## 3. Bibliografia Existente Relevante

### Documentos clave

| Documento | Carpeta | Relevancia |
|-----------|---------|-----------|
| CompCert Framework | verificacion/ | Referencia para preservacion semantica en compilacion |
| Fiat-Crypto machine-word arithmetic | verificacion/ | Aritmetica de palabras de maquina verificada |
| Mechanized semantics for Clight | verificacion/ | Semantica mecanizada para verificacion de compiladores |
| HELIX verified translation DSL | verificacion/ | Traduccion DSL funcional→imperativo verificada |
| Verified peephole rewriting in Lean 4 | verificacion/ | Rewrite rules verificadas en Lean 4 |
| egg equality saturation | optimizacion/ | Optimizacion via e-graphs (futuro: optimization passes) |

### Gaps bibliograficos

1. **CRITICO**: Semantica formal de Rust (ownership, borrowing, lifetimes) — no hay en biblioteca
2. **CRITICO**: Code emission verification especifica para Rust — no hay
3. **IMPORTANTE**: Lean ↔ Rust FFI y extraccion — no hay
4. **IMPORTANTE**: Verificacion incremental/modular de backends — no hay
5. **MEDIO**: Cost models para codigo Rust generado — no hay

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras del CBackend (a replicar)

| Estrategia | Resultado | Aplicacion a Rust |
|-----------|----------|------------------|
| Backend como pretty-printer fuera del TCB | Correctness = upstream Bridge | Identico patron |
| Sanitizacion = tabla finita | 0 keyword collisions | Extender: 58 Rust keywords |
| Parentesis agresivos (fully-parenthesized) | Determinismo + no ambiguedad | Identico en Rust |
| Determinismo gratis (funcion pura) | rfl proofs triviales | stmtToRust ya es puro |
| Extension-only architecture | Zero refactoring, cero regresion | Solo agregar RustBackendProperties |
| Common.lean = 30% reutilizacion | Build time <6s, 0 inconsistencias | Ya reutiliza 100% |
| Bridge lemmas como columna vertebral | Reduce proof LOC 50% | rustBridge patron analogo |

### Decisiones heredables sin cambios

- `Value = Int | Bool` sum type
- Backend ≠ TCB (correctness upstream)
- `Stmt` IR 12 constructores (shared)
- Fuel = depth bound only
- `BackendEmitter` typeclass (instancia ya existe)

### Benchmarks de referencia (CBackend como target)

| Propiedad | CBackend Count | Target Rust |
|-----------|---------------|-------------|
| Sanitizacion keywords | 3 | 3+ (tabla Rust) |
| Identificadores validos | 2 | 2+ (Rust rules) |
| Parentizacion completa | 1 | 1 |
| Braces balanceados | 12 (per-constructor) | 12 |
| Determinismo | 2 | 2 |
| Header generation | 1 | 1 |
| For desugaring | 1 | 1 |
| Control flow braces | 2 | 2 |
| countChar infrastructure | 3 | 3 (reutilizar) |
| **Total** | **34** | **34+ (target: 40)** |

### Errores evitados (bugs del CBackend v1.0.0)

1. **Store/load precedencia**: `a + b[i]` vs `(a+b)[i]` — FIX: parentizar recursivo
2. **Identifiers sin sanitizar**: `int int = 5;` — FIX: tabla finita + prefijo
3. **Sin propiedades formales**: 0 garantias estructurales — FIX: 34 theorems

## 5. Nueva Bibliografia Encontrada

### Papers sobre verificacion formal de Rust

| Paper | Ano | Relevancia | Hallazgo clave |
|-------|-----|-----------|----------------|
| **RustBelt** (POPL 2018) | 2018 | ALTA | Formaliza ownership/borrowing en Iris/Coq. Ownership predicate + sharing predicate. Para v3.2 (solo owned values), simplifica a solo ownership predicate. |
| **Oxide: The Essence of Rust** | 2019 | MEDIA | Primera prueba sintatica de type safety para borrow checking. Lifetimes como sets de locations. |
| **Aeneas: Rust → Lean** (ICFP 2022) | 2022 | ALTA | Traduce Rust a Lean funcional puro. Microsoft lo usa para SymCrypt. Valida que borrow-checked Rust tiene semantica puramente funcional — alinea con enfoque Trust-Lean. |
| **RefinedRust** (MPI-SWS) | 2023 | ALTA | Refinement types sobre ownership. Verified Vec con unsafe. Trust-Lean podria emitir codigo compatible con RefinedRust annotations. |
| **Verus** (SOSP 2024) | 2024 | ALTA | Verificacion de Rust con specs en Rust. 2 best papers OSDI. AutoVerus (ICLR 2025) logra 91.3% auto-proof. Path mas practico para dual verification. |
| **Creusot** | 2022 | MEDIA | Rust → Why3 MLCFG. Specification language Pearlite. Alternativa a Verus para verificar output. |
| **coq-of-rust** | 2024 | MEDIA | Rust → Coq via THIR. Verificando Revm (Ethereum VM). |
| **Ferrocene** | 2024 | MEDIA | Compilador Rust calificado ISO 26262 ASIL D. Si Trust-Lean emite Rust compilado por Ferrocene → cadena high-assurance. |
| **Rust ownership at memory level** (FMSD 2024) | 2024 | MEDIA | Tratamiento formal reciente de ownership a nivel de memoria. |
| **Lessons from verifying Rust stdlib** | 2025 | MEDIA | Lecciones practicas sobre que funciona/falla al verificar Rust real a escala. |

### Tecnicas clave de la literatura

1. **Purely functional representation of borrows (Aeneas)**: Codigo que pasa borrow check = funciones puras. Trust-Lean ya genera desde IR puro → Rust emitido satisface ownership naturalmente si solo usa owned values.
2. **Ownership predicate simplification (RustBelt)**: Sin `&`/`&mut` en output → solo ownership predicate, no sharing predicate. Simplifica formalizacion significativamente.
3. **Wrapping arithmetic explicito (Rust idiom)**: `.wrapping_add()` / `Wrapping<T>` — obligatorio para evitar panic en debug mode. Diferencia critica vs C.
4. **Verus-compatible annotations**: Emitir `requires`/`ensures` junto al Rust para dual verification independiente.
5. **`r#` prefix para keyword escape**: Rust permite `r#type`, `r#match` como identifiers. Alternativa a `_tl_` prefix.

### Rust keywords completa (58 total)

**Strict (39)**: as, async, await, break, const, continue, crate, dyn, else, enum, extern, false, fn, for, if, impl, in, let, loop, match, mod, move, mut, pub, ref, return, self, Self, static, struct, super, trait, true, type, unsafe, use, where, while

**Reserved (14)**: abstract, become, box, do, final, gen, macro, override, priv, try, typeof, unsized, virtual, yield

**Weak (5)**: union, macro_rules, raw, safe, 'static

### Rust vs C: Diferencias criticas para emision de codigo

| Feature | C99 (CBackend) | Rust (RustBackend) | Impacto |
|---------|----------------|-------------------|---------|
| Function decl | `int64_t f(int64_t x)` | `fn f(x: i64) -> i64` | Reescribir generateRustFunction |
| Variable decl | `int64_t x = 0;` | `let mut x: i64 = 0;` | `let mut` + type-after-colon |
| Integer types | `int32_t`, `uint32_t` | `i32`, `u32` | Sustitucion simple |
| Casting | `(int32_t)x` | `x as i32` | Postfix `as` vs prefix C-style |
| Overflow signed | UB | Panic debug / wrap release | Emitir `.wrapping_add()` |
| Overflow unsigned | Defined mod 2^N | Panic debug / wrap release | Emitir `.wrapping_add()` tambien! |
| Shift >= width | UB | Panic | Masking explicito en emision |
| If/while | `if (cond)` | `if cond` (sin parens) | Ya implementado en stmtToRust |
| Array index | `arr[i]` | `arr[i as usize]` | Cast a usize requerido |
| Headers | `#include <stdint.h>` | (nada para primitivos) | Simplifica header |
| Keywords | 37 | 58 | Tabla de sanitizacion expandida |
| Sanitization | `_tl_` prefix | `r#` prefix o `_tl_` | Decision de diseno |

## 6. Insights de Nueva Bibliografia

### Hallazgo clave: Trust-Lean v3.2 puede ser conservador

La literatura muestra que la verificacion formal de Rust es un campo activo y complejo (RustBelt, Oxide, RefinedRust requieren separation logic avanzada). Sin embargo, **Trust-Lean v3.2 NO necesita formalizar ownership/borrowing** porque:

1. El Stmt IR de Trust-Lean es un lenguaje imperativo simple sin referencias/punteros
2. El Rust emitido usa solo owned values (`let mut x: i64 = ...`)
3. No hay `&`, `&mut`, lifetimes, ni traits en el output
4. Esto coloca a Trust-Lean en el subset "ownership-trivial" de Rust

**Implicacion**: Las propiedades a verificar son **sintaticas** (balanced braces, sanitizacion, parentizacion, determinismo) — identicas en estructura a las del CBackend. La formalizacion de ownership es un non-goal para v3.2.

### Oportunidad: Wrapping arithmetic como diferenciador

C tiene overflow definido para unsigned y UB para signed. Rust tiene **panic** para ambos en debug mode. Trust-Lean v3.2 debe:
- Emitir `.wrapping_add()`, `.wrapping_sub()`, `.wrapping_mul()` para aritmetica
- O usar `Wrapping<i64>` / `Wrapping<u32>` como tipo
- Probar que la emision con wrapping preserva semantica de wrapInt64/wrapUInt32

Esto es un **theorem nuevo** sin analogo en CBackend: `stmtToRust_wrapping_preserves_semantics`.

## 7. Sintesis de Insights

### Hallazgos clave (Top 10)

1. **RustBackend es funcional pero formalmente vacio** — 3 simp triviales vs 34 theorems del CBackend. Gap principal = propiedades formales, no funcionalidad.

2. **Extension-only: zero regression risk** — v3.2 solo agrega `RustBackendProperties.lean` + modifica `RustBackend.lean`. Ningun archivo C/MicroC se toca.

3. **Keyword sanitization es CRITICO** — 58 Rust keywords (vs 37 C99). Decision de diseno: `r#` prefix (Rust idiomatico) vs `_tl_` prefix (consistente con C). Recomendacion: `_tl_` por consistencia cross-backend.

4. **Wrapping arithmetic es DIFERENCIADOR** — Rust panic en overflow (signed Y unsigned). Necesita `.wrapping_*()` en output. Theorem nuevo sin analogo en C.

5. **Cast syntax cambia: postfix vs prefix** — `x as i32` vs `(int32_t)x`. Ya implementado en stmtToRust pero sin property theorem.

6. **Ownership es non-goal** — Literature (RustBelt, Oxide) muestra que ownership formalization es compleja. Trust-Lean emite solo owned values → ownership-trivial subset. No necesita formalizar.

7. **CBackendProperties es template exacto** — 27 de 34 theorems se copian/adaptan directamente. Solo cambia: keyword table, bool literals, type names.

8. **Aeneas valida el enfoque** — Demuestra que Rust borrow-checked = pure functional. Trust-Lean emite desde IR puro → output es trivialmente ownership-correct.

9. **Verus como dual verification** — Oportunidad futura: emitir annotations Verus para verificacion independiente del output Rust.

10. **~430 LOC de esfuerzo** — Estimacion conservadora: RustBackendProperties (~200), Common.lean extension (~30), wrapping arithmetic (~100), integration tests (~100).

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigacion |
|--------|-------------|---------|-----------|
| Wrapping arithmetic complica proofs | MEDIA | ALTO | Definir `wrappingBinOpToRust` separado con theorems modulares |
| Shift >= width panic en Rust | BAJA | MEDIO | Trust-Lean ya reduce mod 64; documentar como safe |
| sanitizeIdentifier non-injectivity (L-616) | BAJA | BAJO | Documentar como precondicion; linter opcional |
| `r#` vs `_tl_` decision delay | BAJA | BAJO | Elegir `_tl_` por consistencia, decidir una vez |
| Proof burden de balanced braces para 12 constructores | MEDIA | MEDIO | Copiar estructura CBackendProperties; proofs son analogos |

### Recomendaciones para planificacion

1. **Fase 1 (FUND)**: Sanitizacion Rust — `rustKeywords` tabla + `sanitizeIdentifierRust` + 3 theorems
2. **Fase 2 (CRIT)**: Wrapping arithmetic — `wrappingBinOpToRust` + emission + preservation theorem
3. **Fase 3 (CRIT)**: RustBackendProperties — copiar 27 CBackend theorems + adaptar + 6 Rust-specific
4. **Fase 4 (PAR)**: Integration tests — replicar CBackendIntegration para Rust + smoke tests
5. **Fase 5 (HOJA)**: Audit — zero sorry + spec_audit + wiring_check + tag v3.2.0

### Recursos prioritarios

1. **CBackendProperties.lean** — Template exacto a replicar (34 theorems, 188 LOC)
2. **L-309** (Rust idioms vs C) — Cada diferencia = theorem
3. **L-308** (Backend architecture) — Patron emitter fuera del TCB
4. **Aeneas paper** — Valida owned-values-only approach
5. **Rust Keywords Reference** — doc.rust-lang.org/reference/keywords.html

## 8. Teoremas Extraidos

Seccion omitida (los teoremas de v3.2 son propiedades estructurales sobre emision de codigo, no teoremas matematicos de papers). Se formalizaran durante la implementacion siguiendo el template de CBackendProperties.

### Catalogo de propiedades target (40 theorems)

#### A. Infrastructure (3, reutilizar de Common)
- `countChar_empty`, `countChar_append`, filter helper

#### B. Sanitization (4 nuevos)
- `sanitizeIdentifierRust_not_keyword` — output ∉ rustKeywords
- `sanitizeIdentifierRust_nonempty` — output.toList ≠ []
- `sanitizeIdentifierRust_valid` — isValidRustIdent output = true
- `sanitizeIdentifierRust_idempotent` — f(f(x)) = f(x)

#### C. Determinism (2, rfl)
- `stmtToRust_deterministic` — `stmtToRust l s = stmtToRust l s`
- `exprToRust_deterministic` — `exprToRust e = exprToRust e`

#### D. Expression emission (4)
- `exprToRust_litInt_nonneg` — `n >= 0 → exprToRust(.litInt n) = toString n`
- `exprToRust_litInt_neg` — `n < 0 → exprToRust(.litInt n) = "(" ++ toString n ++ ")"`
- `exprToRust_litBool_true` — `exprToRust(.litBool true) = "true"` (vs C: "1")
- `exprToRust_litBool_false` — `exprToRust(.litBool false) = "false"` (vs C: "0")

#### E. Balanced braces structural (5 simp)
- `stmtBracePairsRust_skip` — 0
- `stmtBracePairsRust_break` — 0
- `stmtBracePairsRust_seq` — pairs s1 + pairs s2
- `stmtBracePairsRust_ite` — 2 + pairs t + pairs e
- `stmtBracePairsRust_while` — 1 + pairs b

#### F. Balanced braces examples (8, by decide)
- skip, break, continue, return, ite, while, for, nested

#### G. Control flow braces (2)
- `stmtToRust_ite_has_open_brace` — countChar '{' >= 2
- `stmtToRust_while_has_open_brace` — countChar '{' >= 1

#### H. For desugaring (1)
- `stmtToRust_for_eq_desugar`

#### I. Header generation (1)
- `generateRustHeader_no_helper`

#### J. Rust-specific (6 nuevos)
- `exprToRust_cast_postfix` — cast usa `as` postfix
- `stmtToRust_if_no_parens` — if sin parentesis alrededor de condicion
- `stmtToRust_while_no_parens` — while sin parentesis
- `stmtToRust_let_mut_decl` — variables usan `let mut`
- `binOpToRust_wrapping_safe` — emision con wrapping si configurado
- `stmtToRust_array_usize_cast` — array index con `as usize`

#### K. Simp lemmas (4, existentes + extender)
- `stmtToRust_skip`, `stmtToRust_break`, `stmtToRust_continue`, `stmtToRust_return_none`

**Total: ~40 theorems** (34 analogos al CBackend + 6 Rust-specific)

## 9. Formalizacion Lean 4

Seccion omitida (la formalizacion se ejecutara durante la implementacion con /plan-project).

## 10. Libreria Generada

Seccion omitida (los theorems se agregan directamente a Trust-Lean/Backend/RustBackendProperties.lean).
