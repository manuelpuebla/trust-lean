# TL_expansion: Add `LowLevelExpr.addrOf` to TrustLean

**Fecha**: 2026-04-08
**Solicitado por**: Proyecto TRZK v3.7.0 (Verified SIMD Codegen)
**Prioridad**: BLOCKER para TRZK nodo N37.4

---

## 1. Contexto: Por qué se necesita esta expansión

### El problema

El proyecto TRZK v3.7.0 rutea butterflies NEON a través de `TrustLean.Stmt.call` para
obtener verificación estructural. El helper `neon_deinterleave_load` tiene esta firma C:

```c
static inline void neon_deinterleave_load(int32x4_t* a, int32x4_t* b, const int32_t* ptr)
```

Los primeros dos parámetros son **punteros de salida**. La llamada correcta en C es:

```c
neon_deinterleave_load(&aVec, &bVec, ptr);  // & = address-of
```

Pero `LowLevelExpr` no tiene constructor `addrOf`. El emisor `exprToC` para `.varRef v`
produce solo `"aVec"`, no `"&aVec"`. El character `&` no es un `isValidCIdentChar`
(Common.lean:74-75), así que no puede codificarse en el nombre de variable.

**Resultado**: Sin `addrOf`, es IMPOSIBLE emitir `&var` en C generado desde Stmt.call.
TRZK N37.4 (reescribir butterflies como Stmt) queda bloqueado.

### Por qué esta solución (no otras)

Se evaluaron alternativas:

| Opción | Veredicto | Razón |
|--------|-----------|-------|
| Special-case en `simdStmtToC` por fname | Rechazada | Frágil: lógica dependiente de strings de funciones |
| Modelar como `UnaryOp` | Rechazada | `UnaryOp` opera sobre `Value`, no sobre estructura; `addrOf` necesita analizar la expresión, no su valor |
| Extender `Stmt` con constructor SIMD | Rechazada | 325 pattern matches + proofs por inducción rotas |
| **Extender `LowLevelExpr` con `.addrOf`** | **Elegida** | 6 archivos, ~7 LOC, 0 proofs rotas |

### Impacto real (verificado)

**Hallazgo clave**: `MicroCExpr` (MicroC/AST.lean:57-64) es un tipo SEPARADO de
`LowLevelExpr`. Las funciones de eval/prettyprint/roundtrip en MicroC/ y MicroRust/
hacen pattern match sobre `MicroCExpr`, NO sobre `LowLevelExpr`. Por lo tanto, NO
necesitan cambios.

`getArrayName` (Core/Eval.lean:33-36) usa wildcard (`| _ => none`). No se rompe.

No existen proofs por inducción estructural sobre `LowLevelExpr` (las inducciones
son sobre `ScalarExpr`, `WFExpr`, `IdxExpr` — tipos fuente que se traducen a
`LowLevelExpr` vía homomorfismos).

| Métrica | Valor |
|---|---|
| Archivos a modificar | **6** |
| Líneas de código nuevo | **~7** |
| Proofs que se rompen | **0** |
| Tests que se rompen | **0** (deriving Repr, Inhabited auto-derivan) |

---

## 2. Infraestructura involucrada

### 2.1 Tipo a modificar: `LowLevelExpr`

**Archivo**: `TrustLean/Core/Value.lean`
**Líneas**: 211-218

```lean
inductive LowLevelExpr where    -- línea 211
  | litInt   : Int → LowLevelExpr         -- línea 212
  | litBool  : Bool → LowLevelExpr        -- línea 213
  | varRef   : VarName → LowLevelExpr     -- línea 214
  | binOp    : BinOp → LowLevelExpr → LowLevelExpr → LowLevelExpr  -- línea 215
  | unaryOp  : UnaryOp → LowLevelExpr → LowLevelExpr               -- línea 216
  | powCall  : LowLevelExpr → Nat → LowLevelExpr                   -- línea 217
  deriving Repr, Inhabited       -- línea 218
```

`VarName` (Value.lean:201-205) ya tiene `deriving Repr, BEq, DecidableEq, Inhabited`.
Agregar `addrOf : VarName → LowLevelExpr` no rompe auto-deriving.

### 2.2 Evaluador semántico: `evalExpr`

**Archivo**: `TrustLean/Core/Eval.lean`
**Líneas**: 43-58

```lean
def evalExpr (env : LowLevelEnv) : LowLevelExpr → Option Value
  | .litInt n => some (.int n)                     -- línea 44
  | .litBool b => some (.bool b)                   -- línea 45
  | .varRef name => some (env name)                -- línea 46
  | .binOp op e1 e2 => ...                         -- líneas 47-50
  | .unaryOp op e => ...                            -- líneas 51-54
  | .powCall base n => ...                          -- líneas 55-58
```

`addrOf` NO tiene semántica de evaluación (es un concepto de codegen, no de
cómputo). Al igual que `.call` en `evalStmt` retorna `none` (Eval.lean:126),
`evalExpr (.addrOf _)` debe retornar `none`.

### 2.3 Backend C: `exprToC`

**Archivo**: `TrustLean/Backend/CBackend.lean`
**Líneas**: 71-79

```lean
def exprToC : LowLevelExpr → String
  | .litInt n => if n < 0 then s!"({n})" else s!"{n}"   -- línea 72
  | .litBool true => "1"                                  -- línea 73
  | .litBool false => "0"                                 -- línea 74
  | .varRef v => varNameToC v                             -- línea 75
  | .binOp op lhs rhs => ...                              -- líneas 76-77
  | .unaryOp op e => ...                                  -- línea 78
  | .powCall base n => ...                                -- línea 79
```

Este es el caso PRINCIPAL. `addrOf v` debe emitir `"&" ++ varNameToC v`.

Nota: `varNameToC` (CBackend.lean:62-64) aplica `sanitizeIdentifier` para `.user s`.
Para `.addrOf (.user "nv0")`, la emisión sería `"&nv0"` (correcto en C).

### 2.4 Backend Rust: `exprToRust`

**Archivo**: `TrustLean/Backend/RustBackend.lean`
**Líneas**: 61-69

Mismo patrón que C. Para Rust, address-of es `&var` (misma sintaxis).

### 2.5 Traducción MicroC: `exprToMicroC`

**Archivo**: `TrustLean/MicroC/Translation.lean`
**Líneas**: 28-34

```lean
def exprToMicroC : LowLevelExpr → MicroCExpr
  | .litInt n => .litInt n                            -- línea 29
  | .litBool b => .litBool b                          -- línea 30
  | .varRef v => .varRef (varNameToC v)               -- línea 31
  | .binOp op e1 e2 => ...                            -- línea 32
  | .unaryOp op e => ...                              -- línea 33
  | .powCall base n => ...                             -- línea 34
```

`MicroCExpr` (MicroC/AST.lean:57-64) es un tipo SEPARADO con 7 constructores propios.
NO extender `MicroCExpr`. Mapear `addrOf` a: `.varRef ("&" ++ varNameToC v)`.

Justificación: El código SIMD fluye por `simdStmtToC` → `exprToC`, NUNCA por
`stmtToMicroC` → `exprToMicroC`. Si un Stmt.call con argumento addrOf pasara por
el path MicroC, `evalStmt(.call)` retorna `none` sin evaluar argumentos. La
representación `.varRef("&nv0")` es semánticamente imprecisa para eval pero correcta
para string emission, y nunca se evalúa en la práctica.

### 2.6 Traducción MicroRust: `exprToMicroRust`

**Archivo**: `TrustLean/MicroRust/Translation.lean`
**Líneas**: 21-27

Mismo patrón que MicroC. Mapear a `.varRef ("&" ++ varNameToRust v)`.

---

## 3. Archivos que NO necesitan cambios (y por qué)

Estos archivos hacen pattern match sobre `MicroCExpr` o `MicroRustExpr`, NO sobre
`LowLevelExpr`. Como NO extendemos esos tipos, estos archivos quedan intactos:

| Archivo | Función | Tipo que matchea |
|---------|---------|-----------------|
| MicroC/Eval.lean:37 | `evalMicroCExpr` | `MicroCExpr` |
| MicroC/Int64Eval.lean:107 | `evalMicroCExpr_int64` | `MicroCExpr` |
| MicroC/UInt128Eval.lean:94 | `evalMicroCExpr_uint128` | `MicroCExpr` |
| MicroC/UnsignedEval.lean:116 | `evalMicroCExpr_uint32` | `MicroCExpr` |
| MicroC/UnsignedEval.lean:141 | `evalMicroCExpr_uint64` | `MicroCExpr` |
| MicroC/AST.lean:195 | `MicroCExpr.size` | `MicroCExpr` |
| MicroC/PrettyPrint.lean:80 | `microCExprToString` | `MicroCExpr` |
| MicroC/RoundtripExpr.lean:26 | `exprDepth` | `MicroCExpr` |
| MicroC/RoundtripExpr.lean:38 | `NegLitDisam` | `MicroCExpr` |
| MicroRust/PrettyPrint.lean:77 | `microRustExprToString` | `MicroRustExpr` |
| MicroRust/RoundtripExpr.lean:28 | `rustExprDepth` | `MicroRustExpr` |
| MicroRust/RoundtripExpr.lean:40 | `NegLitDisamRust` | `MicroRustExpr` |
| MicroC/UInt128FuelMono.lean | Fuel lemmas | `MicroCStmt` |

Adicionalmente, estas funciones matchean `LowLevelExpr` pero con wildcard:

| Archivo | Función | Por qué no se rompe |
|---------|---------|-------------------|
| Core/Eval.lean:33 | `getArrayName` | Usa `\| _ => none` (wildcard) |
| MicroC/Simulation.lean:42 | `WellFormedBase` | Solo matchea `.varRef (.user _)` |
| MicroRust/Simulation.lean:42 | `WellFormedBaseRust` | Solo matchea `.varRef (.user _)` |

---

## 4. Tareas (en orden)

### Tarea 1: Agregar constructor a `LowLevelExpr`

**Archivo**: `TrustLean/Core/Value.lean`
**Línea**: Insertar después de línea 217 (antes de `deriving`)

```lean
  | addrOf   : VarName → LowLevelExpr               -- address-of for C/Rust & emission
```

**Verificación**: `lake build TrustLean.Core.Value` debe pasar. Auto-deriving de
`Repr` e `Inhabited` se mantiene porque `VarName` ya tiene ambas instancias.

### Tarea 2: Agregar caso en `evalExpr`

**Archivo**: `TrustLean/Core/Eval.lean`
**Línea**: Insertar después de línea 58 (después del caso `powCall`)

```lean
  | .addrOf _ => none   -- address-taking has no evaluation semantics
```

**Justificación**: `addrOf` es un concepto de codegen (emitir `&` en C/Rust).
No tiene semántica computacional. Retornar `none` es consistente con
`evalStmt(.call) = none` (Eval.lean:126) — ambos son "trusted external".

**Verificación**: `lake build TrustLean.Core.Eval`

### Tarea 3: Agregar caso en `exprToC`

**Archivo**: `TrustLean/Backend/CBackend.lean`
**Línea**: Insertar después de línea 79 (después del caso `powCall`)

```lean
  | .addrOf v => "&" ++ varNameToC v
```

**Semántica C**: Para `VarName.user "nv0"`, emite `&nv0`.
Para `VarName.array "data" 5`, emite `&data[5]`.
`varNameToC` aplica `sanitizeIdentifier` (Common.lean:90-97), que no afecta
nombres NEON válidos (`nv0`, `nu0`, etc.).

**Verificación**: `lake build TrustLean.Backend.CBackend`

### Tarea 4: Agregar caso en `exprToRust`

**Archivo**: `TrustLean/Backend/RustBackend.lean`
**Línea**: Insertar después de línea 69 (después del caso `powCall`)

```lean
  | .addrOf v => "&" ++ varNameToRust v
```

**Verificación**: `lake build TrustLean.Backend.RustBackend`

### Tarea 5: Agregar caso en `exprToMicroC`

**Archivo**: `TrustLean/MicroC/Translation.lean`
**Línea**: Insertar después de línea 34 (después del caso `powCall`)

```lean
  | .addrOf v => .varRef ("&" ++ varNameToC v)
```

**Justificación**: NO extender `MicroCExpr`. El path SIMD no fluye por MicroC eval.
Al mapear a `.varRef("&nv0")`, el pretty printer de MicroC emitirá `&nv0` (correcto
para string generation). Si se evaluara, `env("&nv0")` retorna un default value —
pero esto nunca ocurre porque `Stmt.call` args no se evalúan (evalStmt retorna none).

**Verificación**: `lake build TrustLean.MicroC.Translation`

### Tarea 6: Agregar caso en `exprToMicroRust`

**Archivo**: `TrustLean/MicroRust/Translation.lean`
**Línea**: Insertar después de línea 27 (después del caso `powCall`)

```lean
  | .addrOf v => .varRef ("&" ++ varNameToRust v)
```

**Verificación**: `lake build TrustLean.MicroRust.Translation`

---

## 5. Verificación final

Después de las 6 tareas:

```bash
# Build completo de TrustLean — OBLIGATORIO
lake build

# Verificar zero sorry (invariante del proyecto)
grep -r "sorry" TrustLean/ --include="*.lean" | grep -v "Tests/" | grep -v "--"
# Debe dar 0 resultados

# Verificar zero axiom no estándar
grep -r "axiom" TrustLean/ --include="*.lean" | grep -v "Tests/"
# Solo deben aparecer axioms del framework (propext, quot, Classical)
```

**Gate**: `lake build` PASS + 0 sorry + 0 axioms nuevos.

---

## 6. Lo que NO hacer

1. **NO extender `MicroCExpr`** (MicroC/AST.lean:57-64). Es un tipo separado con sus
   propios consumidores (7 eval functions, pretty printers, roundtrip). Extenderlo
   dispararía ~15 archivos adicionales de cambios. Innecesario porque el path SIMD
   no usa MicroC.

2. **NO extender `MicroRustExpr`**. Misma razón.

3. **NO extender `UnaryOp`** (Value.lean:165-169). `UnaryOp` opera sobre `Value → Option Value`
   (resultado evaluado). `addrOf` necesita la ESTRUCTURA de la expresión (distinguir
   `addrOf (.varRef x)` de `addrOf (.binOp ...)`), no su valor runtime.

4. **NO modificar `Stmt`**. Agregar constructores a `Stmt` afecta 325 pattern matches +
   proofs por inducción estructural. Fue rechazado en 6 debates adversariales
   (ver TRZK_filosofico.md:1641-1648).

5. **NO modificar `getArrayName`** (Eval.lean:33-36). Usa wildcard `| _ => none`.
   El nuevo constructor `addrOf` cae en el wildcard automáticamente.

6. **NO modificar tests** en `Tests/`. Los tests existentes no usan `addrOf` y no
   se rompen. NO agregar tests para `addrOf` en TrustLean — los tests de integración
   pertenecen al proyecto TRZK (consumidor).

7. **NO agregar docstrings ni comentarios** a código que no se modifica. Solo documentar
   el nuevo constructor y los nuevos pattern match cases.

---

## 7. Consumidor: cómo TRZK usará `addrOf`

Después de esta expansión, el proyecto TRZK puede hacer:

```lean
-- En AmoLean/Bridge/SIMDStmtToC.lean:
-- neonCallVoid ahora puede pasar punteros:
def neonCallDeinterleave (aOut bOut ptr : VarName) : Stmt :=
  Stmt.call (.user "__void") "neon_deinterleave_load"
    [.addrOf aOut, .addrOf bOut, .varRef ptr]

-- simdStmtToC emitirá:
-- neon_deinterleave_load(&aOut, &bOut, ptr);
```

El `exprToC (.addrOf (.user "nv0"))` produce `"&nv0"`.
El `exprToC (.varRef (.user "ptr"))` produce `"ptr"` (sin cambios).

La emisión diferenciada de `&` queda codificada en el IR, no en lógica de strings
dependiente del nombre de la función.

---

## 8. Resumen de archivos

| # | Archivo | Línea | Cambio | LOC |
|---|---------|-------|--------|-----|
| 1 | TrustLean/Core/Value.lean | ~217 | Agregar `\| addrOf : VarName → LowLevelExpr` | 1 |
| 2 | TrustLean/Core/Eval.lean | ~58 | Agregar `\| .addrOf _ => none` | 1 |
| 3 | TrustLean/Backend/CBackend.lean | ~79 | Agregar `\| .addrOf v => "&" ++ varNameToC v` | 1 |
| 4 | TrustLean/Backend/RustBackend.lean | ~69 | Agregar `\| .addrOf v => "&" ++ varNameToRust v` | 1 |
| 5 | TrustLean/MicroC/Translation.lean | ~34 | Agregar `\| .addrOf v => .varRef ("&" ++ varNameToC v)` | 1 |
| 6 | TrustLean/MicroRust/Translation.lean | ~27 | Agregar `\| .addrOf v => .varRef ("&" ++ varNameToRust v)` | 1 |
| **Total** | **6 archivos** | | | **6 LOC** |
