# Trust-Lean Upgrade Context: Plonky3 Verification Support

**Fecha**: 2026-03-13
**Objetivo**: Extender Trust-Lean v3.0 para soportar verificacion formal de Plonky3 via MicroC pipeline
**Consumidor**: AMO-Lean v2.7.0 (Plonky3 full certification)
**Estado actual de Trust-Lean**: v3.0 — MicroC pipeline con Int64, function calls, roundtrip

---

## 1. Contexto: Por que esta upgrade es necesaria

AMO-Lean v2.6.0 demostro que la Translation Validation de Plonky3 funciona: 3018 LOC, 0 sorry, 9 archivos probando que las operaciones de campo de Plonky3 son correctas (Mersenne31, BabyBear via Montgomery, Goldilocks). Pero esa verificacion se hizo **directamente en Lean** (UInt32/UInt64 → ZMod p), sin pasar por MicroC.

El paso siguiente es conectar el pipeline **completo**:

```
Plonky3 (Rust) → [manual translation] → MicroC (formal C)
    → [stmtToMicroC_correct] → Trust-Lean Stmt
    → [expandedSigmaToStmt_correct] → AMO-Lean ExpandedSigma
    → [verified_optimization_pipeline] → E-Graph
    → [fri_pipeline_soundness] → FRI Algebraic Guarantees
```

Para que este pipeline funcione end-to-end, Trust-Lean necesita:
1. Evaluador unsigned (UInt32/UInt64) — actualmente solo tiene Int64 signed
2. Operaciones bitwise — Plonky3 usa `&`, `|`, `^`, `<<`, `>>` extensivamente
3. Type casting (widening/truncation) — u32 → u64 y u64 → u32
4. Bridge aritmetica modular — `x % p` como operacion formal

---

## 2. Estado actual de Trust-Lean v3.0

### Arquitectura

```
FRONTENDS              CORE IR              BACKENDS
+---------------+  +--------------+  +----------------+
| ArithExpr     |  |              |  | C Backend      |
| BoolExpr      +->| Stmt (12ops) +->| Rust Backend   |
| ImpStmt       |  | Value        |  |                |
| ExpandedSigma |  | Fuel-based   |  | (future: LLVM) |
+---------------+  +--------------+  +----------------+
```

### IR actual (Stmt)

```lean
inductive Stmt where
  | skip
  | assign (var : String) (expr : Expr)
  | seq (s1 s2 : Stmt)
  | ite (cond : Expr) (thenBranch elseBranch : Stmt)
  | while (cond : Expr) (body : Stmt)
  | for_ (init : Stmt) (cond : Expr) (update : Stmt) (body : Stmt)
  | break
  | continue
  | call (fname : String) (args : List Expr) (retVar : Option String)
  | arrayStore (arr : String) (idx : Expr) (val : Expr)
  | returnStmt (expr : Option Expr)
  | block (stmts : List Stmt)
```

### BinOp actual

```lean
inductive BinOp where
  | add | sub | mul   -- aritmetica
  | eq | lt           -- comparacion
  | and | or          -- logica (evaluacion total, no short-circuit)
```

**Faltan**: `band`, `bor`, `bxor`, `bshl`, `bshr` (bitwise)

### Modelo de enteros actual

- Unico tipo: `Int64` (signed, 64-bit, two's complement wrapping)
- `wrapInt64 (x : Int) : Int := ((x + 2^63) % 2^64) - 2^63`
- Rango: [-2^63, 2^63 - 1]
- No existe UInt32 ni UInt64

### Teoremas gate existentes

| Teorema | Statement | Archivo |
|---------|-----------|---------|
| `evalStmt_fuel_mono` | Fuel monotonicity | Core/FuelMono.lean |
| `stmtToMicroC_correct` | IR → MicroC forward simulation | MicroC/Simulation.lean |
| `evalMicroCBinOp_int64_agree` | Int64 in-range agreement | MicroC/Int64Agreement.lean |
| `stmtToMicroC_correct_withCalls` | Simulation con function calls | MicroC/CallSimulation.lean |
| `master_roundtrip` | parse(print(stmt)) = stmt | MicroC/RoundtripMaster.lean |
| `expandedSigmaToStmt_correct` | ExpandedSigma → Stmt simulation | Bridge/Correctness.lean |

### Archivos clave

| Archivo | LOC | Contenido |
|---------|-----|-----------|
| `Core/Stmt.lean` | ~120 | Stmt, Expr, BinOp, Value inductives |
| `Core/Eval.lean` | ~200 | evalExpr, evalStmt (fuel-based) |
| `Core/FuelMono.lean` | ~180 | Fuel monotonicity theorems |
| `MicroC/AST.lean` | ~100 | MicroC AST types |
| `MicroC/Translation.lean` | ~200 | Stmt → MicroC translation |
| `MicroC/Eval.lean` | ~250 | MicroC evaluator (Int64) |
| `MicroC/Simulation.lean` | ~350 | Forward simulation proof |
| `MicroC/Int64Agreement.lean` | ~200 | BinOp agreement proofs |
| `MicroC/PrettyPrint.lean` | ~150 | MicroC → C string |
| `MicroC/Parser.lean` | ~300 | C string → MicroC |
| `MicroC/RoundtripMaster.lean` | ~250 | parse(print) = id |
| `MicroC/CallSimulation.lean` | ~200 | Function call simulation |
| `Bridge/Correctness.lean` | ~300 | ExpandedSigma → Stmt correctness |

---

## 3. Tareas de Extension

### Tarea 1: Extender BinOp con operaciones bitwise (~200 LOC)

**Prioridad**: CRITICA (bloqueante para Mersenne31)

**Que hacer**:
1. Agregar 5 constructores a `BinOp`:
   ```lean
   | band   -- bitwise AND: a & b
   | bor    -- bitwise OR: a | b
   | bxor   -- bitwise XOR: a ^ b
   | bshl   -- left shift: a << b
   | bshr   -- right shift: a >> b (arithmetic/logical depending on signedness)
   ```

2. Extender `evalBinOp` en `Core/Eval.lean`:
   ```lean
   | .band => Value.int (Int.land a b)     -- Lean's built-in bitwise AND on Int
   | .bor  => Value.int (Int.lor a b)
   | .bxor => Value.int (Int.xor a b)
   | .bshl => Value.int (Int.shiftLeft a b.toNat)
   | .bshr => Value.int (Int.shiftRight a b.toNat)
   ```

3. Extender `evalMicroCBinOp` en `MicroC/Eval.lean` con wrapping Int64

4. Extender `binOpToC` en `Backend/CBackend.lean`:
   ```lean
   | .band => "&" | .bor => "|" | .bxor => "^" | .bshl => "<<" | .bshr => ">>"
   ```

5. Extender `binOpToMicroC` en `MicroC/Translation.lean`

6. Extender `printMicroCBinOp` y `parseMicroCBinOp` para roundtrip

**Archivos a modificar**: Core/Stmt.lean, Core/Eval.lean, MicroC/AST.lean, MicroC/Eval.lean, MicroC/Translation.lean, MicroC/PrettyPrint.lean, MicroC/Parser.lean, Backend/CBackend.lean

**Teoremas a re-probar/extender**:
- `evalMicroCBinOp_int64_agree` — agregar 5 casos
- `stmtToMicroC_correct` — la simulacion debe cubrir los nuevos BinOps
- `master_roundtrip` — parse/print de los nuevos operadores

**Riesgo**: BAJO — es extension puramente aditiva. Los constructores existentes no cambian. Lean maneja la exhaustividad via `match` patterns.

**Referencia**: `Int.land`, `Int.lor`, `Int.xor`, `Int.shiftLeft`, `Int.shiftRight` en Lean 4 core.

---

### Tarea 2: Evaluador UInt32/UInt64 (~300 LOC)

**Prioridad**: CRITICA (bloqueante para toda la verificacion)

**Que hacer**:

El evaluador actual usa `wrapInt64` (signed). Para Plonky3 necesitamos unsigned wrapping:

1. Definir nuevas funciones de wrapping:
   ```lean
   def wrapUInt32 (x : Int) : Int := x % (2^32 : Int)
   -- Resultado siempre en [0, 2^32)

   def wrapUInt64 (x : Int) : Int := x % (2^64 : Int)
   -- Resultado siempre en [0, 2^64)
   ```

2. Crear `MicroC/EvalUnsigned.lean` (~150 LOC):
   - `evalMicroCExpr_uint32 : MicroCExpr → Env → Int` (wraps all ops at 32-bit unsigned)
   - `evalMicroCExpr_uint64 : MicroCExpr → Env → Int` (wraps all ops at 64-bit unsigned)
   - `evalMicroCStmt_uint32/64` (statement-level evaluation)

3. Crear `MicroC/UnsignedAgreement.lean` (~150 LOC):
   - `evalMicroCBinOp_uint32_agree`: cuando ambos inputs estan en [0, 2^32), el resultado de cada BinOp esta en [0, 2^32) despues de wrapping
   - `evalMicroCBinOp_uint64_agree`: idem para 64-bit
   - Especialmente importante para bitwise: `a & b`, `a >> k` preservan rangos

4. Probar simulacion: `stmtToMicroC_correct_uint32/64`
   - Puede reutilizar la estructura de `stmtToMicroC_correct` (misma induccion sobre Stmt)
   - Solo cambia la funcion de wrapping

**Decision de diseno**: No crear un NUEVO tipo de Value. Seguir usando `Value.int : Int → Value` pero con wrapping diferente. Esto evita duplicar toda la infraestructura. El tipo de wrapping se pasa como parametro o se instancia.

**Alternativa mas limpia**: Parametrizar el evaluador sobre una clase `IntModel`:
```lean
class IntModel (M : Type) where
  wrap : Int → Int
  wrap_idempotent : ∀ x, wrap (wrap x) = wrap x
  wrap_add : ∀ a b, wrap (wrap a + wrap b) = wrap (a + b)
  -- etc.

instance : IntModel Int64Model where wrap := wrapInt64; ...
instance : IntModel UInt32Model where wrap := wrapUInt32; ...
instance : IntModel UInt64Model where wrap := wrapUInt64; ...
```

Esto permite reutilizar TODO el framework de simulacion con un solo parametro de tipo.

**Referencia**: El patron esta probado en Fiat-Crypto (Erbsen et al.) donde parametrizan sobre el ancho de palabra.

---

### Tarea 3: Type Casting (widening/truncation) (~100 LOC)

**Prioridad**: ALTA (necesario para Mersenne31 mul: u32 * u32 → u64, y Goldilocks reduce128)

**Que hacer**:

1. Agregar operaciones unarias de casting:
   ```lean
   inductive UnaryOp where
     | neg           -- existing
     | not_          -- existing
     | widen32to64   -- NEW: (int32_t x) → (int64_t)(x)  -- zero-extend for unsigned
     | trunc64to32   -- NEW: (int64_t x) → (int32_t)(x & 0xFFFFFFFF)
   ```

2. Semantica:
   ```lean
   | .widen32to64 => Value.int (v % 2^32)       -- zero-extend: keep low 32 bits as-is
   | .trunc64to32 => Value.int (v % 2^32)       -- truncate: keep low 32 bits
   ```
   Nota: para unsigned, widen y trunc son ambos `% 2^32` en la representacion actual (Int). La diferencia es semantica: widen preserva el valor, trunc puede perder bits.

3. C backend:
   ```lean
   | .widen32to64 => "(int64_t)" ++ exprToC e
   | .trunc64to32 => "(int32_t)" ++ exprToC e
   ```

4. Teoremas: agreement + roundtrip para los nuevos operadores.

**Referencia**: CompCert `Cop.sem_cast` maneja ~20 tipos de cast. Nosotros solo necesitamos 2.

---

### Tarea 4: Bridge de aritmetica modular (~150 LOC)

**Prioridad**: MEDIA (necesario para la composicion end-to-end, pero AMO-Lean ya tiene los bridges directos)

**Que hacer**:

No se trata de agregar `% p` como primitiva en MicroC (eso seria incorrecto — MicroC modela C99 que no tiene aritmetica modular nativa). En cambio:

1. Definir `reduce_mod_p` como un **patron de programa MicroC**:
   ```c
   // Para Mersenne31: reduce via bit manipulation
   int32_t reduce_mersenne31(int64_t x) {
     int32_t lo = (int32_t)(x & 0x7FFFFFFF);
     int32_t hi = (int32_t)(x >> 31);
     int32_t sum = lo + hi;
     if (sum >= P) sum -= P;
     return sum;
   }
   ```

2. Probar que `evalMicroC(reduce_mersenne31_prog, env) = env["x"] % P`:
   - Esto usa los nuevos bitwise ops (Tarea 1) + casting (Tarea 3)
   - Es un per-function refinement proof identico al patron Jasmin/Kyber

3. Similar para BabyBear (Montgomery reduce) y Goldilocks (reduce128).

**Nota**: Este bridge es donde AMO-Lean v2.7 y Trust-Lean convergen. AMO-Lean define las specs (ZMod p), Trust-Lean ejecuta los programas MicroC, y el bridge theorem prueba que coinciden.

---

### Tarea 5: Hi/Lo splitting para 128-bit (~100 LOC, opcional)

**Prioridad**: BAJA-MEDIA (solo necesario para Goldilocks, que usa u128)

**Que hacer**:

C99 no tiene `__uint128_t` como tipo estandar. La solucion es modelar 128-bit como par (hi, lo) de 64-bit:

```c
// x = hi * 2^64 + lo
int64_t mul_wide_lo(int64_t a, int64_t b) { return (int64_t)(a * b); }
int64_t mul_wide_hi(int64_t a, int64_t b) { /* via Karatsuba or compiler intrinsic */ }
```

Alternativa: GCC extension `__int128` como macro que se expande al patron hi/lo.

**Nota**: Para v3.1, empezar SIN 128-bit (cubrir solo Mersenne31 y BabyBear que usan u32/u64). Goldilocks u128 puede diferirse a v3.2.

---

## 4. Fuentes a estudiar ANTES de escribir codigo

### Obligatorias (leer antes de empezar)

1. **Trust-Lean v3.0 codebase** — Entender la estructura completa:
   - `TrustLean/Core/Stmt.lean` — IR definitions
   - `TrustLean/Core/Eval.lean` — evaluador fuel-based
   - `TrustLean/MicroC/Eval.lean` — evaluador MicroC (Int64)
   - `TrustLean/MicroC/Simulation.lean` — simulacion Stmt ↔ MicroC
   - `TrustLean/MicroC/Int64Agreement.lean` — agreement proofs (TEMPLATE para unsigned)

2. **AMO-Lean v2.6 Plonky3 TV files** — Entender que specs existen:
   - `AmoLean/Field/Mersenne31.lean` — Mersenne31 field ops + toZMod
   - `AmoLean/Field/Montgomery.lean` — Montgomery reduction (the target spec)
   - `AmoLean/Field/Plonky3/Mersenne31TV.lean` — from_u62 correctness
   - `AmoLean/Field/Plonky3/BabyBearTV.lean` — bb_monty_roundtrip

3. **Plonky3 Rust source** (en AMO-Lean repo):
   - `verification/plonky3/plonky3_source/mersenne-31/src/mersenne_31.rs` — Mersenne31 ops
   - `verification/plonky3/plonky3_source/monty-31/src/utils.rs` — Montgomery ops (add, sub, monty_reduce)
   - `verification/plonky3/plonky3_source/goldilocks/src/goldilocks.rs` — Goldilocks ops

### Contextuales (leer para entender el landscape)

4. **CompCert** (Leroy, CACM 2009) — Forward simulation methodology
   - Path: `~/Documents/claudio/biblioteca/indices/verificacion/compcert.md`
   - Relevancia: El patron de simulacion IR → target es identico

5. **Fiat-Crypto** (Erbsen et al., S&P 2019) — Verified field arithmetic codegen
   - Path: buscar en `~/Documents/claudio/biblioteca/verificacion/`
   - Relevancia: Parametrizacion sobre ancho de palabra, bounds inference

6. **Jasmin/Kyber Episode IV** (Almeida et al., TCHES 2023) — Per-function refinement template
   - Relevancia: Exactamente el patron que Trust-Lean + AMO-Lean implementan

7. **Formally Verified NTT** (Trieu, 2025, Rocq) — NTT verificado con code synthesis
   - Path: `~/Documents/claudio/biblioteca/ntt/Formally Verified Number-Theoretic Transform (Trieu, ntt).pdf`
   - Relevancia: Montgomery reduction + Barrett reduction verificados en Rocq

8. **Montgomery Multiplication Verified** (Affeldt et al., ITP 2018)
   - Relevancia: 96 lemmas para Montgomery. Template para la Tarea 4 bridge.

9. **A note on the implementation of the NTT** (Scott)
   - Path: `~/Documents/claudio/biblioteca/ntt/`
   - Relevancia: Constant-time NTT con Montgomery reduction, excess tracking

### Lecciones relevantes (query con query_lessons.py)

```bash
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "Trust-Lean MicroC bitwise unsigned evaluation"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "BinOp extension Stmt evaluation fuel"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-626  # MicroC Int64 wrapping at operation boundaries
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-629  # MicroC fuel mono simplification
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-659  # Extension-only architecture
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-655  # Call-free equivalence patterns
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-685  # Nat-to-Int cast without push_cast
```

---

## 5. Orden de ejecucion recomendado

```
Tarea 1: BinOp bitwise (~200 LOC)
  ↓ [desbloquea Mersenne31 bit masking]
Tarea 2: Evaluador UInt32/UInt64 (~300 LOC)
  ↓ [desbloquea toda la verificacion unsigned]
Tarea 3: Type casting (~100 LOC)
  ↓ [desbloquea widening u32→u64 para mul]
Tarea 4: Bridge modular (~150 LOC)
  ↓ [desbloquea composicion con AMO-Lean specs]
Tarea 5: Hi/Lo 128-bit (~100 LOC, opcional)
  ↓ [desbloquea Goldilocks]
```

**Total**: ~750-850 LOC de extension (nuevos archivos, no modifica existentes excepto BinOp/UnaryOp enums)

**Estrategia**: Extension-only architecture (L-659). Cada tarea produce nuevos archivos. Los unicos archivos existentes que se modifican son:
- `Core/Stmt.lean` — agregar constructores a BinOp/UnaryOp
- `Backend/CBackend.lean` — agregar cases para nuevos ops
- `MicroC/Translation.lean` — agregar cases para nuevos ops
- `MicroC/PrettyPrint.lean` — agregar print para nuevos ops
- `MicroC/Parser.lean` — agregar parse para nuevos ops

Todo lo demas es NUEVO: `MicroC/EvalUnsigned.lean`, `MicroC/UnsignedAgreement.lean`, `MicroC/UnsignedSimulation.lean`.

---

## 6. Criterios de exito

| Criterio | Target |
|----------|--------|
| Sorry | 0 |
| Axiomas nuevos | 0 |
| `lake build` | 0 errores |
| Regresion en v3.0 | 0 (todos los tests existentes pasan) |
| `stmtToMicroC_correct_uint32` | Probado |
| `stmtToMicroC_correct_uint64` | Probado |
| `master_roundtrip` con bitwise ops | Probado |
| Mersenne31 reduce en MicroC | `evalMicroC_uint32(reduce_prog) = x % p` probado |
| BabyBear monty_reduce en MicroC | `evalMicroC_uint32(monty_prog) = monty_reduce(x)` probado |

---

## 7. Version target

**Trust-Lean v3.1**: UInt32/UInt64 + bitwise + casting + Plonky3 field bridges
**Estimacion**: ~750-850 LOC nuevos, 0 sorry, extension-only
