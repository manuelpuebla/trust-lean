# Trust-Lean: Architecture

## Current Version: v4.1.0

### Fase 8: UInt128 Agreement — Goldilocks Formal Gap Closure

**Objetivo**: Extender Trust-Lean MicroC con evaluador UInt128 y agreement theorems, cerrando el gap formal entre el modelo unbounded (`Int`) y la aritmética hardware de 128 bits (`__uint128_t`/`u128`). Esto permite que truth_research_zk produzca código verificado para Goldilocks (`P = 2^64 - 2^32 + 1`), cuya multiplicación `(P-1)² ≈ 3.4×10^38` desborda uint64 pero cabe en uint128.

**Motivación**: Goldilocks `P ≈ 1.84×10^19 > maxInt64 ≈ 9.22×10^18`. El `binOp_agreement` de Int64 no aplica (L-731). El código C/Rust real usa `__uint128_t` para multiplicación. Los soundness theorems existentes operan sobre `Int` (unbounded) — el gap es entre `Int` y `uint128_t` en hardware.

### Design Decisions (v4.1.0)

1. **Extension-only**: Archivos nuevos únicamente. Zero modificaciones a archivos de prueba existentes. Única excepción: agregar imports a `MicroC.lean` (patrón estándar: v3.0 agregó Int64, v3.1 agregó Unsigned).
2. **Reutilizar `wrapWidth` de Unsigned.lean**: `wrapUInt128 := wrapWidth 128`. Todas las propiedades (nonneg, lt, idempotent, of_inRange, composición add/sub/mul) se heredan gratis del módulo parametrizado existente.
3. **Shift modulus = `% 128`**: `bshl`/`bshr` usan `b.toNat % 128`, modelando comportamiento de `__uint128_t` en GCC/Clang. Difiere de uint32/uint64 que usan `% 64`. Decisión documentada y con tests de boundary en 0, 63, 64, 127, 128, 129.
4. **widen/trunc en contexto 128-bit**: `MicroCUnaryOp` es compartido; `widen32to64`/`trunc64to32` aplican wrapping a 128 bits en el evaluador uint128. Semánticamente truncan a 32 bits y luego wrappean, lo cual es seguro para código Goldilocks que no usa estas ops.
5. **Agreement pattern de UnsignedAgreement.lean**: Split condicional + incondicional (L-630). Proof pattern: `wrapWidth_of_inRange 128 _ h.1 h.2`. Sin tácticas custom (mantener consistencia con codebase existente).
6. **Goldilocks bridge**: `(P-1)² < 2^128` probado por `native_decide`, habilitando `InUInt128Range` para todas las operaciones de campo.

### Archivos

**Nuevos** (6 archivos):
- `TrustLean/MicroC/UInt128.lean` — Foundation: abbrevs + boundary tests
- `TrustLean/MicroC/UInt128Eval.lean` — Evaluador: BinOp/UnaryOp/Expr/Stmt + @[simp] lemmas
- `TrustLean/MicroC/UInt128Agreement.lean` — Agreement: 12 per-op + general + non-vacuity
- `TrustLean/MicroC/UInt128FuelMono.lean` — Fuel monotonicity: helpers + structural induction
- `TrustLean/MicroC/UInt128Simulation.lean` — Re-export + smoke tests end-to-end
- `TrustLean/Plonky3/GoldilocksUInt128.lean` — Bridge: fits-in-128 theorems + full-fold program

**Modificados** (imports únicamente):
- `TrustLean/MicroC.lean` — agregar 3 imports

### DAG (v4.1.0)

| Nodo | Tipo | Deps | Target | LOC est. | Status |
|------|------|------|--------|----------|--------|
| N27.1 UInt128 Foundation (wrapUInt128, InUInt128Range, arith ops) | FUND | — | MicroC/UInt128.lean | 66 | completed ✓ |
| N27.2 UInt128 Evaluator (BinOp/UnaryOp/Expr/Stmt + simp lemmas) | CRIT | N27.1 | MicroC/UInt128Eval.lean | 237 | completed ✓ |
| N27.3 UInt128 Agreement (per-op + general + non-vacuity) | CRIT | N27.2 | MicroC/UInt128Agreement.lean | 178 | completed ✓ |
| N27.4 UInt128 Fuel Monotonicity (seq/while helpers + structural induction) | CRIT | N27.2 | MicroC/UInt128FuelMono.lean | 202 | completed ✓ |
| N27.5 UInt128 Simulation (re-export + smoke tests end-to-end) | PAR | N27.3, N27.4 | MicroC/UInt128Simulation.lean | 83 | completed ✓ |
| N27.6 Goldilocks UInt128 Bridge (fits-in-128 + full-fold program) | HOJA | N27.5 | Plonky3/GoldilocksUInt128.lean | 133 | completed ✓ |
| N27.7 Integration + Zero Sorry Audit | HOJA | N27.5, N27.6 | MicroC.lean (imports) | 5 | completed ✓ |

### Formal Properties (v4.1.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N27.1 | wrapUInt128 = wrapWidth 128 (not a redefinition) | INVARIANT | P0 |
| N27.1 | InUInt128Range consistent with InUIntRange 128 | EQUIVALENCE | P0 |
| N27.1 | Boundary: wrapUInt128 (2^128) = 0, wrapUInt128 (-1) = 2^128-1 | SOUNDNESS | P0 |
| N27.2 | evalMicroCBinOp_uint128 handles all 12 MicroCBinOp constructors | INVARIANT | P0 |
| N27.2 | evalMicroC_uint128 terminates with lexicographic (fuel, sizeOf stmt) | INVARIANT | P0 |
| N27.2 | Shift modulus = % 128 (not % 64) — boundary tests at 127, 128, 129 | SOUNDNESS | P0 |
| N27.3 | Conditional agreement: arith/bitwise ops agree when result in InUInt128Range | SOUNDNESS | P0 |
| N27.3 | Unconditional agreement: comparison/logical ops always agree | SOUNDNESS | P0 |
| N27.3 | General BinOp agreement: all ops + InUInt128Range hypothesis | SOUNDNESS | P0 |
| N27.3 | Non-vacuity: concrete overflow-free program agreement | SOUNDNESS | P0 |
| N27.4 | evalMicroC_uint128_fuel_mono_full: more fuel preserves non-OOF results | SOUNDNESS | P0 |
| N27.4 | evalMicroC_uint128_fuel_mono: specialization for .normal outcomes | SOUNDNESS | P0 |
| N27.5 | End-to-end: Goldilocks conditional subtract via evalMicroC_uint128 | SOUNDNESS | P0 |
| N27.6 | goldilocks_mul_fits_uint128: (P-1)*(P-1) < 2^128 | SOUNDNESS | P0 |
| N27.6 | goldilocks_add_fits_uint128: (P-1)+(P-1) < 2^128 | SOUNDNESS | P0 |
| N27.6 | Full-fold Goldilocks reduction via evalMicroC_uint128 with agreement | SOUNDNESS | P0 |
| N27.6 | Non-vacuity: mul(P-1, P-1) agreement between uint128 and unbounded | SOUNDNESS | P0 |
| N27.7 | Zero sorry across entire project | SOUNDNESS | P0 |
| N27.7 | lake build succeeds with all new imports | INVARIANT | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

### Bloques

- [x] **B36: UInt128 Foundation** (SEQ, FUND): N27.1 — closed 2026-03-30
- [x] **B37: UInt128 Evaluator** (SEQ, CRIT): N27.2 — closed 2026-03-30
- [x] **B38: Agreement + FuelMono** (AGENT_TEAM): N27.3, N27.4 — closed 2026-03-30
- [x] **B39: Simulation + Goldilocks Bridge** (AGENT_TEAM): N27.5, N27.6 — closed 2026-03-30
- [x] **B40: Integration + Audit** (SEQ, HOJA): N27.7 — closed 2026-03-30

### Instrucciones Detalladas por Bloque

#### B36: UInt128 Foundation (N27.1)

**Pre-Block Briefing obligatorio:**
- **B1**: Leer este plan en ARCHITECTURE.md
- **B3**: `query_lessons.py --hybrid "wrapWidth unsigned wrapping arithmetic"`
- **B4**: `scout.py TrustLean/MicroC/Unsigned.lean` → Read completo (150 LOC)

**Archivo a crear**: `TrustLean/MicroC/UInt128.lean`

**Referencia obligatoria**: `TrustLean/MicroC/Unsigned.lean` — contiene `wrapWidth`, `InUIntRange`, `wrapUInt32/64`, `addUInt32/64`, etc. LEER COMPLETO antes de escribir.

**Tareas**:
1. Importar `TrustLean.MicroC.Unsigned` (NO reimportar Mathlib directamente)
2. Definir abbreviaciones (NO redefinir, NO reprobar propiedades ya existentes):
   ```lean
   abbrev wrapUInt128 (x : Int) : Int := wrapWidth 128 x
   def InUInt128Range (n : Int) : Prop := 0 ≤ n ∧ n < (2 ^ 128 : Int)
   def addUInt128 (a b : Int) : Int := wrapUInt128 (a + b)
   def subUInt128 (a b : Int) : Int := wrapUInt128 (a - b)
   def mulUInt128 (a b : Int) : Int := wrapUInt128 (a * b)
   ```
3. `@[simp]` lemmas delegando a `wrapWidth_nonneg 128`, `wrapWidth_lt 128`, etc.:
   ```lean
   @[simp] theorem wrapUInt128_nonneg (x : Int) : 0 ≤ wrapUInt128 x := wrapWidth_nonneg 128 x
   @[simp] theorem wrapUInt128_lt (x : Int) : wrapUInt128 x < 2 ^ 128 := wrapWidth_lt 128 x
   @[simp] theorem wrapUInt128_idempotent (x : Int) : wrapUInt128 (wrapUInt128 x) = wrapUInt128 x := wrapWidth_idempotent 128 x
   ```
4. Non-vacuity boundary tests via `native_decide`:
   - `wrapUInt128 0 = 0`
   - `wrapUInt128 (2^128 - 1) = 2^128 - 1`
   - `wrapUInt128 (2^128) = 0`
   - `wrapUInt128 (-1) = 2^128 - 1`
   - `addUInt128 (2^128 - 1) 1 = 0`
   - `subUInt128 0 1 = 2^128 - 1`
   - `mulUInt128 (2^64) (2^64) = 0`

**VERIFICAR**: `lake env lean TrustLean/MicroC/UInt128.lean` compila sin errores ni sorry.

**LOC estimado**: ~50. **Riesgo**: Bajo. **Tiempo**: 30 min.

---

#### B37: UInt128 Evaluator (N27.2)

**Pre-Block Briefing obligatorio:**
- **B1**: Leer este plan en ARCHITECTURE.md
- **B3**: `query_lessons.py --lesson L-625` (fuel mono mirrors structure), `--lesson L-620` (minimize preconditions)
- **B4**: `scout.py TrustLean/MicroC/UnsignedEval.lean` → Read completo (322 LOC) — ESTE ES EL TEMPLATE

**Archivo a crear**: `TrustLean/MicroC/UInt128Eval.lean`

**Referencias obligatorias**:
- `TrustLean/MicroC/UnsignedEval.lean` — Template exacto. Leer COMPLETO.
- `TrustLean/MicroC/UInt128.lean` — Importar las definiciones del bloque anterior.
- `TrustLean/MicroC/Eval.lean` — Importar para `evalMicroCExpr`, `getMicroCArrayName`, `Outcome`, etc.

**Tareas**:
1. Importar `TrustLean.MicroC.Eval` y `TrustLean.MicroC.UInt128`
2. Copiar estructura EXACTA de `evalMicroCBinOp_uint64` → `evalMicroCBinOp_uint128`, sustituyendo:
   - `wrapUInt64` → `wrapUInt128`
   - `addUInt64` → `addUInt128`
   - `subUInt64` → `subUInt128`
   - `mulUInt64` → `mulUInt128`
   - **CRÍTICO**: `b.toNat % 64` → `b.toNat % 128` en `bshl` y `bshr`
3. Copiar `evalMicroCUnaryOp_uint64` → `evalMicroCUnaryOp_uint128`:
   - `wrapUInt64` → `wrapUInt128`
   - Los widen/trunc mantienen `n % (2^32 : Int)` interno pero wrappean con `wrapUInt128`
4. Copiar `evalMicroCExpr_uint64` → `evalMicroCExpr_uint128`:
   - Referenciar `evalMicroCBinOp_uint128`, `evalMicroCUnaryOp_uint128`
   - `wrapUInt64` → `wrapUInt128` en `powCall`
5. Copiar `evalMicroC_uint64` → `evalMicroC_uint128`:
   - Referenciar `evalMicroCExpr_uint128`
   - `termination_by (fuel, sizeOf stmt)` — igual
6. Crear ~40 `@[simp]` lemmas (1 por operador × {BinOp, UnaryOp}):
   - Seguir patrón exacto de `evalMicroCBinOp_uint32_add` etc. pero con `uint128`
   - Todas provables por `rfl`
7. Non-vacuity:
   - Aritmética: `addUInt128 (2^128-1) 1 = 0` (overflow wraps)
   - Bitwise: `band` con mask, `bshl 3 4 = 48`
   - **Shift boundary tests**: `bshl 1 127`, `bshl 1 128` (debe wrappear a 0 si % 128)
   - Mersenne-style: `lo = x & mask, hi = x >> 64, sum = lo + hi`

**VERIFICAR**: `lake env lean TrustLean/MicroC/UInt128Eval.lean` compila sin errores ni sorry.

**LOC estimado**: ~500. **Riesgo**: Bajo (mecánico). **Tiempo**: 3-4 hrs.

**TRAP A EVITAR**: Olvidar cambiar `% 64` → `% 128` en bshl/bshr. GREP después de escribir: `grep "% 64" UInt128Eval.lean` debe retornar 0 resultados.

---

#### B38: Agreement + FuelMono (N27.3 + N27.4 en paralelo)

**Pre-Block Briefing obligatorio (para AMBOS workers):**
- **B1**: Leer este plan en ARCHITECTURE.md
- **B3**: `query_lessons.py --lesson L-630` (conditional vs unconditional split), `--lesson L-625` (fuel mono structure)
- **B4 para N27.3**: `scout.py TrustLean/MicroC/UnsignedAgreement.lean` → Read completo (184 LOC)
- **B4 para N27.4**: `scout.py TrustLean/MicroC/UnsignedFuelMono.lean` → Read completo (~385 LOC)

##### Worker N27.3: UInt128Agreement.lean

**Archivo a crear**: `TrustLean/MicroC/UInt128Agreement.lean`

**Referencias obligatorias**:
- `TrustLean/MicroC/UnsignedAgreement.lean` — Template exacto (184 LOC). LEER COMPLETO.
- `TrustLean/MicroC/Int64Agreement.lean` — Referencia cruzada para UnaryOp agreement (197 LOC).

**Tareas**:
1. Importar `TrustLean.MicroC.UInt128Eval`
2. **12 per-op BinOp agreement** (copiar de UnsignedAgreement, sustituir `uint32`→`uint128`, `32`→`128`):
   - **CONDICIONAL** (requieren `InUInt128Range(result)`): add, sub, mul, band, bor, bxor, bshl, bshr
   - **INCONDICIONAL** (producen Bool): eqOp, ltOp, land, lor
   - Proof pattern EXACTO: `simp only [..., wrapWidth_of_inRange 128 _ h.1 h.2]`
   - **ATENCIÓN**: Para bshl/bshr, la hipótesis usa `b.toNat % 128` (no % 64)
3. **General BinOp agreement**:
   ```lean
   theorem evalMicroCBinOp_uint128_agree (op : MicroCBinOp) (v1 v2 : Value)
       (h : ∀ n, evalMicroCBinOp op v1 v2 = some (.int n) → InUInt128Range n) :
       evalMicroCBinOp_uint128 op v1 v2 = evalMicroCBinOp op v1 v2 := by
     cases op <;> cases v1 <;> cases v2 <;>
       simp_all [evalMicroCBinOp_uint128, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
                 addUInt128, subUInt128, mulUInt128]
     all_goals (rename_i h; exact wrapWidth_of_inRange 128 _ h.1 h.2)
   ```
4. **UnaryOp agreement** (neg condicional, lnot incondicional, general):
   - Copiar patrón de UnsignedAgreement, sustituir `32`→`128`
5. **Non-vacuity** (3 ejemplos mínimo):
   - Programa simple: `x = 3 + 4` produce `x = 7` en ambos evaluadores
   - Overflow wraps: `addUInt128 (2^128-1) 1 = 0` en uint128, `≠ 0` en unbounded
   - Bitwise AND masking coincide entre evaluadores

**VERIFICAR**: `lake env lean TrustLean/MicroC/UInt128Agreement.lean` compila sin errores ni sorry.

**LOC estimado**: ~220. **Riesgo**: Bajo. **Tiempo**: 2-3 hrs.

##### Worker N27.4: UInt128FuelMono.lean

**Archivo a crear**: `TrustLean/MicroC/UInt128FuelMono.lean`

**Referencia obligatoria**:
- `TrustLean/MicroC/UnsignedFuelMono.lean` — Template exacto (~385 LOC). LEER COMPLETO línea por línea.

**Tareas**:
1. Importar `TrustLean.MicroC.UInt128Eval`
2. **Equation lemmas** (copiar de UnsignedFuelMono, sustituir `uint64`→`uint128`):
   - `evalMicroC_uint128_eq_return`, `_eq_assign`, `_eq_store`, `_eq_load`, `_eq_call`
   - Todas provables por `unfold evalMicroC_uint128; rfl`
3. **Helper: `fuel_mono_seq_uint128`** (~30 líneas):
   - Takes IHs for s1 and s2
   - Generalize `evalMicroC_uint128 fuel env s1 = r`
   - Case split on outcomes
   - Copiar estructura exacta de `fuel_mono_seq_mc` en UnsignedFuelMono
4. **Helper: `fuel_mono_while_uint128`** (~50 líneas):
   - Nested induction: outer on fuel, inner uses IH for body
   - Base: fuel=0 → outOfFuel contradiction
   - Inductive: evaluate condition, if true → IH body, then recursive IH while
   - Copiar estructura exacta de `fuel_mono_while_mc` en UnsignedFuelMono
5. **Main: `evalMicroC_uint128_fuel_mono_gen`** (~40 líneas):
   - Structural induction on MicroCStmt (11 cases)
   - skip/break/continue → trivial
   - return/assign/store/load → equation lemmas
   - call → contradiction (returns none)
   - ite → case split on condition
   - seq → call fuel_mono_seq_uint128
   - while → call fuel_mono_while_uint128
6. **Public APIs**:
   ```lean
   theorem evalMicroC_uint128_fuel_mono_full {fuel fuel' : Nat} {env : MicroCEnv}
       {stmt : MicroCStmt} {env' : MicroCEnv} {oc : Outcome}
       (h : evalMicroC_uint128 fuel env stmt = some (oc, env'))
       (hle : fuel ≤ fuel') (hoc : oc ≠ .outOfFuel) :
       evalMicroC_uint128 fuel' env stmt = some (oc, env') :=
     evalMicroC_uint128_fuel_mono_gen stmt h hle hoc

   theorem evalMicroC_uint128_fuel_mono {fuel fuel' : Nat} {env : MicroCEnv}
       {stmt : MicroCStmt} {env' : MicroCEnv}
       (h : evalMicroC_uint128 fuel env stmt = some (.normal, env'))
       (hle : fuel ≤ fuel') :
       evalMicroC_uint128 fuel' env stmt = some (.normal, env') :=
     evalMicroC_uint128_fuel_mono_full h hle (by simp)
   ```

**VERIFICAR**: `lake env lean TrustLean/MicroC/UInt128FuelMono.lean` compila sin errores ni sorry.

**LOC estimado**: ~400. **Riesgo**: Medio (fuel mono es la prueba más intrincada, pero el patrón es 100% copiable). **Tiempo**: 3-4 hrs.

**TRAP A EVITAR (L-649)**: En fuel_mono_while, invocar `evalMicroC_uint128_fuel_mono_gen` recursivamente (IH), NO `evalMicroC_fuel_mono_full` (eso es del evaluador unbounded).

---

#### B39: Simulation + Goldilocks Bridge (N27.5 + N27.6 en paralelo)

**Pre-Block Briefing obligatorio:**
- **B1**: Leer este plan en ARCHITECTURE.md
- **B3**: `query_lessons.py --lesson L-731` (Goldilocks exceeds Int64Range)
- **B4 para N27.5**: `scout.py TrustLean/MicroC/UnsignedSimulation.lean` → Read (80 LOC)
- **B4 para N27.6**: `scout.py TrustLean/Plonky3/GoldilocksReduce.lean` → Read completo (234 LOC)

##### Worker N27.5: UInt128Simulation.lean

**Archivo a crear**: `TrustLean/MicroC/UInt128Simulation.lean`

**Tareas**:
1. Importar `TrustLean.MicroC.UInt128Agreement`, `UInt128FuelMono`, `Simulation`
2. Re-exportar key theorems con `#check`:
   ```lean
   #check @stmtToMicroC_correct
   #check @evalMicroC_uint128_fuel_mono_full
   #check @evalMicroCBinOp_uint128_agree
   #check @evalMicroCUnaryOp_uint128_agree
   ```
3. Smoke tests end-to-end con `evalMicroC_uint128`:
   - Goldilocks conditional subtract (copiar de GoldilocksReduce.lean pero con `evalMicroC_uint128`)
   - 128-bit arithmetic: `x = (2^64) * (2^64-1)` produces correct result
   - Shift boundary: `x = 1 << 127` en uint128
   - Mersenne31 reduce pattern en modo uint128 (compatibilidad backward)

**LOC estimado**: ~120. **Riesgo**: Bajo.

##### Worker N27.6: GoldilocksUInt128.lean

**Archivo a crear**: `TrustLean/Plonky3/GoldilocksUInt128.lean`

**Referencias obligatorias**:
- `TrustLean/Plonky3/GoldilocksReduce.lean` — Constantes, spec, reduce program. LEER COMPLETO.
- `TrustLean/MicroC/UInt128Eval.lean` — Para `evalMicroC_uint128`.
- `TrustLean/MicroC/UInt128Agreement.lean` — Para `evalMicroCBinOp_uint128_agree`.

**Tareas**:
1. Importar `TrustLean.MicroC.UInt128Agreement`, `TrustLean.Plonky3.GoldilocksReduce`
2. **Theorems de bounds** (cierran el gap formal):
   ```lean
   theorem goldilocks_mul_fits_uint128 (a b : Int)
       (ha : 0 ≤ a ∧ a < goldilocks_P_int) (hb : 0 ≤ b ∧ b < goldilocks_P_int) :
       InUInt128Range (a * b) := by
     constructor
     · exact mul_nonneg ha.1 hb.1
     · calc a * b < goldilocks_P_int * goldilocks_P_int := by nlinarith [ha.2, hb.2]
       _ < 2 ^ 128 := by native_decide

   theorem goldilocks_add_fits_uint128 (a b : Int)
       (ha : 0 ≤ a ∧ a < goldilocks_P_int) (hb : 0 ≤ b ∧ b < goldilocks_P_int) :
       InUInt128Range (a + b) := by
     constructor <;> omega

   theorem goldilocks_sub_fits_uint128 (a b : Int)
       (ha : 0 ≤ a ∧ a < goldilocks_P_int) (hb : 0 ≤ b ∧ b < goldilocks_P_int) :
       InUInt128Range (a - b) := by
     constructor <;> omega  -- may need native_decide for upper bound
   ```
3. **Goldilocks full-fold MicroC program usando evalMicroC_uint128**:
   - La spec algebraica ya existe en GoldilocksReduce.lean
   - Crear programa MicroC para el fold completo (hi = x >> 64, lo = x & mask, sum = lo + hi*C)
   - El evaluador uint128 puede manejar shift-by-64 correctamente (64 % 128 = 64, no 0)
   - Smoke tests: fold de valores concretos con `native_decide`
4. **Non-vacuity de agreement**:
   ```lean
   -- evalMicroC_uint128 y evalMicroC coinciden en Goldilocks ops
   example :
       let prog := MicroCStmt.assign "x" (.binOp .mul (.litInt (goldilocks_P_int - 1)) (.litInt (goldilocks_P_int - 1)))
       (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default prog; pure (e "x")) =
       (do let (_, e) ← evalMicroC 10 MicroCEnv.default prog; pure (e "x")) := by native_decide
   ```
5. **Key: demostrar que shift-by-64 funciona en uint128 pero no en uint64**:
   ```lean
   -- In uint128: 64 % 128 = 64, so shift works correctly
   example : (64 : Int).toNat % 128 = 64 := by native_decide
   -- In uint64: 64 % 64 = 0, so shift gives wrong result (this is why uint64 can't do Goldilocks fold)
   example : (64 : Int).toNat % 64 = 0 := by native_decide
   ```

**LOC estimado**: ~200. **Riesgo**: Medio (nlinarith/omega para bounds puede requerir ajustes). **Tiempo**: 3-4 hrs.

---

#### B40: Integration + Audit (N27.7)

**Pre-Block Briefing obligatorio:**
- **B1**: Leer este plan en ARCHITECTURE.md
- **B4**: `scout.py TrustLean/MicroC.lean` → Read completo

**Tareas**:
1. Agregar imports a `TrustLean/MicroC.lean`:
   ```lean
   -- v4.1.0 modules
   import TrustLean.MicroC.UInt128
   import TrustLean.MicroC.UInt128Eval
   import TrustLean.MicroC.UInt128Agreement
   import TrustLean.MicroC.UInt128FuelMono
   import TrustLean.MicroC.UInt128Simulation
   ```
   (GoldilocksUInt128.lean no se importa en MicroC.lean — está en Plonky3/)
2. `lake build` completo — zero errors
3. Zero sorry audit: `grep -r "sorry" TrustLean/MicroC/UInt128*.lean` = 0 resultados
4. `grep -r "sorry" TrustLean/Plonky3/GoldilocksUInt128.lean` = 0 resultados

**LOC estimado**: ~10 (solo imports). **Riesgo**: Bajo. **Tiempo**: 30 min.

---

## Previous Versions

### v4.0.0

### v4.0 Corrección 1: Cerrar roundtrip sorry

**Objetivo**: Cerrar 2 sorry en capstone roundtrip theorems de MicroRust.
**Patron**: Adaptacion textual de MicroC/RoundtripExpr.lean + RoundtripStmt.lean.
**Lecciones**: L-669 (ExprSafe), L-668 (arrayAccess base=varRef), L-675 (nonseq helper + nofun).

| Nodo | Tipo | Deps | Target | LOC est. | Status |
|------|------|------|--------|----------|--------|
| C1.1 rustExpr_roundtrip_with_rest | CRIT | — | RoundtripExpr.lean:793 | ~690 | pending |
| C1.2 parseMicroRust_roundtrip | CRIT | C1.1 | RoundtripStmt.lean:246 | ~250 | pending |

| Bloque | Nodos | Tipo |
|--------|-------|------|
| B34 | C1.1 | SEQ (CRIT) |
| B35 | C1.2 | SEQ (CRIT, depends on B34) |

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
