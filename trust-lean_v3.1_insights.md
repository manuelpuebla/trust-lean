# Trust-Lean v3.1 Insights: Plonky3 Unsigned + Bitwise Extension

**Fecha**: 2026-03-13
**Fuentes**: 8 agentes paralelos — codebase v3.0, AMO-Lean Plonky3 TV, Plonky3 Rust source, 55 lecciones, 15+ papers, 6 librerías internas, búsqueda online exhaustiva, Mathlib/BitVec lemmas
**Objetivo**: Recopilar estrategias, teoremas reutilizables y decisiones de diseño para implementar Trust-Lean v3.1

---

## 1. ESTADO ACTUAL DE TRUST-LEAN v3.0 (Mapa Completo)

### 1.1 IR Core

**BinOp** (7 constructores): `add | sub | mul | eqOp | ltOp | land | lor`
**UnaryOp** (2 constructores): `neg | lnot`
**Value** (2 constructores): `int : Int → Value | bool : Bool → Value`
**Stmt** (12 constructores): assign, store, load, seq, ite, while, for_, call, skip, break_, continue_, return_

**Evaluador**: Fuel-based, `evalStmt : Nat → LowLevelEnv → Stmt → Option (Outcome × LowLevelEnv)`. Fuel solo se consume en `while`/`for_`. Terminación por `(fuel, sizeOf stmt)` lexicográfico.

### 1.2 Wrapping Int64

```lean
def wrapInt64 (n : Int) : Int :=
  let n' := n % twoPow64
  if n' > maxInt64 then n' - twoPow64 else n'
```

Operaciones: `addInt64`, `subInt64`, `mulInt64`, `negInt64` — todas wrappean via `wrapInt64`.

Teoremas clave:
- `InInt64Range_wrapInt64` — wrapping siempre produce valor en rango
- `wrapInt64_of_inRange` — identity en valores en rango
- `wrapInt64_idempotent` — idempotencia

### 1.3 Agreement Pattern (TEMPLATE para unsigned)

```lean
-- Per-operator (condicional para aritmética):
theorem evalMicroCBinOp_int64_agree_add (a b : Int) (h : InInt64Range (a + b)) :
    evalMicroCBinOp_int64 .add (.int a) (.int b) = evalMicroCBinOp .add (.int a) (.int b)

-- Per-operator (incondicional para comparación/lógica):
theorem evalMicroCBinOp_int64_agree_eqOp ...  -- sin hypothesis de rango

-- General:
theorem evalMicroCBinOp_int64_agree (op : MicroCBinOp) (v1 v2 : Value)
    (h : ∀ n, evalMicroCBinOp op v1 v2 = some (.int n) → InInt64Range n) :
    evalMicroCBinOp_int64 op v1 v2 = evalMicroCBinOp op v1 v2
```

**Insight clave**: Para bitwise ops, el agreement será **incondicional** (como eqOp/ltOp), porque bitwise no tiene overflow en el sentido aritmético.

### 1.4 Simulation Pattern

```lean
theorem stmtToMicroC_correct
    (hinj : VarNameInjective) (hwf : WellFormedArrayBases stmt)
    (h : evalStmt fuel env stmt = some (oc, env'))
    (hb : microCBridge env mcEnv) (hoc : oc ≠ .outOfFuel) :
    ∃ mcEnv', evalMicroC fuel mcEnv (stmtToMicroC stmt) = some (oc, mcEnv')
      ∧ microCBridge env' mcEnv'
```

Prueba por inducción estructural sobre Stmt. Caso while delegado a `sim_while_helper` con fuel induction.

### 1.5 Archivos Clave para Modificar

| Archivo | LOC | Cambio v3.1 |
|---------|-----|-------------|
| `Core/Value.lean` | ~231 | +5 BinOp constructores (band/bor/bxor/bshl/bshr) |
| `Core/Eval.lean` | ~266 | +5 cases en evalBinOp |
| `MicroC/AST.lean` | ~233 | +5 MicroCBinOp constructores |
| `MicroC/Int64Eval.lean` | ~462 | +5 cases en evalMicroCBinOp_int64 |
| `MicroC/Int64Agreement.lean` | ~158 | +5 agreement theorems |
| `Backend/CBackend.lean` | ~178 | +5 cases en binOpToC |
| `MicroC/PrettyPrint.lean` | ~225 | +5 printer cases |
| `MicroC/Parser.lean` | ~382 | +5 parser cases |

---

## 2. TARGET: Plonky3 Field Operations (Rust → MicroC)

### 2.1 Mersenne31 (P = 2^31 - 1)

**Operación clave — `reduce_64`** (from_u62):
```rust
pub(crate) fn reduce_64(val: u64) -> u32 {
    let lo = (val & (P as u64)) as u32;    // x & 0x7FFFFFFF (low 31 bits)
    let hi = val >> 31;                     // x / 2^31
    let sum1 = lo as u64 + hi;
    let lo2 = (sum1 & (P as u64)) as u32;
    let hi2 = (sum1 >> 31) as u32;
    let sum2 = lo2 + hi2;
    sum2.min(sum2.wrapping_sub(P))
}
```

**Bitwise ops requeridas**: `& 0x7FFFFFFF` (band), `>> 31` (bshr)
**Type casts requeridos**: `as u32` (trunc64to32), `as u64` (widen32to64)
**Identidad algebraica**: `2^31 ≡ 1 (mod P)`, probada en AMO-Lean como `two_pow_31_mod_p`

**Multiplicación**: u32 × u32 → u64 (widening mul), luego `reduce_64`

### 2.2 BabyBear (P = 2013265921 = 2^31 - 2^27 + 1)

**Montgomery Reduction** (monty_reduce):
```rust
fn monty_reduce(x: u64) -> u32 {
    let t = x.wrapping_mul(MONTY_MU as u64) as u32;   // t = (x * MU) mod 2^32
    let u = (t as u64) * (PRIME as u64);               // u = t * P
    let result = ((x - u) >> 32) as u32;               // (x - u) / R
    if result >= PRIME { result - PRIME } else { result }
}
```

**Constantes**: MU_NEG = 2013265919, MU = 2281701377, R = 2^32
**Identidad clave**: `(MU * P + 1) % R = 0`
**Teorema AMO-Lean**: `bb_monty_roundtrip : from_monty(monty_mul(to_monty a, to_monty b)) = (a * b) % P`

### 2.3 Goldilocks (P = 2^64 - 2^32 + 1) — Diferido a v3.2

**reduce128**: Requiere u128 (hi/lo splitting). Usa identidad `2^64 ≡ 2^32 - 1 (mod P)`.
**Decision**: Diferir a v3.2 por complejidad de 128-bit.

### 2.4 Operaciones Totales Requeridas

| Operación | Mersenne31 | BabyBear | Goldilocks |
|-----------|------------|----------|------------|
| `band` (&) | ✓ (masking) | ✓ | ✓ |
| `bor` (\|) | — | — | — |
| `bxor` (^) | — | — | — |
| `bshl` (<<) | — | — | — |
| `bshr` (>>) | ✓ (split) | ✓ (reduce) | ✓ |
| `widen32to64` | ✓ (mul) | ✓ (mul) | — |
| `trunc64to32` | ✓ (reduce) | ✓ (reduce) | — |
| `wrapUInt32` | ✓ | ✓ | — |
| `wrapUInt64` | ✓ | ✓ | ✓ |

---

## 3. ESTRATEGIA DE DISEÑO: IntModel Typeclass

### 3.1 Patrón Parametrizado (Validado por Fiat-Crypto + CompCert)

```lean
class IntModel (M : Type) where
  wrap : Int → Int
  wrap_idempotent : ∀ x, wrap (wrap x) = wrap x
  wrap_add : ∀ a b, wrap (wrap a + wrap b) = wrap (a + b)
  wrap_sub : ∀ a b, wrap (wrap a - wrap b) = wrap (a - b)
  wrap_mul : ∀ a b, wrap (wrap a * wrap b) = wrap (a * b)

instance : IntModel Int64Model where wrap := wrapInt64; ...
instance : IntModel UInt32Model where wrap := wrapUInt32; ...
instance : IntModel UInt64Model where wrap := wrapUInt64; ...
```

**Ventaja**: Un solo framework de simulación instanciado 3 veces. Ahorra ~600 LOC de duplicación.

**Fuente**: Fiat-Crypto (Erbsen et al., S&P 2019) parametriza sobre word width con el mismo patrón. CompCert usa module signature con `wordsize` parameter.

### 3.2 Alternativa Más Ligera: Width Parameter

```lean
def wrapWidth (width : Nat) (x : Int) : Int := x % (2 ^ width : Int)

-- Propiedades genéricas:
theorem wrapWidth_idempotent (w : Nat) (x : Int) :
    wrapWidth w (wrapWidth w x) = wrapWidth w x

theorem wrapWidth_add (w : Nat) (a b : Int) :
    wrapWidth w (wrapWidth w a + wrapWidth w b) = wrapWidth w (a + b)
```

Instanciación: `wrapUInt32 = wrapWidth 32`, `wrapUInt64 = wrapWidth 64`.

**Ventaja**: Más simple que typeclass, permite `omega` y `Int.emod_*` lemmas directamente.
**Recomendación**: Usar este approach para v3.1 (pragmático). Typeclass si se necesitan más modelos en el futuro.

### 3.3 Decision de Diseño: Value.int con Wrapping (No Nuevos Value Constructores)

Mantener `Value.int : Int → Value` y wrappear en evaluación. **NO** crear `Value.uint32 : UInt32 → Value`.

**Razón**: Evita duplicar toda la infraestructura (evaluación, simulación, bridge, roundtrip). El wrapping se parametriza, el tipo de datos permanece igual.

**Fuente**: CompCert's `repr`/`unsigned` model — mathematical integers con wrapping at operation boundaries.

---

## 4. TEOREMAS CLAVE DE MATHLIB / LEAN 4 CORE

### 4.1 Para Task 1 (Bitwise BinOps)

**Evaluación de bitwise sobre Int** (Lean usa two's complement infinito):

| Lemma | Uso |
|-------|-----|
| `Int.testBit_land` | `(m.land n).testBit k = (m.testBit k && n.testBit k)` |
| `Int.testBit_lor` | `(m.lor n).testBit k = (m.testBit k \|\| n.testBit k)` |
| `Int.testBit_lxor` | `(m.xor n).testBit k = (m.testBit k ^^ n.testBit k)` |

**Evaluación de bitwise sobre Nat** (más lemmas disponibles):

| Lemma | Uso |
|-------|-----|
| `Nat.and_comm` | Commutativity of AND |
| `Nat.or_comm` | Commutativity of OR |
| `Nat.xor_comm` | Commutativity of XOR |
| `Nat.and_or_distrib_left` | `x &&& (y \|\|\| z) = (x &&& y) \|\|\| (x &&& z)` |
| `Nat.shiftLeft_eq` | `a <<< b = a * 2 ^ b` |
| `Nat.shiftRight_eq_div_pow` | `m >>> n = m / 2 ^ n` |
| `Nat.shiftRight_le` | `m >>> n ≤ m` — range preservation |
| `Nat.and_two_pow` | Bit extraction pattern |

**Insight crítico**: `Int.land` en Lean opera sobre two's complement infinito. Para unsigned (valores no-negativos), `Int.land a b` cuando `a ≥ 0 ∧ b ≥ 0` es equivalente a `Nat.land a.toNat b.toNat`. Esto simplifica enormemente los proofs de agreement.

### 4.2 Para Task 2 (UInt32/UInt64 Wrapping)

| Lemma | Uso |
|-------|-----|
| `Int.emod_nonneg` | `b ≠ 0 → 0 ≤ a % b` — wrapUInt siempre non-negative |
| `Int.emod_lt` | `b ≠ 0 → a % b < b` — wrapUInt siempre < 2^width |
| `Int.emod_eq_of_lt` | `0 ≤ a → a < b → a % b = a` — identity on in-range values |
| `Int.emod_add_emod_left` | `(a + b) % c = (a % c + b) % c` — wrapping addition |
| `Int.emod_sub_emod` | `(a - b) % c = (a % c - b % c) % c` — wrapping subtraction |
| `Int.emod_mul_bmod` | `(a * b) % c = (a % c * b) % c` — wrapping multiplication |
| `Int.toNat_emod` | Bridge Int wrapping ↔ Nat mod |
| `Nat.mod_mul_right_mod` | `a % (b * c) % b = a % b` — truncation proofs |

### 4.3 Para Task 4 (Bridge Modular)

| Lemma | Uso |
|-------|-----|
| `ZMod.intCast_eq_intCast_iff'` | `cast a = cast b ↔ a % c = b % c` |
| `ZMod.val_add` | `(a + b).val = (a.val + b.val) % n` |
| `ZMod.val_mul` | `(a * b).val = (a.val * b.val) % n` |
| `Int.ModEq.add/mul/sub` | Congruence preservation |
| `Int.mod_modEq` | `a % n ≡ a [ZMOD n]` |

### 4.4 BitVec — Alternativa Futura

`BitVec w` wraps `Fin (2^w)`. Tiene ALL algebraic properties + `bv_decide` tactic. Si Trust-Lean algún día refactoriza Value para incluir width information, `BitVec` es el modelo natural.

Lemmas disponibles: `BitVec.toNat_add`, `toNat_mul`, `toNat_and`, `toNat_or`, `toNat_xor`, `toNat_shiftLeft`, `toNat_ushiftRight`, plus `and_comm`, `or_comm`, `xor_comm`, `and_assoc`, etc. — todo gratis.

Para v3.1: NO refactorizar a BitVec (demasiado invasivo). Usar `Int.emod` + Nat bitwise lemmas.

---

## 5. LECCIONES APRENDIDAS APLICABLES

### 5.1 Evaluador y Wrapping

- **L-626**: Wrappear en operation boundaries, NO en storage/retrieval. Literals y variable refs retornan unwrapped.
- **L-620**: Wrapping arithmetic es total. `addInt64 a 0 = wrapInt64 a` sin precondiciones.
- **L-630**: Split agreement en incondicional (comparison/logical/bitwise) y condicional (arithmetic).
- **L-625**: Fuel monotonicity para nuevo evaluador sigue estructura idéntica al existente.
- **L-632**: `cases op <;> cases v1 <;> cases v2 <;> simp_all [defs...]` para agreement sobre enums finitos.

### 5.2 Arquitectura de Extensión

- **L-659**: Extension-only architecture. Nuevos archivos, mínimas modificaciones a existentes.
- **L-655**: Inducción estructural + while helper para equivalencia call-free.
- **L-657**: Lifting lemma evita duplicar simulation proof de 300+ LOC.
- **L-577**: Dedicated `@[simp]` lemmas por constructor hacen proofs robustos.
- **L-580**: Desugaring for→seq+while a nivel AST elimina caso for de fuel mono.

### 5.3 Parser/Roundtrip

- **L-607/L-611**: NoLeading predicates para parser exactness.
- **L-669/L-673**: ExprSafe predicate para roundtrip composicional.
- **L-670**: NegLitDisam para negative literals.
- **L-677**: `call_combined_bound` para fuel bounds sobre argument lists.

### 5.4 Field Arithmetic

- **L-198**: `2*ORDER < UInt.size` check obligatorio al portar entre UInt32/UInt64.
- **L-202**: Pattern replication entre finite fields: 80% mecánico si `toZMod` está en place.
- **L-573**: `ZMod.natCast_mod`, `ZMod.pow_card_sub_one_eq_one` (Fermat) útiles para bridge.
- **L-685**: Sin Mathlib, manual cast lemmas: `Int.ofNat_add`, `Int.ofNat_mul`.

---

## 6. BIBLIOGRAFÍA ANALIZADA

### 6.1 Tier 1 — Must-Read (Técnicas directamente aplicables)

| Paper | Técnica Clave | Aplicación v3.1 |
|-------|--------------|-----------------|
| **Fiat-Crypto** (Erbsen et al., S&P 2019) | Parametrización sobre word width via typeclass | `IntModel` pattern para evaluador genérico |
| **CompCert** (Leroy, CACM 2009/2016) | Forward simulation + `repr`/`unsigned` integer model | Template para `stmtToMicroC_correct_uint32/64` |
| **Trieu NTT** (2025, Rocq) | Montgomery + Barrett reduction verificados | Bridge proofs para BabyBear monty_reduce |
| **Scott NTT** | Excess tracking para overflow analysis | Proofs de rango en bitwise ops |
| **Navas et al.** | Interval abstract domain para shifts + bit-masks | Template para `evalMicroCBinOp_uint32_agree` |
| **Bhat et al. LeanMLIR** (ITP 2024) | `BitVec w` formalization en Lean 4 | Referencia para bitvector rewrite proofs |
| **Blazy & Leroy Clight** (JAR 2009) | Signed/unsigned integer model con `sem_cast` | Cast semantics para widen/trunc |

### 6.2 Tier 2 — Architecture Patterns

| Paper | Técnica Clave |
|-------|--------------|
| **Leroy Mechanized Semantics** (2010) | Forward simulation IMP → VM con fuel |
| **Affeldt Monadic Effects** (Coq, 2019) | Packed classes + equational reasoning |
| **HELIX** (Zaliva & Franchetti, 2018) | Translation validation functional → imperative |
| **Krebbers CH2O** (2015) | C11 integer representations + undefined behavior |

### 6.3 Gaps en Bibliografía

- **Jasmin/Kyber Episode IV** (Almeida et al., TCHES 2023) — No encontrado en biblioteca. Técnica clave: per-function refinement.
- **Montgomery Multiplication Verified** (Affeldt et al., ITP 2018) — 96 lemmas. No indexado separadamente.

---

## 7. TEOREMAS REUTILIZABLES DE LIBRERÍAS INTERNAS

### 7.1 Alta Prioridad

| Teorema | Librería | Path | Aplicación |
|---------|----------|------|------------|
| `foldl_inv_extends` | ProofKit | `ProofKit/Foldl.lean:25` | Thread unsigned wrapping bounds a través de statement sequences |
| `foldl_pair_inv_extends` | ProofKit | `ProofKit/Foldl.lean:42` | Pair state (env + state) threading |
| `Pattern.eval_ext` | OptiSat | `LambdaSat/EMatchSpec.lean:116` | Extensionality of evaluation — template para agreement proofs |
| `Pattern.map_eval_ext` | OptiSat | `LambdaSat/EMatchSpec.lean:139` | Map-level evaluation agreement |
| `mapOption` + lemmas | VerifiedExtraction | `VerifiedExtraction/Greedy.lean:24-78` | Evaluate function call argument lists |
| `ExtractableSound` | VerifiedExtraction | `VerifiedExtraction/Greedy.lean:98` | Template para `evalStmt_correct_unsigned` |

### 7.2 Media Prioridad

| Teorema | Librería | Aplicación |
|---------|----------|------------|
| `noiseChain_mono` | VeriHE | Monotonicity proof template para wrapping bounds |
| `noiseAfter_le` | VeriHE | Per-operation bound preservation |
| `noiseChain_append` | VeriHE | List append composition para statement concatenation |
| `foldl_md_preserves` | LeanHash | Invariant propagation via foldl |
| `extractF_correct` | VerifiedExtraction | Fuel-based correctness proof strategy |
| `arith_extractable_sound` | VerifiedExtraction | Concrete instantiation reference |

### 7.3 Nota Importante

**Ninguna librería interna tiene teoremas sobre bitwise operations** (`land`, `lor`, `xor`, `shiftLeft`, `shiftRight`). Los proof patterns sí son transferibles (invariant threading, extensionality, fuel-based correctness), pero los lemmas bitwise deben venir de Lean core / Mathlib.

---

## 8. AMO-LEAN: SPECS QUE TRUST-LEAN v3.1 DEBE CONECTAR

### 8.1 Plonky3Field Typeclass

```lean
class Plonky3Field (F : Type) [Field F] where
  char : Nat
  char_prime : Nat.Prime char
  toZMod : F → ZMod char
  toZMod_injective : Function.Injective toZMod
  toZMod_add : ∀ a b, toZMod (a + b) = toZMod a + toZMod b
  toZMod_mul : ∀ a b, toZMod (a * b) = toZMod a * toZMod b
```

Instancias: Mersenne31Field, BabyBearField, GoldilocksField.

### 8.2 Teoremas AMO-Lean que Anclan el Bridge

| Teorema | Archivo | Statement |
|---------|---------|-----------|
| `plonky3_mul_refines` | Mersenne31TV.lean | `plonky3_mul a b = a * b` (from_u62 reduction = field mul) |
| `from_u62_val_mod` | Mersenne31TV.lean | `(from_u62 x hx).value.toNat = x % ORDER_NAT` |
| `two_pow_31_mod_p` | Mersenne31TV.lean | `2^31 % ORDER_NAT = 1` (Mersenne identity) |
| `bb_monty_roundtrip` | BabyBearTV.lean | `from_monty(monty_mul(to_monty a, to_monty b)) = (a * b) % P` |
| `monty_reduce_spec` | Montgomery.lean | `R * monty_reduce(x) ≡ x (mod p)` |
| `plonky3_reduce128_val` | GoldilocksTV.lean | `reduce128(x_lo, x_hi) = (x_lo + x_hi * 2^64) % P` |

### 8.3 Punto de Convergencia

El bridge theorem de Trust-Lean v3.1 debe tener la forma:

```lean
theorem reduce_mersenne31_microc_correct (env : MicroCEnv) (x : Nat)
    (hx : x < 2^62) (henv : env "x" = Value.int x) :
    ∃ env', evalMicroC_uint32 fuel env reduce_mersenne31_prog = some (.normal, env')
      ∧ env' "result" = Value.int (x % ORDER_NAT)
```

Esto conecta con AMO-Lean via `from_u62_val_mod`:
```
evalMicroC_uint32(reduce_prog) = x % P = (from_u62 x).value.toNat
```

---

## 9. PROOF PATTERNS CRÍTICOS PARA v3.1

### 9.1 Agreement para Bitwise (Incondicional)

```lean
-- Para unsigned (valores non-negative), bitwise ops son incondicionales:
theorem evalMicroCBinOp_uint32_agree_band (a b : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    evalMicroCBinOp_uint32 .band (.int a) (.int b) =
    some (.int (wrapUInt32 (Int.land a b)))

-- Key insight: Int.land on non-negative ints = Nat.land on their toNat
-- And: Nat.land a b ≤ min a b (AND never increases)
-- So: if a, b < 2^32, then Int.land a b < 2^32 → wrapUInt32 is identity
```

### 9.2 Wrapping Composition (CompCert Pattern)

```lean
-- THE fundamental property for all ops:
theorem wrap_binop_compose (op : BinOp) (a b : Int) (width : Nat) :
    wrapWidth width (evalOp op (wrapWidth width a) (wrapWidth width b)) =
    wrapWidth width (evalOp op a b)
-- Source: CompCert Integers.v — "repr(op(unsigned x, unsigned y)) = op_repr(x, y)"
```

### 9.3 Forward Simulation para Unsigned

```lean
-- Reuses 100% de la estructura de stmtToMicroC_correct:
theorem stmtToMicroC_correct_uint32
    (hinj : VarNameInjective) (hwf : WellFormedArrayBases stmt)
    (h : evalStmt fuel env stmt = some (oc, env'))
    (hb : microCBridge env mcEnv) (hoc : oc ≠ .outOfFuel)
    -- NEW: all values in env are in UInt32 range
    (hrange : ∀ v, InUInt32Range (env v)) :
    ∃ mcEnv', evalMicroC_uint32 fuel mcEnv (stmtToMicroC stmt) = some (oc, mcEnv')
      ∧ microCBridge env' mcEnv'
      ∧ ∀ v, InUInt32Range (mcEnv' v)

-- Si se parametriza con IntModel, esta proof se escribe UNA vez.
```

### 9.4 Per-Function Refinement (Jasmin/Kyber Pattern)

```
Spec (AMO-Lean): x % P = from_u62(x).value.toNat
                    ↕ from_u62_val_mod
Plonky3 (Rust):  reduce_64(x) = lo&P + hi + ... → MicroC manual translation
                    ↕ reduce_mersenne31_microc_correct
MicroC eval:     evalMicroC_uint32(prog, env) → result
                    ↕ stmtToMicroC_correct_uint32
Trust-Lean IR:   evalStmt(fuel, env, stmt) → result
```

---

## 10. RIESGOS IDENTIFICADOS Y MITIGACIONES

### 10.1 `Int.land` en Negative Numbers

**Riesgo**: Lean's `Int.land` opera en two's complement infinito. `Int.land (-1) x = x`.

**Mitigación**: Para unsigned evaluator, todos los valores son `≥ 0`. Agregar precondición `ha : 0 ≤ a` a bitwise agreement theorems. En esa condición, `Int.land` se reduce a `Nat.land` que tiene semántica clara.

### 10.2 Shift Amounts ≥ Bit Width

**Riesgo**: C99 dice undefined behavior para shifts ≥ width. Lean no tiene restricción.

**Mitigación**: Dos opciones:
1. Reducir shift amount mod width (como UInt32.shiftLeft en Lean): `a <<< (b % 32)`
2. Precondición `hshift : b < width` en agreement theorems

**Recomendación**: Opción 1 (match C implementation behavior, no UB).

### 10.3 Widening Multiplication

**Riesgo**: `u32 * u32 → u64` requiere computar en 64-bit, no en 32-bit. Si se wrappea en 32-bit antes de multiplicar, se pierden bits.

**Mitigación**: El programa MicroC debe hacer explicit widening ANTES de la multiplicación:
```c
int64_t wide_a = (int64_t)a;  // widen32to64
int64_t wide_b = (int64_t)b;  // widen32to64
int64_t product = wide_a * wide_b;  // 64-bit multiply
```
Trust-Lean modela esto con `UnaryOp.widen32to64` seguido de `evalMicroCBinOp_uint64 .mul`.

### 10.4 Parser/Printer para Nuevos Ops

**Riesgo**: Agregar 5 operators al parser podría romper roundtrip proofs (1620 LOC en RoundtripStmt.lean).

**Mitigación**:
- Extension-only: nuevos cases en match, no modifica existing cases
- Lean's exhaustivity checker fuerza cubrir nuevos constructores
- Roundtrip proofs existentes no se invalidan (solo se extienden)
- L-669: ExprSafe predicate se extiende automáticamente

---

## 11. DECISIONES DE DISEÑO CONSOLIDADAS

| Decision | Opción Elegida | Alternativa Rechazada | Razón |
|----------|---------------|----------------------|-------|
| Integer model | `Value.int : Int → Value` + wrapping | Nuevos constructores `Value.uint32/64` | Evita duplicar infraestructura (~3000 LOC) |
| Parametrización | `wrapWidth (w : Nat)` function | Full `IntModel` typeclass | Más simple, omega/emod lemmas directos |
| Bitwise sobre | `Int.land/lor/xor` (Lean core) | `BitVec w` como modelo base | Menor refactor; BitVec para v4.0 |
| Shift semantics | Reduce mod width | Precondición `b < width` | Matches C behavior, evita UB |
| 128-bit | Diferido a v3.2 | Hi/Lo splitting en v3.1 | Solo Goldilocks lo necesita |
| Agreement type | Incondicional para bitwise | Condicional con InRange | AND/OR/XOR nunca exceden inputs |
| Roundtrip | Extender parser/printer existente | Parser separado para bitwise | Mantiene roundtrip_master unified |

---

## 12. SMOKE TESTS Y NON-VACUITY REQUERIDOS

### 12.1 Bitwise Operations

```lean
-- AND masking (Mersenne31 pattern):
#eval wrapUInt32 (Int.land 0xFFFFFFFF 0x7FFFFFFF)  -- expect 0x7FFFFFFF

-- Shift right (bit splitting):
#eval wrapUInt32 (Int.shiftRight 0x100000000 31)  -- expect 2

-- XOR:
#eval wrapUInt32 (Int.xor 0xFF00FF00 0x0F0F0F0F)  -- expect 0xF00FF00F
```

### 12.2 Unsigned Wrapping

```lean
-- UInt32 overflow:
#eval wrapUInt32 (2^32 : Int)  -- expect 0
#eval wrapUInt32 (2^32 - 1 : Int)  -- expect 4294967295

-- UInt64 overflow:
#eval wrapUInt64 (2^64 : Int)  -- expect 0
```

### 12.3 Mersenne31 Reduce

```lean
-- from_u62 pattern:
def P : Nat := 2^31 - 1
#eval (100 * 200) % P  -- expect the reduced product
-- Must match: lo = (100*200) &&& P; hi = (100*200) >>> 31; result = lo + hi
```

### 12.4 BabyBear Montgomery

```lean
-- Roundtrip: to_monty → monty_mul → from_monty = plain mul % P
#eval let p := 2013265921; let R := 2^32
      let a := 42; let b := 99
      let a_m := (a * R) % p; let b_m := (b * R) % p
      -- monty_mul: monty_reduce(a_m * b_m)
      -- from_monty: monty_reduce(result)
      (a * b) % p  -- should match end-to-end
```

---

## 13. RESUMEN EJECUTIVO

Trust-Lean v3.1 es una **extensión puramente aditiva** (~750-850 LOC) que agrega:

1. **5 BinOp bitwise** (band, bor, bxor, bshl, bshr) — bajo riesgo, agreement incondicional
2. **Evaluador UInt32/UInt64** parametrizado por `wrapWidth` — reutiliza 100% de la infraestructura existente
3. **2 UnaryOp de casting** (widen32to64, trunc64to32) — semántica trivial: ambos son `% 2^32` en representación Int
4. **Bridge theorems** para Mersenne31 reduce y BabyBear monty_reduce — per-function refinement conectando evalMicroC con AMO-Lean specs

**Fundamento teórico sólido**: Fiat-Crypto (parametrización), CompCert (simulation + integer model), Jasmin (per-function refinement), 55 lecciones aplicables, ~60 Mathlib lemmas identificados.

**No hay blockers técnicos**. Todas las herramientas (Lean 4 bitwise ops, Int.emod lemmas, AMO-Lean specs) están disponibles y probadas.
