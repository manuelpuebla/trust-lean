/-
  Trust-Lean v3.1 — BabyBear Montgomery Reduce Bridge
  N20.2: CRITICO — MicroC program for BabyBear Montgomery reduction + correctness.

  Models Plonky3's Montgomery REDC (monty-31/src/utils.rs:105-125):
    t = (x * MU) truncated to 32 bits       // t = (x * MU) % R
    u = t * P                                 // u = t * P (in 64-bit)
    q = ((x - u) >> 32) truncated to 32 bits // q = (x - u) / R
    if q >= P then q -= P                    // canonical representative

  Montgomery identity: (MU * P + 1) % R = 0, where R = 2^32.
  Correctness: R * result ≡ x (mod P).

  Connection to AMO-Lean: bb_monty_roundtrip proves
    from_monty(monty_mul(to_monty a, to_monty b)) = (a * b) % P
-/
import TrustLean.MicroC.UnsignedEval

set_option autoImplicit false

namespace TrustLean

/-! ## BabyBear Constants -/

/-- BabyBear prime: P = 2^31 - 2^27 + 1 = 2013265921 -/
def babyBear_P : Int := 2013265921

/-- Montgomery R = 2^32 -/
def babyBear_R : Int := 2^32

/-- Montgomery MU = P^(-1) mod R (the positive inverse) -/
def babyBear_MU : Int := 2281701377

/-- Montgomery MU_NEG = (-P^(-1)) mod R -/
def babyBear_MU_NEG : Int := 2013265919

/-! ## BabyBear Constant Theorems -/

/-- P = 2013265921 (BabyBear prime value). -/
theorem babyBear_P_val : babyBear_P = 2013265921 := by native_decide

/-- P = 15 * 2^27 + 1 (structural decomposition). -/
theorem babyBear_P_formula : babyBear_P = 15 * 2^27 + 1 := by native_decide

/-- P = 2^31 - 2^27 + 1 (alternative formula). -/
theorem babyBear_P_formula2 : babyBear_P = 2^31 - 2^27 + 1 := by native_decide

/-- R = 2^32 (Montgomery radix). -/
theorem babyBear_R_val : babyBear_R = 4294967296 := by native_decide

/-- R = 2^32 as a formula. -/
theorem babyBear_R_formula : babyBear_R = 2^32 := by native_decide

/-- MU is the modular inverse of P mod R: (MU * P) % R = 1. -/
theorem babyBear_MU_inverse : (babyBear_MU * babyBear_P) % babyBear_R = 1 := by native_decide

/-- MU value: 2281701377. -/
theorem babyBear_MU_val : babyBear_MU = 2281701377 := by native_decide

/-- MU + MU_NEG = R (they are complementary mod R). -/
theorem babyBear_MU_complement : babyBear_MU + babyBear_MU_NEG = babyBear_R := by native_decide

/-- MU_NEG value: 2013265919. -/
theorem babyBear_MU_NEG_val : babyBear_MU_NEG = 2013265919 := by native_decide

/-- MU_NEG is the negated inverse: (MU_NEG * P + 1) % R = 0. -/
theorem babyBear_MU_NEG_identity :
    (babyBear_MU_NEG * babyBear_P + 1) % babyBear_R = 0 := by native_decide

/-! ## Montgomery Identity Verification -/

/-- Key Montgomery identity: (MU_NEG * P + 1) % R = 0 -/
example : (babyBear_MU_NEG * babyBear_P + 1) % babyBear_R = 0 := by native_decide

/-- Alternative: (MU * P) % R = 1 (MU is the positive inverse) -/
example : (babyBear_MU * babyBear_P) % babyBear_R = 1 := by native_decide

/-- P value check -/
example : babyBear_P = 2013265921 := by native_decide

/-- P = 2^31 - 2^27 + 1 -/
example : babyBear_P = 2^31 - 2^27 + 1 := by native_decide

/-! ## Montgomery Reduce Program -/

/-- MicroC program for BabyBear Montgomery reduction (addition variant).
    Input: env "x" contains the value to reduce (assumes 0 ≤ x < R * P).
    Output: env "result" contains monty_reduce(x).

    Algorithm (REDC addition variant):
    1. t = (x * MU_NEG) & 0xFFFFFFFF   // t = (x * MU_NEG) % R (truncate to 32 bits)
    2. u = t * P                         // u = t * P (in 64-bit)
    3. s = x + u                         // s = x + u (divisible by R)
    4. q = s >> 32                       // q = s / R
    5. if q >= P then q -= P             // canonical representative
    6. result = q -/
def monty_reduce_prog : MicroCStmt :=
  .seq (.assign "t" (.binOp .band
        (.binOp .mul (.varRef "x") (.litInt babyBear_MU_NEG))
        (.litInt 0xFFFFFFFF)))
  (.seq (.assign "u" (.binOp .mul (.varRef "t") (.litInt babyBear_P)))
  (.seq (.assign "s" (.binOp .add (.varRef "x") (.varRef "u")))
  (.seq (.assign "q" (.binOp .bshr (.varRef "s") (.litInt 32)))
  (.seq (.ite (.binOp .ltOp (.litInt (babyBear_P - 1)) (.varRef "q"))
          (.assign "q" (.binOp .sub (.varRef "q") (.litInt babyBear_P)))
          .skip)
        (.assign "result" (.varRef "q"))))))

/-! ## Formal Algebraic Specification -/

/-- Pure mathematical specification of Montgomery reduction (addition variant).
    Given x, computes q such that R * q ≡ x (mod P), where R = 2^32.
    Algorithm:
    1. t = (x * MU_NEG) % R           -- key: t * P ≡ -x (mod R)
    2. u = t * P                        -- so x + u ≡ 0 (mod R)
    3. s = x + u                        -- s is divisible by R
    4. q = s / R                        -- exact division
    5. if q ≥ P then q - P else q       -- canonical representative -/
def monty_reduce_spec (x : Nat) : Nat :=
  let R := 2^32
  let P := 2013265921
  let MU_NEG := 2013265919
  let t := (x * MU_NEG) % R
  let u := t * P
  let s := x + u
  let q := s / R
  if q ≥ P then q - P else q

/-- Montgomery identity: MU_NEG * P + 1 is divisible by R. -/
theorem monty_identity : (2013265919 * 2013265921 + 1) % 2^32 = 0 := by native_decide

/-- The Montgomery spec satisfies R * result ≡ x (mod P) for valid inputs.
    This is the fundamental Montgomery reduction property. -/
theorem monty_reduce_spec_mod_correct (x : Nat) (hx : x < 2^32 * 2013265921) :
    (2^32 * monty_reduce_spec x) % 2013265921 = x % 2013265921 := by
  unfold monty_reduce_spec
  omega

/-- The spec is bounded: result < P for valid inputs. -/
theorem monty_reduce_spec_bounded (x : Nat) (hx : x < 2^32 * 2013265921) :
    monty_reduce_spec x < 2013265921 := by
  unfold monty_reduce_spec
  omega

/-- The spec matches concrete values. -/
example : monty_reduce_spec 0 = 0 := by native_decide
example : monty_reduce_spec (2^32) = 1 := by native_decide
example : monty_reduce_spec (42 * 2^32) = 42 := by native_decide

/-- Full roundtrip: to_monty(7) → monty_reduce → 7. -/
example : monty_reduce_spec ((7 * 2^32) % 2013265921) = 7 := by native_decide

/-- Full roundtrip: to_monty(99) → monty_reduce → 99. -/
example : monty_reduce_spec ((99 * 2^32) % 2013265921) = 99 := by native_decide

/-- Montgomery multiplication roundtrip: to_monty(7) * to_monty(6) → monty_reduce → monty_reduce → 42. -/
example :
    let P := 2013265921
    let R := 2^32
    let a_m := (7 * R) % P
    let b_m := (6 * R) % P
    let product := a_m * b_m
    let ab_monty := monty_reduce_spec product
    monty_reduce_spec ab_monty = 42 := by native_decide

/-! ## Correctness Smoke Tests -/

/-- monty_reduce(0) = 0 -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int 0 else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env monty_reduce_prog
        pure (e "result")) = some (.int 0) := by native_decide

/-- monty_reduce(P) — should give a valid result -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int babyBear_P else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env monty_reduce_prog
        pure (e "result")).isSome = true := by native_decide

/-- monty_reduce(R) — R mod P in Montgomery form -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int babyBear_R else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env monty_reduce_prog
        pure (e "result")) = some (.int 1) := by native_decide

/-- monty_reduce(42 * R) should give 42 (taking 42 out of Montgomery form) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (42 * babyBear_R) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env monty_reduce_prog
        pure (e "result")) = some (.int 42) := by native_decide

/-- Verify: R mod P (R = 2^32, P = 2013265921) -/
example : babyBear_R % babyBear_P = 2281701375 := by native_decide

/-- Verify: monty_reduce(42 * R) = 42, and R * 42 = 42 * R ≡ 42 * R (mod P) -/
example : (42 * babyBear_R) % babyBear_P = (babyBear_R * 42) % babyBear_P := by
  native_decide

/-! ## Full Montgomery Roundtrip Test -/

/-- to_monty(a) = (a * R) % P -/
def to_monty (a : Int) : Int := (a * babyBear_R) % babyBear_P

/-- to_monty(0) = 0 (zero maps to zero in Montgomery form). -/
theorem to_monty_zero : to_monty 0 = 0 := by native_decide

/-- to_monty(1) = R % P (one maps to R mod P in Montgomery form). -/
theorem to_monty_one : to_monty 1 = babyBear_R % babyBear_P := by native_decide

-- from_monty via monty_reduce: takes Montgomery form back to normal
-- We test the full roundtrip: to_monty → monty_mul → from_monty

/-- Roundtrip test: to_monty(7) → monty_reduce → should give 7 back

    to_monty(7) = (7 * R) % P
    monty_reduce(to_monty(7)) should = 7 -/
example :
    let a_monty := to_monty 7
    let env : MicroCEnv := fun s => if s == "x" then .int a_monty else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env monty_reduce_prog
        pure (e "result")) = some (.int 7) := by native_decide

/-- Roundtrip test: to_monty(99) → monty_reduce → should give 99 -/
example :
    let a_monty := to_monty 99
    let env : MicroCEnv := fun s => if s == "x" then .int a_monty else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env monty_reduce_prog
        pure (e "result")) = some (.int 99) := by native_decide

/-- Montgomery multiplication roundtrip: to_monty(7) * to_monty(6) → monty_reduce twice → 42
    Step 1: monty_reduce(to_monty(7) * to_monty(6)) gives a*b in Montgomery form
    Step 2: monty_reduce again gives plain 42 -/
example :
    let a_m := to_monty 7
    let b_m := to_monty 6
    let product := a_m * b_m
    let env1 : MicroCEnv := fun s => if s == "x" then .int product else .int 0
    -- We verify the two-step result equals 42 by computing the intermediate value
    -- and checking the second reduce
    let ab_monty := ((product * babyBear_MU_NEG) % babyBear_R * babyBear_P + product) / babyBear_R
    let ab_monty_canonical := if ab_monty ≥ babyBear_P then ab_monty - babyBear_P else ab_monty
    let env2 : MicroCEnv := fun s => if s == "x" then .int ab_monty_canonical else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env2 monty_reduce_prog
        pure (e "result")) = some (.int 42) := by native_decide

end TrustLean
