/-
  Trust-Lean — KoalaBear Pseudo-Mersenne Reduce Bridge
  MicroC program for KoalaBear two-fold reduction + correctness.

  Models Plonky3's pseudo-Mersenne reduction for KoalaBear (two-fold variant):
    -- First fold
    lo  = x & 0x7FFFFFFF       // low 31 bits
    hi  = x >> 31              // high bits
    prod = hi * C              // C = 2^24 - 1 = 16777215
    sum1 = lo + prod           // lo + hi * C ≡ x (mod P)
    -- Second fold
    lo2  = sum1 & 0x7FFFFFFF
    hi2  = sum1 >> 31
    prod2 = hi2 * C
    sum2 = lo2 + prod2         // sum2 ≡ sum1 ≡ x (mod P)
    -- Conditional subtract
    if (sum2 >= P) sum2 -= P   // canonical representative

  KoalaBear prime: P = 2^31 - 2^24 + 1 = 2130706433
  Pseudo-Mersenne identity: 2^31 ≡ C (mod P), where C = 2^24 - 1.

  Uses evalMicroC_uint64 (not uint32) because hi * C can exceed 2^32 for larger inputs.
  Two folds suffice for inputs < 2^44, bringing the value below 2*P.
-/
import TrustLean.MicroC.UnsignedEval

set_option autoImplicit false

namespace TrustLean

/-! ## KoalaBear Constants -/

/-- KoalaBear prime: P = 2^31 - 2^24 + 1 = 2130706433 -/
def koalaBear_P : Int := 2130706433

/-- KoalaBear pseudo-Mersenne constant: C = 2^24 - 1 = 16777215.
    The identity is: 2^31 ≡ C (mod P), so x = lo + hi * 2^31 ≡ lo + hi * C (mod P). -/
def koalaBear_C : Int := 16777215

/-- Mask for low 31 bits: 2^31 - 1 = 0x7FFFFFFF -/
def koalaBear_MASK31 : Int := 2147483647

/-! ## KoalaBear Identity Verification -/

/-- P = 2^31 - 2^24 + 1 -/
example : koalaBear_P = 2^31 - 2^24 + 1 := by native_decide

/-- C = 2^24 - 1 -/
example : koalaBear_C = 2^24 - 1 := by native_decide

/-- Key pseudo-Mersenne identity: 2^31 ≡ C (mod P).
    This justifies the fold: x = lo + hi * 2^31 ≡ lo + hi * C (mod P). -/
example : (2^31 : Int) % koalaBear_P = koalaBear_C := by native_decide

/-- P value check -/
example : koalaBear_P = 2130706433 := by native_decide

/-! ## KoalaBear Two-Fold Reduce Program -/

/-- MicroC program for KoalaBear two-fold pseudo-Mersenne reduction.
    Input: env "x" contains the value to reduce (assumes 0 ≤ x < 2^44).
    Output: env "result" contains x % P.

    Uses evalMicroC_uint64 because hi * C can exceed 2^32 for inputs > 2^39.
    Two folds bring x < 2^44 down to sum2 < 2*P, so one conditional subtract suffices.

    Algorithm:
    1. lo  = x & MASK31       (x % 2^31)
    2. hi  = x >> 31           (x / 2^31)
    3. prod = hi * C
    4. sum1 = lo + prod        (first fold: sum1 ≡ x mod P)
    5. lo2  = sum1 & MASK31
    6. hi2  = sum1 >> 31
    7. prod2 = hi2 * C
    8. sum2 = lo2 + prod2      (second fold: sum2 ≡ x mod P)
    9. if sum2 >= P then sum2 -= P
    10. result = sum2 -/
def reduce_koalabear_prog : MicroCStmt :=
  -- First fold
  .seq (.assign "lo" (.binOp .band (.varRef "x") (.litInt koalaBear_MASK31)))
  (.seq (.assign "hi" (.binOp .bshr (.varRef "x") (.litInt 31)))
  (.seq (.assign "prod" (.binOp .mul (.varRef "hi") (.litInt koalaBear_C)))
  (.seq (.assign "sum1" (.binOp .add (.varRef "lo") (.varRef "prod")))
  -- Second fold
  (.seq (.assign "lo2" (.binOp .band (.varRef "sum1") (.litInt koalaBear_MASK31)))
  (.seq (.assign "hi2" (.binOp .bshr (.varRef "sum1") (.litInt 31)))
  (.seq (.assign "prod2" (.binOp .mul (.varRef "hi2") (.litInt koalaBear_C)))
  (.seq (.assign "sum2" (.binOp .add (.varRef "lo2") (.varRef "prod2")))
  -- Conditional subtract
  (.seq (.ite (.binOp .ltOp (.litInt (koalaBear_P - 1)) (.varRef "sum2"))
          (.assign "sum2" (.binOp .sub (.varRef "sum2") (.litInt koalaBear_P)))
          .skip)
        (.assign "result" (.varRef "sum2"))))))))))

/-! ## Formal Algebraic Specification -/

/-- Pure mathematical specification of KoalaBear two-fold pseudo-Mersenne reduction.
    Computes x % P using the identity 2^31 ≡ C (mod P):
    - First fold: lo + hi * C where x = lo + hi * 2^31
    - Second fold: lo2 + hi2 * C where sum1 = lo2 + hi2 * 2^31
    - Conditional subtract for canonical representative in [0, P)

    Two folds suffice for x < 2^44: after the first fold, sum1 < 2^38;
    after the second fold, sum2 < 2^32 < 2*P. -/
def koalabear_reduce_spec (x : Nat) : Nat :=
  let P := 2130706433
  let C := 16777215
  -- First fold
  let lo := x % 2^31
  let hi := x / 2^31
  let sum1 := lo + hi * C
  -- Second fold
  let lo2 := sum1 % 2^31
  let hi2 := sum1 / 2^31
  let sum2 := lo2 + hi2 * C
  -- Conditional subtract
  if sum2 ≥ P then sum2 - P else sum2

/-- The pseudo-Mersenne identity: 2^31 % P = C. -/
theorem koalabear_two_pow_mod : 2^31 % 2130706433 = 16777215 := by native_decide

/-- Key algebraic lemma: a single fold preserves the residue mod P.
    Proof uses the identity: x = lo + hi * 2^31 = lo + hi * (P + C) = lo + hi*C + hi*P,
    so x mod P = (lo + hi*C) mod P. -/
theorem koalabear_fold_preserves_mod (x : Nat) :
    (x % 2^31 + x / 2^31 * 16777215) % 2130706433 = x % 2130706433 := by
  omega

/-- The two-fold specification is correct for x < 2^44:
    koalabear_reduce_spec x = x % P.

    Proof strategy:
    1. Each fold preserves x mod P (koalabear_fold_preserves_mod)
    2. For x < 2^44, two folds produce sum2 < 2*P
    3. Conditional subtract on [0, 2*P) gives canonical representative -/
theorem koalabear_reduce_spec_correct (x : Nat) (hx : x < 2^44) :
    koalabear_reduce_spec x = x % 2130706433 := by
  unfold koalabear_reduce_spec
  simp only []
  have : x / 2^31 < 8192 := by omega
  have : x % 2^31 < 2147483648 := by omega
  have h_sum1_bound : x % 2^31 + x / 2^31 * 16777215 < 139586428928 := by omega
  have : (x % 2^31 + x / 2^31 * 16777215) / 2^31 < 65 := by omega
  split <;> omega

/-- The spec matches concrete values (bridge tests). -/
example : koalabear_reduce_spec 0 = 0 := by native_decide
example : koalabear_reduce_spec 42 = 42 := by native_decide
example : koalabear_reduce_spec 2130706432 = 2130706432 := by native_decide  -- P - 1
example : koalabear_reduce_spec 2130706433 = 0 := by native_decide  -- P
example : koalabear_reduce_spec 2130706434 = 1 := by native_decide  -- P + 1
example : koalabear_reduce_spec (2^31) = 16777215 := by native_decide  -- 2^31 mod P = C
example : koalabear_reduce_spec (2^40 + 7) = 67108355 := by native_decide
example : koalabear_reduce_spec 3000000000 = 869293567 := by native_decide

/-! ## Correctness Smoke Tests -/

/-- Reduce 0: result = 0 -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int 0 else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int 0) := by native_decide

/-- Reduce 1: result = 1 (already < P) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int 1 else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int 1) := by native_decide

/-- Reduce P - 1: result = P - 1 (already < P) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (koalaBear_P - 1) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int (koalaBear_P - 1)) := by native_decide

/-- Reduce P: result = 0 (P mod P = 0) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int koalaBear_P else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int 0) := by native_decide

/-- Reduce P + 1: result = 1 -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (koalaBear_P + 1) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int 1) := by native_decide

/-- Reduce 2^31: result = C (pseudo-Mersenne identity) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (2^31) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int koalaBear_C) := by native_decide

/-- Reduce 2^40 + 7: tests two-fold reduction with large value -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (2^40 + 7) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int 67108355) := by native_decide

/-- Reduce multiplication result that exceeds P:
    50000 * 50000 = 2500000000 > P = 2130706433
    2500000000 % 2130706433 = 369293567 -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (50000 * 50000) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_koalabear_prog
        pure (e "result")) = some (.int 369293567) := by native_decide

/-! ## Verify Modular Arithmetic Consistency -/

example : (0 : Int) % koalaBear_P = 0 := by native_decide
example : (1 : Int) % koalaBear_P = 1 := by native_decide
example : (koalaBear_P - 1) % koalaBear_P = koalaBear_P - 1 := by native_decide
example : koalaBear_P % koalaBear_P = 0 := by native_decide
example : (koalaBear_P + 1) % koalaBear_P = 1 := by native_decide
example : (2^31 : Int) % koalaBear_P = koalaBear_C := by native_decide
example : (2^40 + 7 : Int) % koalaBear_P = 67108355 := by native_decide
example : (50000 * 50000 : Int) % koalaBear_P = 369293567 := by native_decide

/-! ## Key Algebraic Identities -/

/-- 2^31 ≡ C (mod P): the pseudo-Mersenne identity -/
example : (2^31 : Int) % koalaBear_P = koalaBear_C := by native_decide

/-- P = 2^31 - 2^24 + 1 is the KoalaBear prime -/
example : koalaBear_P = 2^31 - 2^24 + 1 := by native_decide

/-- MASK31 = 2^31 - 1 -/
example : koalaBear_MASK31 = 2^31 - 1 := by native_decide

end TrustLean
