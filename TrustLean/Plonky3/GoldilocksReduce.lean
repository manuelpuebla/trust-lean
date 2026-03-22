/-
  Trust-Lean — Goldilocks Pseudo-Mersenne Reduce Bridge
  MicroC program for Goldilocks reduction + correctness.

  Goldilocks prime: P = 2^64 - 2^32 + 1 = 18446744069414584321
  Pseudo-Mersenne identity: 2^64 ≡ C (mod P), where C = 2^32 - 1 = 4294967295.

  Two-fold specification (pure Nat):
    -- First fold: split x into lo64 + hi64 * C
    -- Second fold: split sum1 into lo2 + hi2 * C
    -- Conditional subtract for canonical representative

  MicroC program: models the final conditional subtract stage for values < 2*P.
  The uint64 evaluator's shift-by-64 modular behavior (64 % 64 = 0) prevents
  modeling the full 128-bit fold in MicroC. The algebraic spec handles all inputs.

  Correctness: goldilocks_reduce_spec x = x % P for x < 2^128.
-/
import TrustLean.MicroC.UnsignedEval

set_option autoImplicit false

namespace TrustLean

/-! ## Goldilocks Constants -/

/-- Goldilocks prime: P = 2^64 - 2^32 + 1 = 18446744069414584321 -/
def goldilocks_P : Nat := 18446744069414584321

/-- Goldilocks pseudo-Mersenne constant: C = 2^32 - 1 = 4294967295.
    The identity is: 2^64 ≡ C (mod P), so x = lo + hi * 2^64 ≡ lo + hi * C (mod P). -/
def goldilocks_C : Nat := 4294967295

/-- Goldilocks P as Int (for MicroC programs). -/
def goldilocks_P_int : Int := 18446744069414584321

/-! ## Goldilocks Identity Verification -/

/-- P = 2^64 - 2^32 + 1 -/
example : goldilocks_P = 2^64 - 2^32 + 1 := by native_decide

/-- C = 2^32 - 1 -/
example : goldilocks_C = 2^32 - 1 := by native_decide

/-- Key pseudo-Mersenne identity: 2^64 ≡ C (mod P).
    This justifies the fold: x = lo + hi * 2^64 ≡ lo + hi * C (mod P). -/
example : 2^64 % goldilocks_P = goldilocks_C := by native_decide

/-- P value check -/
example : goldilocks_P = 18446744069414584321 := by native_decide

/-- C^2 < P: ensures second fold's product doesn't need a third fold. -/
example : goldilocks_C * goldilocks_C < goldilocks_P := by native_decide

/-! ## Formal Algebraic Specification -/

/-- Pure mathematical specification of Goldilocks two-fold pseudo-Mersenne reduction.
    Computes x % P using the identity 2^64 ≡ C (mod P):
    - First fold: split x into lo (low 64 bits) and hi (remaining bits),
      compute sum1 = lo + hi * C
    - Second fold: split sum1 into lo2 (low 64 bits) and hi2 (remaining),
      compute sum2 = lo2 + hi2 * C
    - Conditional subtract for canonical representative in [0, P)

    Two folds suffice for x < 2^128 because:
    - After first fold: sum1 < 2^64 + 2^64 * (2^32 - 1) = 2^96
    - After second fold: sum2 < 2^64 + (2^32 - 1)^2 < 2^65 - 2^33 < 2*P -/
def goldilocks_reduce_spec (x : Nat) : Nat :=
  let P := goldilocks_P
  let C := goldilocks_C
  -- First fold
  let lo := x % 2^64
  let hi := x / 2^64
  let sum1 := lo + hi * C
  -- Second fold
  let lo2 := sum1 % 2^64
  let hi2 := sum1 / 2^64
  let sum2 := lo2 + hi2 * C
  -- Conditional subtract
  if sum2 ≥ P then sum2 - P else sum2

/-- The pseudo-Mersenne identity: 2^64 % P = C. -/
theorem goldilocks_two_pow_mod : 2^64 % goldilocks_P = goldilocks_C := by native_decide

/-- Key algebraic lemma: a single fold preserves the residue mod P.
    Proof uses: x = lo + hi * 2^64 = lo + hi * (P + C) = lo + hi*C + hi*P,
    so x mod P = (lo + hi*C) mod P. -/
theorem goldilocks_fold_preserves_mod (x : Nat) :
    (x % 2^64 + x / 2^64 * 4294967295) % 18446744069414584321 =
    x % 18446744069414584321 := by
  omega

/-- The two-fold specification is correct for x < 2^128:
    goldilocks_reduce_spec x = x % P.

    Proof strategy:
    1. Each fold preserves x mod P (goldilocks_fold_preserves_mod)
    2. For x < 2^128, two folds produce sum2 < 2*P
    3. Conditional subtract on [0, 2*P) gives canonical representative -/
theorem goldilocks_reduce_spec_correct (x : Nat) (hx : x < 2^128) :
    goldilocks_reduce_spec x = x % goldilocks_P := by
  unfold goldilocks_reduce_spec goldilocks_P goldilocks_C
  simp only []
  have : x / 2^64 < 2^64 := by omega
  have : x % 2^64 < 2^64 := by omega
  have h_sum1_bound : x % 2^64 + x / 2^64 * 4294967295 < 2^96 := by omega
  have : (x % 2^64 + x / 2^64 * 4294967295) / 2^64 < 2^32 := by omega
  split <;> omega

/-- The spec matches concrete values (bridge tests). -/
example : goldilocks_reduce_spec 0 = 0 := by native_decide
example : goldilocks_reduce_spec 42 = 42 := by native_decide
example : goldilocks_reduce_spec (goldilocks_P - 1) = goldilocks_P - 1 := by native_decide
example : goldilocks_reduce_spec goldilocks_P = 0 := by native_decide
example : goldilocks_reduce_spec (goldilocks_P + 1) = 1 := by native_decide
example : goldilocks_reduce_spec (2^64) = goldilocks_C := by native_decide
example : goldilocks_reduce_spec (2^64 + 42) = goldilocks_C + 42 := by native_decide
example : goldilocks_reduce_spec (2^80 + 7) = (2^80 + 7) % goldilocks_P := by native_decide

/-! ## MicroC Program — Conditional Subtract -/

/-- MicroC program for Goldilocks conditional subtract (final reduction stage).

    For values already in [0, 2*P), produces the canonical representative in [0, P).
    This models the final stage of Goldilocks reduction after the two-fold
    has brought the value below 2*P.

    The full 128-bit fold cannot be modeled in the uint64 MicroC evaluator because
    the shift-by-64 instruction wraps (64 % 64 = 0, standard hardware behavior).
    The algebraic spec (goldilocks_reduce_spec) handles the full fold.

    Input: env "x" contains a value in [0, 2*P).
    Output: env "result" contains x % P. -/
def reduce_goldilocks_prog : MicroCStmt :=
  .seq (.ite (.binOp .ltOp (.litInt (goldilocks_P_int - 1)) (.varRef "x"))
          (.assign "result" (.binOp .sub (.varRef "x") (.litInt goldilocks_P_int)))
          (.assign "result" (.varRef "x")))
       .skip

/-! ## Correctness Smoke Tests — Conditional Subtract -/

/-- Reduce 0: result = 0 -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int 0 else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_goldilocks_prog
        pure (e "result")) = some (.int 0) := by native_decide

/-- Reduce 1: result = 1 -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int 1 else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_goldilocks_prog
        pure (e "result")) = some (.int 1) := by native_decide

/-- Reduce 42: result = 42 (already < P) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int 42 else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_goldilocks_prog
        pure (e "result")) = some (.int 42) := by native_decide

/-- Reduce P - 1: result = P - 1 (already < P) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (goldilocks_P_int - 1) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_goldilocks_prog
        pure (e "result")) = some (.int (goldilocks_P_int - 1)) := by native_decide

/-- Reduce P: result = 0 (P mod P = 0) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int goldilocks_P_int else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_goldilocks_prog
        pure (e "result")) = some (.int 0) := by native_decide

/-- Reduce P + 1: result = 1 -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (goldilocks_P_int + 1) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_goldilocks_prog
        pure (e "result")) = some (.int 1) := by native_decide

/-- Reduce 2*P - 1: result = P - 1 (largest valid input for conditional subtract) -/
example :
    let env : MicroCEnv := fun s => if s == "x" then .int (2 * goldilocks_P_int - 1) else .int 0
    (do let (_, e) ← evalMicroC_uint64 20 env reduce_goldilocks_prog
        pure (e "result")) = some (.int (goldilocks_P_int - 1)) := by native_decide

/-! ## Verify Modular Arithmetic Consistency -/

example : (0 : Int) % goldilocks_P_int = 0 := by native_decide
example : (1 : Int) % goldilocks_P_int = 1 := by native_decide
example : (42 : Int) % goldilocks_P_int = 42 := by native_decide
example : (goldilocks_P_int - 1) % goldilocks_P_int = goldilocks_P_int - 1 := by native_decide
example : goldilocks_P_int % goldilocks_P_int = 0 := by native_decide
example : (goldilocks_P_int + 1) % goldilocks_P_int = 1 := by native_decide
example : (2^64 : Int) % goldilocks_P_int = (goldilocks_C : Int) := by native_decide

/-! ## Key Algebraic Identities -/

/-- 2^64 ≡ C (mod P): the pseudo-Mersenne identity -/
example : (2^64 : Int) % goldilocks_P_int = (goldilocks_C : Int) := by native_decide

/-- P = 2^64 - 2^32 + 1 is the Goldilocks prime -/
example : goldilocks_P = 2^64 - 2^32 + 1 := by native_decide

/-- C^2 < P: key property ensuring two folds suffice -/
example : goldilocks_C * goldilocks_C < goldilocks_P := by native_decide

/-- 2*P - 1 < 2^65: confirms conditional subtract result fits in 64 bits -/
example : 2 * goldilocks_P - 1 < 2^65 := by native_decide

end TrustLean
