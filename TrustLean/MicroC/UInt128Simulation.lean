/-
  Trust-Lean v4.1.0 — UInt128 Simulation (Lifting Pattern)
  N27.5: PARALELO — re-export key theorems + end-to-end smoke tests.

  The unsigned uint128 evaluator is independently correct:
  1. **Fuel monotonicity** proven (UInt128FuelMono.lean)
  2. **Op-level agreement** proven (UInt128Agreement.lean) — non-shift ops unconditional,
     shift ops conditional on modulus match (b.toNat < 64)
  3. **Translation unchanged**: stmtToMicroC is the same function

  The formal guarantee:
  - stmtToMicroC_correct: evalStmt ≈ evalMicroC (unbounded)
  - evalMicroC_uint128_fuel_mono_full: fuel monotonicity for wrapping evaluator
  - evalMicroCBinOp_uint128_agree_nonshift: per-op agreement when values in range
  These compose: for in-range programs, evalStmt ≈ evalMicroC ≈ evalMicroC_uint128.
-/
import TrustLean.MicroC.UInt128Agreement
import TrustLean.MicroC.UInt128FuelMono
import TrustLean.MicroC.Simulation

set_option autoImplicit false

namespace TrustLean

-- Re-export key theorems for easy access
#check @stmtToMicroC_correct
#check @evalMicroC_uint128_fuel_mono_full
#check @evalMicroCBinOp_uint128_agree_nonshift
#check @evalMicroCBinOp_uint128_agree_add
#check @evalMicroCBinOp_uint128_agree_mul
#check @evalMicroCUnaryOp_uint128_agree

/-! ## Smoke Tests: End-to-End UInt128 Evaluation -/

/-- Goldilocks conditional subtract via evalMicroC_uint128 (same as GoldilocksReduce.lean) -/
example :
    let P := (18446744069414584321 : Int)
    let env : MicroCEnv := fun s => if s == "x" then .int 0 else .int 0
    (do let (_, e) ← evalMicroC_uint128 20 env
          (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "x"))
                  (.assign "result" (.binOp .sub (.varRef "x") (.litInt P)))
                  (.assign "result" (.varRef "x")))
               .skip)
        pure (e "result")) = some (.int 0) := by native_decide

/-- 128-bit arithmetic: large product that fits -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .mul (.litInt (2^64 - 1)) (.litInt 42)))
        pure (e "x")) = some (.int ((2^64 - 1) * 42)) := by native_decide

/-- Shift boundary: x = 1 << 127 in uint128 mode -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .bshl (.litInt 1) (.litInt 127)))
        pure (e "x")) = some (.int (2^127)) := by native_decide

/-- Key for Goldilocks fold: shift-by-64 works correctly in uint128 -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "hi" (.binOp .bshr (.litInt (2^64 + 42)) (.litInt 64)))
        pure (e "hi")) = some (.int 1) := by native_decide

/-- Backward compat: Mersenne31 reduce pattern works in uint128 mode -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.seq (.assign "lo" (.binOp .band (.litInt (2^31 + 42)) (.litInt 0x7FFFFFFF)))
          (.seq (.assign "hi" (.binOp .bshr (.litInt (2^31 + 42)) (.litInt 31)))
                (.assign "sum" (.binOp .add (.varRef "lo") (.varRef "hi")))))
        pure (e "sum")) = some (.int 43) := by native_decide

/-- While loop: sum 0..2 produces 3 in uint128 mode -/
example :
    let body := MicroCStmt.seq
      (.assign "sum" (.binOp .add (.varRef "sum") (.varRef "i")))
      (.assign "i" (.binOp .add (.varRef "i") (.litInt 1)))
    let loop := MicroCStmt.while_ (.binOp .ltOp (.varRef "i") (.litInt 3)) body
    let init := MicroCStmt.seq (.assign "sum" (.litInt 0))
                (.seq (.assign "i" (.litInt 0)) loop)
    (do let (_, e) ← evalMicroC_uint128 20 MicroCEnv.default init
        pure (e "sum")) = some (.int 3) := by native_decide

end TrustLean
