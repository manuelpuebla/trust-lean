/-
  Trust-Lean v3.1 — Integration Tests + Smoke Tests
  Bitwise ops, casting, unsigned wrapping, Plonky3 field bridges.

  Phase 1: Bitwise + Casting extension smoke tests.
  Phase 2: Unsigned evaluator tests (added later).
  Phase 3: Plonky3 field bridge tests (added later).
-/
import TrustLean.MicroC.Int64Eval
import TrustLean.MicroC.Int64Agreement
import TrustLean.MicroC.Roundtrip

set_option autoImplicit false

namespace TrustLean

/-! ## Phase 1: Bitwise + Casting Smoke Tests -/

/-! ### BinOp evaluation smoke tests -/

-- Bitwise AND: 0xFF & 0x0F = 0x0F
#eval evalBinOp .band (.int 0xFF) (.int 0x0F)
-- expect: some (Value.int 15)

-- Bitwise OR: 0xF0 | 0x0F = 0xFF
#eval evalBinOp .bor (.int 0xF0) (.int 0x0F)
-- expect: some (Value.int 255)

-- Bitwise XOR: 0xFF ^ 0x0F = 0xF0
#eval evalBinOp .bxor (.int 0xFF) (.int 0x0F)
-- expect: some (Value.int 240)

-- Left shift: 1 << 10 = 1024
#eval evalBinOp .bshl (.int 1) (.int 10)
-- expect: some (Value.int 1024)

-- Right shift: 1024 >> 3 = 128
#eval evalBinOp .bshr (.int 1024) (.int 3)
-- expect: some (Value.int 128)

-- Mersenne masking: x & 0x7FFFFFFF (low 31 bits of 2^31 + 42)
#eval evalBinOp .band (.int (2^31 + 42)) (.int 0x7FFFFFFF)
-- expect: some (Value.int 42)

-- Bit splitting: (2^31 + 42) >> 31 = 1
#eval evalBinOp .bshr (.int (2^31 + 42)) (.int 31)
-- expect: some (Value.int 1)

/-! ### UnaryOp casting smoke tests -/

-- widen32to64: value in range is identity
#eval evalUnaryOp .widen32to64 (.int 42)
-- expect: some (Value.int 42)

-- widen32to64: value >= 2^32 gets truncated
#eval evalUnaryOp .widen32to64 (.int (2^32 + 7))
-- expect: some (Value.int 7)

-- trunc64to32: keep low 32 bits
#eval evalUnaryOp .trunc64to32 (.int (2^32 + 99))
-- expect: some (Value.int 99)

-- trunc64to32: value in range is identity
#eval evalUnaryOp .trunc64to32 (.int 12345)
-- expect: some (Value.int 12345)

/-! ### Int64 evaluator bitwise smoke tests -/

-- Int64 bitwise AND
#eval evalMicroCBinOp_int64 .band (.int 0xFF) (.int 0x0F)
-- expect: some (Value.int 15)

-- Int64 left shift
#eval evalMicroCBinOp_int64 .bshl (.int 3) (.int 4)
-- expect: some (Value.int 48)

-- Int64 casting
#eval evalMicroCUnaryOp_int64 .widen32to64 (.int 42)
-- expect: some (Value.int 42)

#eval evalMicroCUnaryOp_int64 .trunc64to32 (.int (2^32 + 7))
-- expect: some (Value.int 7)

/-! ### Statement-level bitwise evaluation -/

/-- Smoke test: x = 0xFF & 0x0F produces x = 15 -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.assign "x" (.binOp .band (.litInt 0xFF) (.litInt 0x0F)))
        pure (e "x")) = some (.int 15) := by native_decide

/-- Smoke test: x = 8 >> 2 produces x = 2 -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.assign "x" (.binOp .bshr (.litInt 8) (.litInt 2)))
        pure (e "x")) = some (.int 2) := by native_decide

/-- Smoke test: x = 3 << 4 produces x = 48 -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.assign "x" (.binOp .bshl (.litInt 3) (.litInt 4)))
        pure (e "x")) = some (.int 48) := by native_decide

/-- Smoke test: x = 7 ^ 3 produces x = 4 (XOR) -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.assign "x" (.binOp .bxor (.litInt 7) (.litInt 3)))
        pure (e "x")) = some (.int 4) := by native_decide

/-- Smoke test: cast (int32_t)(2^32 + 99) = 99 -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.assign "x" (.unaryOp .trunc64to32 (.litInt (2^32 + 99))))
        pure (e "x")) = some (.int 99) := by native_decide

/-- Smoke test: Mersenne masking then shift -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.seq (.assign "lo" (.binOp .band (.litInt (2^31 + 42)) (.litInt 0x7FFFFFFF)))
                (.assign "hi" (.binOp .bshr (.litInt (2^31 + 42)) (.litInt 31))))
        pure (e "lo", e "hi")) = some (.int 42, .int 1) := by native_decide

/-! ### Roundtrip smoke tests for new ops -/

/-- Bitwise AND expression roundtrips -/
example : parseMicroCExpr (microCExprToString (.binOp .band (.varRef "x") (.varRef "y")))
    = some (.binOp .band (.varRef "x") (.varRef "y")) := by native_decide

/-- Left shift expression roundtrips -/
example : parseMicroCExpr (microCExprToString (.binOp .bshl (.varRef "a") (.varRef "b")))
    = some (.binOp .bshl (.varRef "a") (.varRef "b")) := by native_decide

/-- Right shift expression roundtrips -/
example : parseMicroCExpr (microCExprToString (.binOp .bshr (.varRef "a") (.varRef "b")))
    = some (.binOp .bshr (.varRef "a") (.varRef "b")) := by native_decide

/-- XOR expression roundtrips -/
example : parseMicroCExpr (microCExprToString (.binOp .bxor (.varRef "a") (.varRef "b")))
    = some (.binOp .bxor (.varRef "a") (.varRef "b")) := by native_decide

/-- OR expression roundtrips -/
example : parseMicroCExpr (microCExprToString (.binOp .bor (.varRef "a") (.varRef "b")))
    = some (.binOp .bor (.varRef "a") (.varRef "b")) := by native_decide

/-- Cast widen expression roundtrips -/
example : parseMicroCExpr (microCExprToString (.unaryOp .widen32to64 (.varRef "x")))
    = some (.unaryOp .widen32to64 (.varRef "x")) := by native_decide

/-- Cast trunc expression roundtrips -/
example : parseMicroCExpr (microCExprToString (.unaryOp .trunc64to32 (.varRef "x")))
    = some (.unaryOp .trunc64to32 (.varRef "x")) := by native_decide

/-! ### Regression: existing v3.0 tests still pass -/

/-- Regression: simple add still works -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
        pure (e "x")) = some (.int 7) := by native_decide

/-- Regression: Int64 overflow still wraps correctly -/
example :
    (do let (_, e) ← evalMicroC_int64 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt 9223372036854775807) (.litInt 1)))
        pure (e "x")) = some (.int (-9223372036854775808)) := by native_decide

end TrustLean
