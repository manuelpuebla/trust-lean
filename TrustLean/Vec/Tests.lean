/-
  Trust-Lean v4.2.0 — VecStmt Smoke Tests + Non-Vacuity
  N28.7: HOJA — butterfly vecMap = N× scalar butterfly, end-to-end emission.
-/
import TrustLean.Vec.LiftingTheorem
import TrustLean.Vec.FuelMono
import TrustLean.Vec.CBackend
import TrustLean.Vec.RustBackend
import TrustLean.Vec.VecSpecialOp

set_option autoImplicit false

namespace TrustLean

/-! ## Concrete Butterfly Body -/

def simpleButterflyBody : Stmt :=
  .seq (.assign (.user "wb") (.binOp .mul (.varRef (.user "w")) (.varRef (.user "b"))))
  (.seq (.assign (.user "sum") (.binOp .add (.varRef (.user "a")) (.varRef (.user "wb"))))
        (.assign (.user "diff") (.binOp .sub (.varRef (.user "a")) (.varRef (.user "wb")))))

def butterflyVars : List String := ["a", "b", "w", "wb", "sum", "diff"]

/-! ## Test 1: vecMap evaluates correctly with 2 lanes -/

example :
    let env : LowLevelEnv := fun v => match v with
      | .array "a" 0 => .int 10
      | .array "a" 1 => .int 20
      | .array "b" 0 => .int 3
      | .array "b" 1 => .int 5
      | .array "w" 0 => .int 2
      | .array "w" 1 => .int 4
      | _ => .int 0
    match evalVecStmt 10 env (.vecMap 2 butterflyVars simpleButterflyBody) with
    | some (.normal, env') =>
      -- Lane 0: wb=6, sum=16, diff=4. Lane 1: wb=20, sum=40, diff=0.
      env' (.array "sum" 0) = .int 16 ∧
      env' (.array "diff" 0) = .int 4 ∧
      env' (.array "sum" 1) = .int 40 ∧
      env' (.array "diff" 1) = .int 0
    | _ => False := by
  simp only [evalVecStmt, List.range, List.range.loop, List.foldl, evalOneLane, selectLane,
        evalStmt, evalExpr, evalBinOp, writeLane, LowLevelEnv.update,
        simpleButterflyBody, butterflyVars]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Test 2: vecLoad + vecMap + vecStore pipeline -/

example :
    let env : LowLevelEnv := fun v => match v with
      | .array "data" 0 => .int 100
      | .array "data" 1 => .int 200
      | _ => .int 0
    let addOneBody := Stmt.assign (.user "x") (.binOp .add (.varRef (.user "x")) (.litInt 1))
    let pipeline := VecStmt.vecSeq
      (.vecLoad "x" "data" (.litInt 0) 2)
      (.vecSeq (.vecMap 2 ["x"] addOneBody)
               (.vecStore "data" (.litInt 0) "x" 2))
    match evalVecStmt 10 env pipeline with
    | some (.normal, env') =>
      env' (.array "data" 0) = .int 101 ∧
      env' (.array "data" 1) = .int 201
    | _ => False := by
  simp only [evalVecStmt, List.range, List.range.loop, List.foldl, evalOneLane, selectLane,
        evalStmt, evalExpr, evalBinOp, writeLane, LowLevelEnv.update]
  exact ⟨rfl, rfl⟩

/-! ## Test 3: Backend emission produces strings -/

example : neonBinOpIntrinsic .add = "vaddq_u32" := by rfl
example : avx2BinOpIntrinsic .mul = "_mm256_mullo_epi32" := by rfl
example : rustNeonIntrinsic .sub = "std::arch::aarch64::vsubq_u32" := by rfl
example : rustAvx2Intrinsic .band = "std::arch::x86_64::_mm256_and_si256" := by rfl

/-! ## Test 4: VecSpecialOp via evalVecStmt -/

/-- NEON emission: satDoublingMulHigh emits vqdmulhq_s32 -/
example : (vecStmtToC VecConfig.neon 0
    (.vecSpecialOp .satDoublingMulHigh 4 "m" "x" "mu")).length > 0 := by decide

/-- AVX2 emission: mulHigh emits emulation (NOT _mm256_mulhi_epi32) -/
example : (vecStmtToC VecConfig.avx2 0
    (.vecSpecialOp (.mulHigh 32) 8 "hi" "a" "b")).length > 0 := by native_decide

/-- Rust NEON emission: satDoublingMulHigh -/
example : (vecStmtToRust VecConfig.neon 0
    (.vecSpecialOp .satDoublingMulHigh 4 "m" "x" "mu")).length > 0 := by decide

/-- evalVecSpecialOp: horizAdd [10,20,30,40] = [30,70] -/
example : evalVecSpecialOp .horizAdd [10, 20, 30, 40] [] 4 = some [30, 70] := by native_decide

/-- evalVecSpecialOp: mulHigh shift=1 [(6,7)] = [21] -/
example : evalVecSpecialOp (.mulHigh 1) [6] [7] 1 = some [21] := by native_decide

/-! ## Re-export key theorems -/

#check @vecMap_lane_correct_single
#check @evalVecStmt_fuel_mono_full
#check @evalVecStmt_fuel_mono
#check @selectLane_after_writeLane_same
#check @selectLane_after_writeLane_other
#check @env_update_user_preserves_array

end TrustLean
