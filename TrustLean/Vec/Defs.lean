/-
  Trust-Lean v4.2.0 — VecStmt Definitions
  N28.1: FUNDACIONAL — VecStmt, VecConfig, VecType, selectLane, writeLane, writesTo.

  SIMD wrapper layer over Stmt. Zero modifications to Core IR.
  Uses existing VarName.array for lane storage — no Value extension needed.

  Key insight: VarName.array "x" i for i ∈ 0..lanes represents SIMD lanes.
  selectLane/writeLane remap between scalar VarNames (user "x") and
  lane positions (array "x" i). The lifting theorem (LiftingTheorem.lean)
  proves that vecMap n body = n independent evalStmt calls.
-/
import TrustLean.Core.Stmt
import TrustLean.Vec.VecSpecialOp

set_option autoImplicit false

namespace TrustLean

/-! ## Vector Types and Configuration -/

/-- Lane element type. v4.2.0 focuses on u32; extensible to u64/f32. -/
inductive VecType where
  | u32 | u64
  deriving Repr, BEq, DecidableEq, Inhabited

/-- SIMD target configuration. -/
structure VecConfig where
  /-- Number of parallel lanes (4 for NEON, 8 for AVX2). -/
  lanes : Nat
  /-- Target backend: "neon", "avx2", or "scalar" (fallback). -/
  target : String
  /-- Element type per lane. -/
  vecType : VecType
  /-- Alignment hint for load/store (0 = natural). -/
  alignment : Nat := 0
  deriving Repr, Inhabited

/-- Standard NEON configuration: 4 × u32. -/
def VecConfig.neon : VecConfig :=
  { lanes := 4, target := "neon", vecType := .u32 }

/-- Standard AVX2 configuration: 8 × u32. -/
def VecConfig.avx2 : VecConfig :=
  { lanes := 8, target := "avx2", vecType := .u32 }

/-- Scalar fallback configuration. -/
def VecConfig.scalar (n : Nat) : VecConfig :=
  { lanes := n, target := "scalar", vecType := .u32 }

/-! ## Lane Selection / Write-Back -/

/-- Select lane `i` from the environment: remap `user name` → `array name i`
    for each name in `vars`. Non-listed variables pass through unchanged. -/
def selectLane (i : Int) (vars : List String) (env : LowLevelEnv) : LowLevelEnv :=
  fun v => match v with
    | .user name => if name ∈ vars then env (.array name i) else env v
    | _ => env v

/-- Write lane `i` results back: for each name in `vars`,
    write `laneEnv(user name)` to position `array name i` in the output env.
    Non-listed and non-matching positions pass through from `env`. -/
def writeLane (i : Int) (vars : List String) (laneEnv env : LowLevelEnv) : LowLevelEnv :=
  fun v => match v with
    | .array name idx => if name ∈ vars ∧ idx = i then laneEnv (.user name) else env v
    | _ => env v

/-! ## selectLane / writeLane Properties -/

@[simp] theorem selectLane_user_in (i : Int) (vars : List String) (env : LowLevelEnv)
    (name : String) (h : name ∈ vars) :
    selectLane i vars env (.user name) = env (.array name i) := by
  simp [selectLane, h]

@[simp] theorem selectLane_user_not_in (i : Int) (vars : List String) (env : LowLevelEnv)
    (name : String) (h : name ∉ vars) :
    selectLane i vars env (.user name) = env (.user name) := by
  simp [selectLane, h]

@[simp] theorem selectLane_temp (i : Int) (vars : List String) (env : LowLevelEnv) (n : Nat) :
    selectLane i vars env (.temp n) = env (.temp n) := by
  simp [selectLane]

@[simp] theorem selectLane_array (i : Int) (vars : List String) (env : LowLevelEnv)
    (name : String) (idx : Int) :
    selectLane i vars env (.array name idx) = env (.array name idx) := by
  simp [selectLane]

@[simp] theorem writeLane_array_match (i : Int) (vars : List String) (laneEnv env : LowLevelEnv)
    (name : String) (h : name ∈ vars) :
    writeLane i vars laneEnv env (.array name i) = laneEnv (.user name) := by
  simp [writeLane, h]

@[simp] theorem writeLane_array_other_lane (i j : Int) (vars : List String)
    (laneEnv env : LowLevelEnv) (name : String) (hij : j ≠ i) :
    writeLane i vars laneEnv env (.array name j) = env (.array name j) := by
  simp [writeLane]
  intro _ heq; exact absurd heq hij

@[simp] theorem writeLane_array_other_name (i : Int) (vars : List String)
    (laneEnv env : LowLevelEnv) (name : String) (h : name ∉ vars) :
    writeLane i vars laneEnv env (.array name i) = env (.array name i) := by
  simp [writeLane, h]

@[simp] theorem writeLane_user (i : Int) (vars : List String) (laneEnv env : LowLevelEnv)
    (name : String) :
    writeLane i vars laneEnv env (.user name) = env (.user name) := by
  simp [writeLane]

@[simp] theorem writeLane_temp (i : Int) (vars : List String) (laneEnv env : LowLevelEnv)
    (n : Nat) :
    writeLane i vars laneEnv env (.temp n) = env (.temp n) := by
  simp [writeLane]

/-! ## writesTo — Static Analysis of Modified VarNames -/

/-- Compute the set of VarNames that a Stmt may modify.
    Conservative: over-approximation is sound (may include vars that are
    conditionally written). Uses List for simplicity (no Finset import). -/
def writesTo : Stmt → List VarName
  | .assign v _ => [v]
  | .store _ _ _ => []  -- store modifies array positions, not tracked by VarName.user
  | .load v _ _ => [v]
  | .seq s1 s2 => writesTo s1 ++ writesTo s2
  | .ite _ s1 s2 => writesTo s1 ++ writesTo s2
  | .while _ body => writesTo body
  | .for_ init _ step body => writesTo init ++ writesTo step ++ writesTo body
  | .call v _ _ => [v]
  | .skip => []
  | .break_ => []
  | .continue_ => []
  | .return_ _ => []

/-- A Stmt "writes only user vars in vars" if all its writesTo targets
    are .user names contained in the vars list. -/
def writesOnlyUserVarsIn (body : Stmt) (vars : List String) : Prop :=
  ∀ v ∈ writesTo body, ∃ name, v = .user name ∧ name ∈ vars

/-! ## Vector Read/Write Helpers -/

/-- Read `lanes` consecutive Int values from array positions in the environment.
    readVec env "x" 4 reads env(array "x" 0), ..., env(array "x" 3). -/
def readVec (env : LowLevelEnv) (name : String) (lanes : Nat) : List Int :=
  (List.range lanes).map fun i =>
    match env (.array name (Int.ofNat i)) with
    | .int v => v
    | _ => 0

/-- Write a list of Int values to consecutive array positions in the environment.
    writeVec env "x" [10, 20] writes 10 to array "x" 0 and 20 to array "x" 1. -/
def writeVec (env : LowLevelEnv) (name : String) (vals : List Int) : LowLevelEnv :=
  (List.range vals.length).foldl (fun e i =>
    e.update (.array name (Int.ofNat i)) (.int (vals.getD i 0))) env

/-! ## VecStmt IR -/

/-- Vector statement IR — wrapper over Stmt for SIMD operations.
    Does NOT modify Stmt. Delegates scalar evaluation to evalStmt. -/
inductive VecStmt where
  /-- Transparent scalar passthrough. -/
  | scalar : Stmt → VecStmt
  /-- Apply scalar `body` to `lanes` elements in parallel.
      `vars` lists the variable names that participate in the SIMD operation.
      The lifting theorem requires `writesOnlyUserVarsIn body vars`. -/
  | vecMap (lanes : Nat) (vars : List String) (body : Stmt) : VecStmt
  /-- Load `lanes` consecutive elements from `base[startIdx..]` into `dst[0..lanes-1]`. -/
  | vecLoad (dst : String) (base : String) (startIdx : LowLevelExpr) (lanes : Nat) : VecStmt
  /-- Store `src[0..lanes-1]` into `base[startIdx..]`. -/
  | vecStore (base : String) (startIdx : LowLevelExpr) (src : String) (lanes : Nat) : VecStmt
  /-- Non-lane-wise SIMD operation (mulHigh, satDoublingMulHigh, horizAdd).
      Reads src1/src2 as vectors, applies op, writes result to dst. -/
  | vecSpecialOp (op : VecSpecialOp) (lanes : Nat) (dst src1 src2 : String) : VecStmt
  /-- Sequential composition of VecStmts. -/
  | vecSeq : VecStmt → VecStmt → VecStmt
  deriving Repr, Inhabited

/-! ## Non-Vacuity -/

-- selectLane remaps correctly
example : selectLane 2 ["a", "b"] LowLevelEnv.default (.user "a") =
    LowLevelEnv.default (.array "a" 2) := by simp [selectLane, LowLevelEnv.default]

-- selectLane passes through non-listed vars
example : selectLane 2 ["a"] LowLevelEnv.default (.user "z") =
    LowLevelEnv.default (.user "z") := by simp [selectLane, LowLevelEnv.default]

-- writeLane writes to correct position
example : let laneEnv : LowLevelEnv := fun v => match v with
            | .user "x" => .int 42 | _ => .int 0
          writeLane 1 ["x"] laneEnv LowLevelEnv.default (.array "x" 1) = .int 42 := by
  simp [writeLane]

-- writeLane doesn't affect other lanes
example : let laneEnv : LowLevelEnv := fun v => match v with
            | .user "x" => .int 42 | _ => .int 0
          writeLane 1 ["x"] laneEnv LowLevelEnv.default (.array "x" 0) =
          LowLevelEnv.default (.array "x" 0) := by
  simp [writeLane, LowLevelEnv.default]

-- writesTo: butterfly body
example : writesTo (.seq (.assign (.user "tmp") (.litInt 0))
                   (.seq (.assign (.user "sum") (.litInt 0))
                         (.assign (.user "diff") (.litInt 0)))) =
    [.user "tmp", .user "sum", .user "diff"] := by rfl

end TrustLean
