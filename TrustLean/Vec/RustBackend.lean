/-
  Trust-Lean v4.2.0 — VecStmt Rust Backend
  N28.6: PARALELO — vecStmtToRust: std::arch intrinsics.

  Emits Rust code with SIMD intrinsics using std::arch::aarch64 (NEON)
  or std::arch::x86_64 (AVX2). Scalar fallback uses simple loops.
  Outside the TCB — string emission only.
-/
import TrustLean.Vec.Defs
import TrustLean.Vec.VecSpecialOp
import TrustLean.Backend.RustBackend

set_option autoImplicit false

namespace TrustLean

/-! ## Rust SIMD Intrinsic Tables -/

/-- Rust NEON intrinsic path (std::arch::aarch64). -/
def rustNeonIntrinsic : BinOp → String
  | .add  => "std::arch::aarch64::vaddq_u32"
  | .sub  => "std::arch::aarch64::vsubq_u32"
  | .mul  => "std::arch::aarch64::vmulq_u32"
  | .band => "std::arch::aarch64::vandq_u32"
  | .bor  => "std::arch::aarch64::vorrq_u32"
  | .bxor => "std::arch::aarch64::veorq_u32"
  | .bshl => "std::arch::aarch64::vshlq_n_u32"
  | .bshr => "std::arch::aarch64::vshrq_n_u32"
  | _     => "/* unsupported */"

/-- Rust AVX2 intrinsic path (std::arch::x86_64). -/
def rustAvx2Intrinsic : BinOp → String
  | .add  => "std::arch::x86_64::_mm256_add_epi32"
  | .sub  => "std::arch::x86_64::_mm256_sub_epi32"
  | .mul  => "std::arch::x86_64::_mm256_mullo_epi32"
  | .band => "std::arch::x86_64::_mm256_and_si256"
  | .bor  => "std::arch::x86_64::_mm256_or_si256"
  | .bxor => "std::arch::x86_64::_mm256_xor_si256"
  | .bshl => "std::arch::x86_64::_mm256_slli_epi32"
  | .bshr => "std::arch::x86_64::_mm256_srli_epi32"
  | _     => "/* unsupported */"

/-- Rust vector type name. -/
def rustVecType (config : VecConfig) : String :=
  if config.target == "neon" then
    match config.vecType with
    | .u32 => "std::arch::aarch64::uint32x4_t"
    | .u64 => "std::arch::aarch64::uint64x2_t"
  else if config.target == "avx2" then
    "std::arch::x86_64::__m256i"
  else
    "[u32; " ++ toString config.lanes ++ "]"

/-! ## VecStmt → Rust Code Generation -/

private def rustIndent (level : Nat) : String :=
  String.mk (List.replicate (level * 4) ' ')

/-- Generate Rust code from a VecStmt.
    Outside TCB — produces String, no proof obligations. -/
def vecStmtToRust (config : VecConfig) (level : Nat) : VecStmt → String
  | .scalar s => stmtToRust level s
  | .vecMap lanes vars body =>
    let ind := rustIndent level
    if config.target == "scalar" then
      ind ++ "for _lane in 0.." ++ toString lanes ++ " {\n" ++
      stmtToRust (level + 1) body ++ "\n" ++
      ind ++ "}\n"
    else
      ind ++ "// vecMap " ++ toString lanes ++ " lanes (" ++ config.target ++ ")\n" ++
      ind ++ "// Scalar body: " ++ stmtToRust 0 body ++ "\n" ++
      ind ++ "// SIMD intrinsics emitted by target backend\n"
  | .vecLoad dst base startIdx lanes =>
    let ind := rustIndent level
    if config.target == "scalar" then
      String.intercalate "" <|
        (List.range lanes).map fun i =>
          ind ++ "let " ++ dst ++ "_" ++ toString i ++ " = " ++
          base ++ "[(" ++ exprToRust startIdx ++ " + " ++ toString i ++ ") as usize];\n"
    else if config.target == "neon" then
      ind ++ "let v_" ++ dst ++ " = unsafe { std::arch::aarch64::vld1q_u32(" ++
        base ++ ".as_ptr().add((" ++ exprToRust startIdx ++ ") as usize)) };\n"
    else
      ind ++ "let v_" ++ dst ++ " = unsafe { std::arch::x86_64::_mm256_loadu_si256(" ++
        base ++ ".as_ptr().add((" ++ exprToRust startIdx ++ ") as usize) as *const _) };\n"
  | .vecStore base startIdx src lanes =>
    let ind := rustIndent level
    if config.target == "scalar" then
      String.intercalate "" <|
        (List.range lanes).map fun i =>
          ind ++ base ++ "[(" ++ exprToRust startIdx ++ " + " ++ toString i ++ ") as usize] = " ++
          src ++ "_" ++ toString i ++ ";\n"
    else if config.target == "neon" then
      ind ++ "unsafe { std::arch::aarch64::vst1q_u32(" ++
        base ++ ".as_mut_ptr().add((" ++ exprToRust startIdx ++ ") as usize), v_" ++ src ++ ") };\n"
    else
      ind ++ "unsafe { std::arch::x86_64::_mm256_storeu_si256(" ++
        base ++ ".as_mut_ptr().add((" ++ exprToRust startIdx ++ ") as usize) as *mut _, v_" ++ src ++ ") };\n"
  | .vecSpecialOp op _lanes dst src1 src2 =>
    let ind := rustIndent level
    match config.target with
    | "neon" => match op with
      | .mulHigh _ =>
        ind ++ "let v_" ++ dst ++ " = unsafe { std::arch::aarch64::vmulhq_s32(v_" ++ src1 ++ ", v_" ++ src2 ++ ") };\n"
      | .satDoublingMulHigh =>
        ind ++ "let v_" ++ dst ++ " = unsafe { std::arch::aarch64::vqdmulhq_s32(v_" ++ src1 ++ ", v_" ++ src2 ++ ") };\n"
      | .horizAdd =>
        ind ++ "let v_" ++ dst ++ " = unsafe { std::arch::aarch64::vpaddlq_s32(v_" ++ src1 ++ ") };\n"
    | "avx2" => match op with
      | .mulHigh _ =>
        ind ++ "// AVX2 mulHigh emulation (no _mm256_mulhi_epi32 for 32-bit)\n" ++
        ind ++ "let v_" ++ dst ++ " = unsafe {\n" ++
        ind ++ "    let lo = std::arch::x86_64::_mm256_srli_epi64(std::arch::x86_64::_mm256_mul_epu32(v_" ++ src1 ++ ", v_" ++ src2 ++ "), 32);\n" ++
        ind ++ "    let hi = std::arch::x86_64::_mm256_mul_epu32(std::arch::x86_64::_mm256_srli_epi64(v_" ++ src1 ++ ", 32), std::arch::x86_64::_mm256_srli_epi64(v_" ++ src2 ++ ", 32));\n" ++
        ind ++ "    std::arch::x86_64::_mm256_blend_epi32(lo, hi, 0xAA)\n" ++
        ind ++ "};\n"
      | .satDoublingMulHigh =>
        ind ++ "// AVX2 satDoublingMulHigh emulation\n" ++
        ind ++ "let v_" ++ dst ++ " = unsafe {\n" ++
        ind ++ "    let s1 = std::arch::x86_64::_mm256_slli_epi32(v_" ++ src1 ++ ", 1);\n" ++
        ind ++ "    let lo = std::arch::x86_64::_mm256_srli_epi64(std::arch::x86_64::_mm256_mul_epu32(s1, v_" ++ src2 ++ "), 32);\n" ++
        ind ++ "    let hi = std::arch::x86_64::_mm256_mul_epu32(std::arch::x86_64::_mm256_srli_epi64(s1, 32), std::arch::x86_64::_mm256_srli_epi64(v_" ++ src2 ++ ", 32));\n" ++
        ind ++ "    std::arch::x86_64::_mm256_blend_epi32(lo, hi, 0xAA)\n" ++
        ind ++ "};\n"
      | .horizAdd =>
        ind ++ "let v_" ++ dst ++ " = unsafe { std::arch::x86_64::_mm256_hadd_epi32(v_" ++ src1 ++ ", v_" ++ src2 ++ ") };\n"
    | _ => -- scalar fallback
      ind ++ "// vecSpecialOp scalar fallback\n"
  | .vecSeq s1 s2 =>
    vecStmtToRust config level s1 ++ vecStmtToRust config level s2

/-- Rust feature gate / use statement for SIMD. -/
def rustSimdUse (config : VecConfig) : String :=
  if config.target == "neon" then
    "#[cfg(target_arch = \"aarch64\")]\nuse std::arch::aarch64::*;\n"
  else if config.target == "avx2" then
    "#[cfg(target_arch = \"x86_64\")]\nuse std::arch::x86_64::*;\n"
  else ""

/-! ## Non-Vacuity -/

/-- Rust NEON intrinsic: add. -/
example : rustNeonIntrinsic .add = "std::arch::aarch64::vaddq_u32" := by rfl

/-- Rust AVX2 intrinsic: mul. -/
example : rustAvx2Intrinsic .mul = "std::arch::x86_64::_mm256_mullo_epi32" := by rfl

/-- Scalar Rust config emits non-empty string. -/
example : (vecStmtToRust (VecConfig.scalar 4) 0
    (.vecMap 4 ["a"] (.assign (.user "a") (.litInt 42)))).length > 0 := by decide

end TrustLean
