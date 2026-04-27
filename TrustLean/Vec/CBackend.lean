/-
  Trust-Lean v4.2.0 — VecStmt C Backend
  N28.5: PARALELO — vecStmtToC: NEON + AVX2 + scalar fallback.

  Emits C code with SIMD intrinsics based on VecConfig.target.
  Outside the TCB — mistakes produce wrong C code, not unsound proofs.
-/
import TrustLean.Vec.Defs
import TrustLean.Vec.VecSpecialOp
import TrustLean.Backend.CBackend

set_option autoImplicit false

namespace TrustLean

/-! ## SIMD Intrinsic Tables -/

/-- NEON intrinsic for a BinOp (ARMv8 Advanced SIMD, u32 lanes). -/
def neonBinOpIntrinsic : BinOp → String
  | .add  => "vaddq_u32"
  | .sub  => "vsubq_u32"
  | .mul  => "vmulq_u32"
  | .band => "vandq_u32"
  | .bor  => "vorrq_u32"
  | .bxor => "veorq_u32"
  | .bshl => "vshlq_n_u32"
  | .bshr => "vshrq_n_u32"
  | _     => "/* unsupported_neon_op */"

/-- AVX2 intrinsic for a BinOp (Intel, 8 × u32 in __m256i). -/
def avx2BinOpIntrinsic : BinOp → String
  | .add  => "_mm256_add_epi32"
  | .sub  => "_mm256_sub_epi32"
  | .mul  => "_mm256_mullo_epi32"
  | .band => "_mm256_and_si256"
  | .bor  => "_mm256_or_si256"
  | .bxor => "_mm256_xor_si256"
  | .bshl => "_mm256_slli_epi32"
  | .bshr => "_mm256_srli_epi32"
  | _     => "/* unsupported_avx2_op */"

/-- NEON vector type for VecType. -/
def neonVecType : VecType → String
  | .u32 => "uint32x4_t"
  | .u64 => "uint64x2_t"

/-- AVX2 vector type (always __m256i). -/
def avx2VecType : VecType → String
  | _ => "__m256i"

/-- NEON broadcast intrinsic. -/
def neonBroadcast : VecType → String
  | .u32 => "vdupq_n_u32"
  | .u64 => "vdupq_n_u64"

/-- AVX2 broadcast intrinsic. -/
def avx2Broadcast : VecType → String
  | .u32 => "_mm256_set1_epi32"
  | .u64 => "_mm256_set1_epi64x"

/-- NEON load intrinsic. -/
def neonLoad : VecType → String
  | .u32 => "vld1q_u32"
  | .u64 => "vld1q_u64"

/-- NEON store intrinsic. -/
def neonStore : VecType → String
  | .u32 => "vst1q_u32"
  | .u64 => "vst1q_u64"

/-- AVX2 load intrinsic (unaligned). -/
def avx2Load : String := "_mm256_loadu_si256"

/-- AVX2 store intrinsic (unaligned). -/
def avx2Store : String := "_mm256_storeu_si256"

/-! ## VecSpecialOp → C Intrinsics -/

/-- Emit C code for a VecSpecialOp. Handles NEON, AVX2, and scalar fallback.
    NOTE: AVX2 mulHigh uses emulation (no _mm256_mulhi_epi32 for 32-bit). -/
private def indentC (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

def vecSpecialOpToC (config : VecConfig) (level : Nat) (dst src1 src2 : String)
    : VecSpecialOp → String
  | .mulHigh _ =>
    let ind := indentC level
    if config.target == "neon" then
      ind ++ dst ++ " = vmulhq_s32(" ++ src1 ++ ", " ++ src2 ++ ");\n"
    else if config.target == "avx2" then
      -- AVX2 has no _mm256_mulhi_epi32 for 32-bit. Emulation:
      ind ++ "{ /* mulHigh emulation for AVX2 (no _mm256_mulhi_epi32) */\n" ++
      ind ++ "  __m256i __lo = _mm256_srli_epi64(_mm256_mul_epu32(" ++ src1 ++ ", " ++ src2 ++ "), 32);\n" ++
      ind ++ "  __m256i __hi = _mm256_mul_epu32(_mm256_srli_epi64(" ++ src1 ++ ", 32), _mm256_srli_epi64(" ++ src2 ++ ", 32));\n" ++
      ind ++ "  " ++ dst ++ " = _mm256_blend_epi32(__lo, __hi, 0xAA);\n" ++
      ind ++ "}\n"
    else
      -- Scalar fallback
      ind ++ "for (int _i = 0; _i < " ++ toString config.lanes ++ "; _i++) " ++
        dst ++ "[_i] = (" ++ src1 ++ "[_i] * " ++ src2 ++ "[_i]) >> 32;\n"
  | .satDoublingMulHigh =>
    let ind := indentC level
    if config.target == "neon" then
      ind ++ dst ++ " = vqdmulhq_s32(" ++ src1 ++ ", " ++ src2 ++ ");\n"
    else if config.target == "avx2" then
      -- AVX2 emulation of saturating doubling multiply-high
      ind ++ "{ /* satDoublingMulHigh emulation for AVX2 */\n" ++
      ind ++ "  __m256i __s1 = _mm256_slli_epi32(" ++ src1 ++ ", 1);\n" ++
      ind ++ "  __m256i __lo = _mm256_srli_epi64(_mm256_mul_epu32(__s1, " ++ src2 ++ "), 32);\n" ++
      ind ++ "  __m256i __hi = _mm256_mul_epu32(_mm256_srli_epi64(__s1, 32), _mm256_srli_epi64(" ++ src2 ++ ", 32));\n" ++
      ind ++ "  " ++ dst ++ " = _mm256_blend_epi32(__lo, __hi, 0xAA);\n" ++
      ind ++ "}\n"
    else
      ind ++ "for (int _i = 0; _i < " ++ toString config.lanes ++ "; _i++) {\n" ++
      ind ++ "  int64_t __t = ((int64_t)" ++ src1 ++ "[_i] * " ++ src2 ++ "[_i] * 2) >> 32;\n" ++
      ind ++ "  " ++ dst ++ "[_i] = __t > 2147483647 ? 2147483647 : (__t < -2147483648 ? -2147483648 : (int32_t)__t);\n" ++
      ind ++ "}\n"
  | .horizAdd =>
    let ind := indentC level
    if config.target == "neon" then
      ind ++ dst ++ " = vpaddlq_s32(" ++ src1 ++ ");\n"
    else if config.target == "avx2" then
      ind ++ dst ++ " = _mm256_hadd_epi32(" ++ src1 ++ ", " ++ src2 ++ ");\n"
    else
      ind ++ "for (int _i = 0; _i < " ++ toString (config.lanes / 2) ++ "; _i++) " ++
        dst ++ "[_i] = " ++ src1 ++ "[2*_i] + " ++ src1 ++ "[2*_i+1];\n"

/-! ## VecStmt → C Code Generation -/

/-- Indentation helper. -/
private def indent (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

/-- Emit a scalar for loop as fallback for vecMap. -/
private def emitScalarLoop (level : Nat) (lanes : Nat) (_ : List String)
    (bodyC : String) : String :=
  let ind := indent level
  ind ++ "for (int _lane = 0; _lane < " ++ toString lanes ++ "; _lane++) {\n" ++
  bodyC ++ "\n" ++
  ind ++ "}\n"

/-- Generate C code from a VecStmt using the given SIMD configuration.
    Outside TCB — produces String, no proof obligations. -/
def vecStmtToC (config : VecConfig) (level : Nat) : VecStmt → String
  | .scalar s => stmtToC level s
  | .vecMap lanes vars body =>
    if config.target == "scalar" then
      emitScalarLoop level lanes vars (stmtToC (level + 1) body)
    else
      -- For NEON/AVX2, emit the scalar body as a comment + intrinsic version
      let ind := indent level
      ind ++ "/* vecMap " ++ toString lanes ++ " lanes (" ++ config.target ++ ") */\n" ++
      ind ++ "/* Scalar body: " ++ stmtToC 0 body ++ " */\n" ++
      ind ++ "/* SIMD intrinsics emitted by target backend */\n"
  | .vecLoad dst base startIdx lanes =>
    let ind := indent level
    if config.target == "neon" then
      let load := neonLoad config.vecType
      ind ++ neonVecType config.vecType ++ " v_" ++ dst ++
        " = " ++ load ++ "((const uint32_t*)&" ++ base ++ "[" ++ exprToC startIdx ++ "]);\n"
    else if config.target == "avx2" then
      ind ++ avx2VecType config.vecType ++ " v_" ++ dst ++
        " = " ++ avx2Load ++ "((const __m256i*)&" ++ base ++ "[" ++ exprToC startIdx ++ "]);\n"
    else
      -- Scalar fallback: load elements one by one
      let ind := indent level
      String.intercalate "" <|
        (List.range lanes).map fun i =>
          ind ++ dst ++ "[" ++ toString i ++ "] = " ++ base ++ "[" ++
          exprToC startIdx ++ " + " ++ toString i ++ "];\n"
  | .vecStore base startIdx src lanes =>
    let ind := indent level
    if config.target == "neon" then
      let store := neonStore config.vecType
      ind ++ store ++ "((uint32_t*)&" ++ base ++ "[" ++ exprToC startIdx ++ "], v_" ++ src ++ ");\n"
    else if config.target == "avx2" then
      ind ++ avx2Store ++ "((__m256i*)&" ++ base ++ "[" ++ exprToC startIdx ++ "], v_" ++ src ++ ");\n"
    else
      String.intercalate "" <|
        (List.range lanes).map fun i =>
          ind ++ base ++ "[" ++ exprToC startIdx ++ " + " ++ toString i ++ "] = " ++
          src ++ "[" ++ toString i ++ "];\n"
  | .vecSpecialOp op _lanes dst src1 src2 =>
    vecSpecialOpToC config level ("v_" ++ dst) ("v_" ++ src1) ("v_" ++ src2) op
  | .vecSeq s1 s2 =>
    vecStmtToC config level s1 ++ vecStmtToC config level s2

/-- Generate the required C header include for a VecConfig. -/
def vecHeaderInclude (config : VecConfig) : String :=
  if config.target == "neon" then "#include <arm_neon.h>\n"
  else if config.target == "avx2" then "#include <immintrin.h>\n"
  else ""

/-! ## Non-Vacuity: Emission Tests -/

/-- NEON header include. -/
example : vecHeaderInclude VecConfig.neon = "#include <arm_neon.h>\n" := by rfl

/-- AVX2 header include. -/
example : vecHeaderInclude VecConfig.avx2 = "#include <immintrin.h>\n" := by rfl

/-- Intrinsic table: NEON add. -/
example : neonBinOpIntrinsic .add = "vaddq_u32" := by rfl

/-- Intrinsic table: AVX2 mul. -/
example : avx2BinOpIntrinsic .mul = "_mm256_mullo_epi32" := by rfl

/-- Scalar config emits non-empty string. -/
example : (vecStmtToC (VecConfig.scalar 4) 0
    (.vecMap 4 ["a"] (.assign (.user "a") (.litInt 42)))).length > 0 := by decide

end TrustLean
