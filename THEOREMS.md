═══ Specification Audit: Trust-Lean ═══
Theorems: 360  Lemmas: 0  Pipeline: 62
Clean: 318  T1(vacuity): 0  T1.5(identity): 0  T2(weak): 0  T3(structural): 13  T4(no-witness): 29

── TIER 3 — STRUCTURAL (13 issues) ──
  theorem scalarAssignToStmt_scalarBridge [PIPELINE]
    TrustLean/Bridge/ScalarTranslation.lean:62
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem fullBridge_scalar [PIPELINE]
    TrustLean/Bridge/Types.lean:262
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem fullBridge_loop [PIPELINE]
    TrustLean/Bridge/Types.lean:265
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem fullBridge_mem [PIPELINE]
    TrustLean/Bridge/Types.lean:268
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem loopBridge_update_scalar [PIPELINE]
    TrustLean/Bridge/Types.lean:273
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem memBridge_update_scalar [PIPELINE]
    TrustLean/Bridge/Types.lean:282
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem scalarBridge_update_mem [PIPELINE]
    TrustLean/Bridge/Types.lean:306
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem loopBridge_update_mem [PIPELINE]
    TrustLean/Bridge/Types.lean:319
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem scalarBridge_update_loop [PIPELINE]
    TrustLean/Bridge/Types.lean:331
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem memBridge_update_loop [PIPELINE]
    TrustLean/Bridge/Types.lean:343
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem ArithExpr.compile_correct [PIPELINE]
    TrustLean/Frontend/ArithExpr/Correctness.lean:69
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem BoolExpr.compile_correct [PIPELINE]
    TrustLean/Frontend/BoolExpr/Correctness.lean:77
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem microCBridge_default [PIPELINE]
    TrustLean/MicroC/Bridge.lean:37
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

── TIER 4 — NO WITNESS (29 issues) ──
  theorem gatherToStmt_go_correct [PIPELINE]
    TrustLean/Bridge/Correctness.lean:89
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem scatterToStmt_go_correct [PIPELINE]
    TrustLean/Bridge/Correctness.lean:121
    ⚠ T3-MANY-HYPOTHESES: 11 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem initTempsToStmt_correct [PIPELINE]
    TrustLean/Bridge/Correctness.lean:152
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem loopGo_succ_eq_of_agree
    TrustLean/Bridge/Correctness.lean:256
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem while_loop_correct [PIPELINE]
    TrustLean/Bridge/Correctness.lean:276
    ⚠ T2-UNUSED-PARTIAL: 1/13 params are _-prefixed: ['_hWFBody']
    ⚠ T3-MANY-HYPOTHESES: 13 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem loop_case_correct [PIPELINE]
    TrustLean/Bridge/Correctness.lean:382
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem expandedSigmaToStmt_correct [PIPELINE]
    TrustLean/Bridge/Correctness.lean:444
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem load_mem_correct [PIPELINE]
    TrustLean/Bridge/MemoryTranslation.lean:88
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem store_mem_correct [PIPELINE]
    TrustLean/Bridge/MemoryTranslation.lean:104
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem scalarBlockToStmt_correct [PIPELINE]
    TrustLean/Bridge/ScalarTranslation.lean:81
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem scalarBridge_update_other [PIPELINE]
    TrustLean/Bridge/Types.lean:294
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fuel_mono_seq
    TrustLean/Core/FuelMono.lean:28
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalStmt_fuel_mono_full
    TrustLean/Core/FuelMono.lean:192
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ArithExpr.compile_result_eval_stable
    TrustLean/Frontend/ArithExpr/Correctness.lean:37
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem BoolExpr.compile_result_eval_stable
    TrustLean/Frontend/BoolExpr/Correctness.lean:40
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem bridge_after_assign [PIPELINE]
    TrustLean/Frontend/ImpStmt/Correctness.lean:65
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ImpStmt.compile_correct [PIPELINE]
    TrustLean/Frontend/ImpStmt/Correctness.lean:87
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem microCBridge_update [PIPELINE]
    TrustLean/MicroC/Bridge.lean:42
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fuel_mono_seq_mc
    TrustLean/MicroC/FuelMono.lean:27
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalMicroC_fuel_mono_full
    TrustLean/MicroC/FuelMono.lean:166
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fuel_mono_seq_int64
    TrustLean/MicroC/Int64Eval.lean:293
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalMicroC_int64_fuel_mono_full
    TrustLean/MicroC/Int64Eval.lean:428
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem microCBridge_array_update [PIPELINE]
    TrustLean/MicroC/Simulation.lean:87
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem stmtToMicroC_correct [PIPELINE]
    TrustLean/MicroC/Simulation.lean:209
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fuel_mono_seq_uint32
    TrustLean/MicroC/UnsignedFuelMono.lean:55
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalMicroC_uint32_fuel_mono_full
    TrustLean/MicroC/UnsignedFuelMono.lean:185
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fuel_mono_seq_uint64
    TrustLean/MicroC/UnsignedFuelMono.lean:241
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalMicroC_uint64_fuel_mono_full
    TrustLean/MicroC/UnsignedFuelMono.lean:371
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem Pipeline.sound [PIPELINE]
    TrustLean/Pipeline.lean:53
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

✓ PASS — No blocking spec issues found