import Solcore.Frontend.RustHull.CreationTransportCorrespondence
import Solcore.Frontend.RustHull.RuntimeChildCallTerminationCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallUpdateCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallCallbackCorrespondence
import Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence
import Solcore.Frontend.RustHull.AccountObservationBuiltinCompiler

/-! Actual CREATE and CREATE2 lowering preserves every rule of
`CreationSemantics`. The static and init-size guards halt the frame through
the actual termination code, a missing gas observation faults, and the other
refusals and the admitted attempts run the actual transport and the installed
create handler. The handler cell, its closure and the shared state come from
the frame model. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.CreationBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive account_related runtime_related
  localLocations sharedLocations)
open RuntimeChildCallEffectsCorrespondence

structure References where
  isStatic : Core.Expr
  gas : Core.Expr
  memory : Core.Expr
  memorySize : Core.Expr
  returnData : Core.Expr
  returnDataSize : Core.Expr
  handler : Core.Expr
  address : Core.Expr
  depth : Core.Expr

/-- The frame references read in the lowering scope; the transport cells are
read under the binder for the available gas. -/
structure CompiledReferences (scope : Scope) (references : References) : Prop where
  isStatic : Effects.reference scope "isStatic" .bool = .ok references.isStatic
  gas : Effects.reference scope "availableGas" (.sum .unit .word) = .ok references.gas
  memory : Effects.reference (scope.temporary .word) "memory" WordMapping.type = .ok references.memory
  memorySize : Effects.reference (scope.temporary .word) "memorySize" .word = .ok references.memorySize
  returnData : Effects.reference (scope.temporary .word) "returnData" WordMapping.type = .ok references.returnData
  returnDataSize : Effects.reference (scope.temporary .word) "returnDataSize" .word = .ok references.returnDataSize
  handler : Effects.reference (scope.temporary .word) "createHandler"
    (OptionalCell.cellType Creation.callbackType) = .ok references.handler
  address : Effects.reference (scope.temporary .word) "address" .word = .ok references.address
  depth : Effects.reference (scope.temporary .word) "callDepth" .word = .ok references.depth

def expression (references : References) (create2 : Bool) (invalid value offset length salt : Core.Expr) :
    Core.Expr :=
  let invalidWord := LanguageResult.bind .word invalid (LanguageResult.success (.word Word.zero))
  .ifE (.loadCell references.isStatic) invalidWord
    (.ifE (.binary .wordGt length (.word (Word.ofNatModulo 49152))) invalidWord
      (.caseE (.loadCell references.gas) (LanguageResult.failure .word (.word (Word.ofNatModulo 9)))
        (Creation.invoke references.memory references.memorySize references.returnData references.returnDataSize
          references.handler (.loadCell references.address) (.loadCell references.depth)
          (value.weakenAt 0) (salt.weakenAt 0) (.bool create2) (.var 0) (offset.weakenAt 0) (length.weakenAt 0))))

theorem create_components {scope : Scope} {create2 : Bool} {value offset length salt : Core.Expr}
    {lowered : Lowered}
    (compiled : CreationImplementation.lowerCreate scope create2 value offset length salt = .ok lowered) :
    ∃ references invalid, CompiledReferences scope references ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      lowered = ⟨.word, expression references create2 invalid value offset length salt⟩ := by
  unfold CreationImplementation.lowerCreate at compiled
  obtain ⟨isStatic, staticCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨invalid, invalidCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨gas, gasCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨memorySize, memorySizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨returnData, returnDataCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨returnDataSize, returnDataSizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨handler, handlerCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨address, addressCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨depth, depthCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨⟨isStatic, gas, memory, memorySize, returnData, returnDataSize, handler, address, depth⟩, invalid,
    ⟨staticCompiled, gasCompiled, memoryCompiled, memorySizeCompiled, returnDataCompiled, returnDataSizeCompiled,
      handlerCompiled, addressCompiled, depthCompiled⟩, invalidCompiled, (Except.ok.inj returned).symm⟩

theorem create_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "create" arguments = .ok lowered) : arguments.length = 3 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem create2_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "create2" arguments = .ok lowered) : arguments.length = 4 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, rest⟩⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem create_lowered {scope : Scope} {value offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "create" [value, offset, length] = .ok lowered) :
    ∃ references invalid, CompiledReferences scope references ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      lowered = ⟨.word, expression references false invalid value offset length (.word Word.zero)⟩ := by
  rw [CreationImplementation.lowerBuiltin_create] at compiled
  obtain ⟨actual, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases Except.ok.inj returned
  exact create_components compiled

theorem create2_lowered {scope : Scope} {value offset length salt : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "create2" [value, offset, length, salt] = .ok lowered) :
    ∃ references invalid, CompiledReferences scope references ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      lowered = ⟨.word, expression references true invalid value offset length salt⟩ := by
  rw [CreationImplementation.lowerBuiltin_create2] at compiled
  obtain ⟨actual, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases Except.ok.inj returned
  exact create_components compiled

def References.rename (references : References) (mapping : Renaming) : References :=
  ⟨references.isStatic.rename mapping, references.gas.rename mapping,
    references.memory.rename mapping.lift, references.memorySize.rename mapping.lift,
    references.returnData.rename mapping.lift, references.returnDataSize.rename mapping.lift,
    references.handler.rename mapping.lift, references.address.rename mapping.lift,
    references.depth.rename mapping.lift⟩

theorem expression_rename (references : References) (create2 : Bool)
    (invalid value offset length salt : Core.Expr) (mapping : Renaming) :
    (expression references create2 invalid value offset length salt).rename mapping =
      expression (references.rename mapping) create2 (invalid.rename mapping) (value.rename mapping)
        (offset.rename mapping) (length.rename mapping) (salt.rename mapping) := by
  simp only [expression, References.rename, Core.Expr.rename, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, CreationCorrespondence.invoke_rename, Core.Expr.rename_weakenAt_zero]
  rfl

theorem length_guard (length : Word) :
    decide (length > Word.ofNatModulo 49152) = decide (CreationSemantics.maxInitCodeSize < length.val) := by
  have limit : (Word.ofNatModulo 49152).val = 49152 := Nat.mod_eq_of_lt (by decide)
  simp only [CreationSemantics.maxInitCodeSize, GT.gt, Fin.lt_def, limit]
  rfl

theorem depth_guard (depth : Word) :
    decide (depth > Word.ofNatModulo 1023) = decide (CreationSemantics.depthLimit ≤ depth.val) := by
  have limit : (Word.ofNatModulo 1023).val = 1023 := Nat.mod_eq_of_lt (by decide)
  simp only [CreationSemantics.depthLimit, GT.gt, Fin.lt_def, limit]
  rfl

theorem nonce_guard (nonce : Word) :
    nonce > Word.ofNatModulo (2 ^ 64 - 2) ↔ CreationSemantics.maxNonce ≤ nonce.val := by
  have limit : (Word.ofNatModulo (2 ^ 64 - 2)).val = 2 ^ 64 - 2 := Nat.mod_eq_of_lt (by decide)
  simp only [CreationSemantics.maxNonce, GT.gt, Fin.lt_def, limit]
  omega

/-- The installed create handler of the creating frame. -/
structure Handler (layout : Layout) (store : Store) where
  location : Nat
  value : Value
  read : store.read? location = some (.inRight .unit value)
  outside : location ∉ (localLocations layout).resources.all
  closure : CreationCorrespondence.HandlerClosure (sharedLocations layout) value

section
variable {scope : Scope} {references : References} {create2 : Bool}
variable {invalid valueExpr offsetExpr lengthExpr saltExpr : Core.Expr}
variable {value offset length salt : Word}
variable {result : Semantics.Result Semantics.Value} {finalState : RuntimeCallEffectsSemantics.State}
variable {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
variable {layout : Layout} {baseline : Nat → Option Value} {image : Option (List UInt8)}
variable {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

/-- A refusal after the transport keeps the shared state and publishes the
cleared caller cells. -/
private theorem refused_related (passive : CallPassive layout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    {final : Store} {size : Word}
    (localFinal : CallTransportCorrespondence.StateRel (localLocations layout)
      (CreationCorrespondence.cleared (RuntimeCallEffectsSemantics.transport state.external) size) final)
    (frame : CallTransportCorrespondence.Frame (localLocations layout) store final) :
    StateRel (model layout baseline slots image handlers anchors context) world
      {state with external := CreationSemantics.refused state.external size} final ∧ ClosuresPreserved store final := by
  have base := base_related stateRelated
  have sharedRelated : (transportModel layout handlers anchors context).related
      (RuntimeCallEffectsSemantics.shared state.external) store :=
    ⟨RuntimeCallEffectsCorrespondence.shared_resources base, linked_related stateRelated,
      stateRelated.external.1, stateRelated.external.2.2.1.2⟩
  have sharedFinal := (transportModel layout handlers anchors context).frame frame sharedRelated
  exact ⟨of_base (RuntimeCallEffectsCorrespondence.transport_updated passive base localFinal sharedFinal.1.1
      (RuntimeCallEffectsCorrespondence.Frame.of_local frame)) sharedFinal.2.1 sharedFinal.2.2.2,
    RuntimeCallEffectsCorrespondence.frame_closures base (RuntimeCallEffectsCorrespondence.Frame.of_local frame)⟩

/-- The renamed lowering, evaluated after argument packing. Word arguments are
stable under the binder introduced for the available gas. -/
theorem expression_preserves
    (compiled : CompiledReferences scope references)
    (invalidCompiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid)
    (computed : CreationSemantics.Refused value offset length state.external result finalState)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {gasLocation : Nat} (gasMember : ⟨"availableGas", .sum .unit .word, gasLocation⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (handler : Handler layout store)
    (handlerMember : ⟨"createHandler", OptionalCell.cellType Creation.callbackType, handler.location⟩ ∈ slots)
    (lengthEvaluated : Evaluates environment store (lengthExpr.rename mapping) (.word length) store)
    (valueWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((valueExpr.rename mapping).weakenAt 0) (.word value) store)
    (offsetWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((offsetExpr.rename mapping).weakenAt 0) (.word offset) store)
    (lengthWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((lengthExpr.rename mapping).weakenAt 0) (.word length) store)
    (saltWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((saltExpr.rename mapping).weakenAt 0) (.word salt) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment store
        ((expression references create2 invalid valueExpr offsetExpr lengthExpr saltExpr).rename mapping)
        resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  rw [expression_rename]
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memory := RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storage := RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have observed := RuntimeEnvironmentEffectsCorrespondence.observations_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have staticEvaluated : Evaluates environment store (Core.Expr.loadCell (references.isStatic.rename mapping))
      (.bool state.external.runtime.runtime.runtime.runtime.runtime.storage.isStatic) store :=
    .loadCell (reference_evaluates runtime staticMember compiled.isStatic store) storage.isStatic
  have gasRead := observed _ gasMember _ (show EnvironmentBuiltinCorrespondence.observation
    state.external.runtime.runtime.runtime.runtime.environment "availableGas" (.sum .unit .word) =
      some (EnvironmentBuiltinCorrespondence.wordOption state.external.runtime.runtime.runtime.runtime.environment.gas) from rfl)
  have gasLoaded : Evaluates environment store (Core.Expr.loadCell (references.gas.rename mapping))
      (EnvironmentBuiltinCorrespondence.wordOption state.external.runtime.runtime.runtime.runtime.environment.gas) store :=
    .loadCell (reference_evaluates runtime gasMember compiled.gas store) gasRead
  have lengthGuard : Evaluates environment store
      (.binary .wordGt (lengthExpr.rename mapping) (.word (Word.ofNatModulo 49152)))
      (.bool (decide (CreationSemantics.maxInitCodeSize < length.val))) store :=
    .binary lengthEvaluated .word (by simp only [BinaryOp.apply, length_guard])
  have staticGuard (isStatic : Bool)
      (same : (CreationSemantics.frame state.external).storage.isStatic = isStatic) :
      Evaluates environment store (Core.Expr.loadCell (references.isStatic.rename mapping)) (.bool isStatic) store := by
    rw [← same]
    exact staticEvaluated
  have halted : ∃ resultValue final, ResultRel .word (RuntimeCallEffectsSemantics.invalid state.external).1 resultValue ∧
      Evaluates environment store (LanguageResult.bind .word (invalid.rename mapping)
        (LanguageResult.success (.word Word.zero))) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := (RuntimeCallEffectsSemantics.invalid state.external).2} final ∧
      ClosuresPreserved store final := by
    have terminated := TerminationBuiltinCorrespondence.terminate_evaluates invalidCompiled runtime
      memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
      (fun _ _ => .word) (fun _ _ => .word)
    obtain ⟨_, memoryFinal, storageFinal, frame⟩ :=
      TerminationBuiltinCorrespondence.terminate_state memory storage 3 Word.zero Word.zero
    have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base
      (RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base) memoryFinal storageFinal frame) rfl
    have strengthened := of_base finalRelated (invalid_linked stateRelated)
      (context.updated base finalRelated stateRelated.external.2.2.1.2)
    exact ⟨.inLeft .word (.word Word.maximum), _, .language _, LanguageResult.bind_failure .word terminated,
      strengthened, TerminationBuiltinCorrespondence.terminate_closures memory storage 3 Word.zero Word.zero⟩
  have invoked {gas : Word} (available : CreationSemantics.availableGas state.external = some gas)
      {target : Value} {final : Store}
      (called : Evaluates (.word gas :: environment) store
        (Creation.invoke (references.memory.rename mapping.lift) (references.memorySize.rename mapping.lift)
          (references.returnData.rename mapping.lift) (references.returnDataSize.rename mapping.lift)
          (references.handler.rename mapping.lift) (.loadCell (references.address.rename mapping.lift))
          (.loadCell (references.depth.rename mapping.lift)) ((valueExpr.rename mapping).weakenAt 0)
          ((saltExpr.rename mapping).weakenAt 0) (.bool create2) (.var 0) ((offsetExpr.rename mapping).weakenAt 0)
          ((lengthExpr.rename mapping).weakenAt 0)) target final)
      (notStatic : (CreationSemantics.frame state.external).storage.isStatic = false)
      (bounded : length.val ≤ CreationSemantics.maxInitCodeSize) :
      Evaluates environment store
        ((expression (references.rename mapping) create2 (invalid.rename mapping) (valueExpr.rename mapping)
          (offsetExpr.rename mapping) (lengthExpr.rename mapping) (saltExpr.rename mapping))) target final := by
    have gasSome : Evaluates environment store (Core.Expr.loadCell (references.gas.rename mapping))
        (.inRight .unit (.word gas)) store := by
      have same : state.external.runtime.runtime.runtime.runtime.environment.gas = some gas := available
      simpa only [same, EnvironmentBuiltinCorrespondence.wordOption] using gasLoaded
    apply Evaluates.ifFalse (staticGuard false notStatic)
    apply Evaluates.ifFalse (by simpa only [decide_eq_false_iff_not, Nat.not_lt] using
      (show decide (CreationSemantics.maxInitCodeSize < length.val) = false by simpa using bounded) ▸ lengthGuard)
    exact .caseRight gasSome called
  have inner {gas : Word} := runtime.temporary .word (.word gas)
  have packedInvoke (gas : Word) : Evaluates (.word gas :: environment) store
      (bundle [references.memory.rename mapping.lift, references.memorySize.rename mapping.lift,
        references.returnData.rename mapping.lift, references.returnDataSize.rename mapping.lift,
        references.handler.rename mapping.lift, .loadCell (references.address.rename mapping.lift),
        .loadCell (references.depth.rename mapping.lift), (valueExpr.rename mapping).weakenAt 0,
        (saltExpr.rename mapping).weakenAt 0, .bool create2, .var 0, (offsetExpr.rename mapping).weakenAt 0,
        (lengthExpr.rename mapping).weakenAt 0])
      (bundleValues (CreationCorrespondence.argumentValues (localLocations layout) handler.location
        ⟨state.external.runtime.runtime.runtime.runtime.runtime.storage.address, state.external.callDepth,
          value, salt, create2, gas, offset, length⟩)) store :=
    .pair (reference_evaluates (inner (gas := gas)) memoryMember compiled.memory store)
      (.pair (reference_evaluates (inner (gas := gas)) memorySizeMember compiled.memorySize store)
      (.pair (reference_evaluates (inner (gas := gas)) dataMember compiled.returnData store)
      (.pair (reference_evaluates (inner (gas := gas)) dataSizeMember compiled.returnDataSize store)
      (.pair (reference_evaluates (inner (gas := gas)) handlerMember compiled.handler store)
      (.pair (.loadCell (reference_evaluates (inner (gas := gas)) addressMember compiled.address store) storage.address)
      (.pair (.loadCell (reference_evaluates (inner (gas := gas)) depthMember compiled.depth store)
          (RuntimeCallEffectsCorrespondence.depth_related base))
      (.pair (valueWeakened _) (.pair (saltWeakened _) (.pair .bool (.pair (.var rfl)
        (.pair (offsetWeakened _) (lengthWeakened _))))))))))))
  have separate : ∀ location ∈ (sharedLocations layout).all,
      location ∉ (localLocations layout).resources.all := by
    intro location member
    apply RuntimeCallEffectsCorrespondence.shared_local_separation layout
    simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.all, List.mem_cons,
      List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
  have creatorKey : (state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
      CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask =
      CreationSemantics.creator state.external :=
    CreationCorrespondence.mask_idempotent _
  have allowedDepth {depth : Word} (allowed : depth.val < CreationSemantics.depthLimit) :
      ¬depth > Word.ofNatModulo 1023 := by
    have limit : (Word.ofNatModulo 1023).val = 1023 := Nat.mod_eq_of_lt (by decide)
    simp only [CreationSemantics.depthLimit] at allowed
    simp only [GT.gt, Fin.lt_def, limit]
    omega
  cases computed with
  | staticFrame isStatic =>
      obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ := halted
      exact ⟨resultValue, final, resultRelated, .ifTrue (staticGuard true isStatic) evaluated, finalRelated, retained⟩
  | oversized notStatic oversized =>
      obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ := halted
      refine ⟨resultValue, final, resultRelated, .ifFalse (staticGuard false notStatic) (.ifTrue ?_ evaluated),
        finalRelated, retained⟩
      simpa only [oversized, decide_true] using lengthGuard
  | missingGas notStatic bounded missing =>
      have gasNone : Evaluates environment store (Core.Expr.loadCell (references.gas.rename mapping))
          (.inLeft .word .unit) store := by
        have same : state.external.runtime.runtime.runtime.runtime.environment.gas = none := missing
        simpa only [same, EnvironmentBuiltinCorrespondence.wordOption] using gasLoaded
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 9)), store, .language _, ?_, stateRelated, ClosuresPreserved.refl _⟩
      apply Evaluates.ifFalse (staticGuard false notStatic)
      apply Evaluates.ifFalse (by simpa only [decide_eq_false_iff_not, Nat.not_lt] using
        (show decide (CreationSemantics.maxInitCodeSize < length.val) = false by simpa using bounded) ▸ lengthGuard)
      exact .caseLeft gasNone (.inLeft .word)
  | inputOverflow notStatic bounded available invalid =>
      refine ⟨.inLeft .word (.word Memory.overflowReason), store, .language _, ?_, stateRelated, ClosuresPreserved.refl _⟩
      exact invoked available (CreationCorrespondence.invoke_overflow (packedInvoke _)
        (RuntimeCallEffectsCorrespondence.local_related base) invalid) notStatic bounded
  | depthExceeded notStatic bounded available touched exceeded =>
      have exceeded' : state.external.callDepth > Word.ofNatModulo 1023 := by
        have limit : (Word.ofNatModulo 1023).val = 1023 := Nat.mod_eq_of_lt (by decide)
        simp only [CreationSemantics.depthLimit] at exceeded
        simp only [GT.gt, Fin.lt_def, limit]
        omega
      obtain ⟨final, evaluated, localFinal, frame⟩ := CreationCorrespondence.invoke_depth (packedInvoke _)
        (RuntimeCallEffectsCorrespondence.local_related base) touched exceeded'
      obtain ⟨finalRelated, closures⟩ := refused_related callPassive stateRelated localFinal frame
      exact ⟨_, final, .value (.word _), invoked available evaluated notStatic bounded, finalRelated, closures⟩
  | underfunded notStatic bounded available touched allowed shortfall =>
      obtain ⟨final, evaluated, localFinal, frame⟩ := CreationCorrespondence.invoke_refused (packedInvoke _)
        (RuntimeCallEffectsCorrespondence.local_related base) touched (allowedDepth allowed) bounded
        handler.read handler.outside handler.closure (RuntimeCallEffectsCorrespondence.shared_related base) separate
        (fun _ => .underfunded (by
          change _ > StorageSemantics.readWord ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
            CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask) state.external.runtime.runtime.balances
          rw [creatorKey]
          exact shortfall))
      obtain ⟨finalRelated, closures⟩ := refused_related callPassive stateRelated localFinal frame
      exact ⟨_, final, .value (.word _), invoked available evaluated notStatic bounded, finalRelated, closures⟩
  | nonceExhausted notStatic bounded available touched allowed funded found exhausted =>
      obtain ⟨final, evaluated, localFinal, frame⟩ := CreationCorrespondence.invoke_refused (packedInvoke _)
        (RuntimeCallEffectsCorrespondence.local_related base) touched (allowedDepth allowed) bounded
        handler.read handler.outside handler.closure (RuntimeCallEffectsCorrespondence.shared_related base) separate
        (fun _ => .exhausted
          (by
            change ¬_ > StorageSemantics.readWord ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
              CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask) state.external.runtime.runtime.balances
            rw [creatorKey]
            exact Nat.not_lt.mpr funded)
          (by
            change StorageSemantics.get state.external.runtime.runtime.runtime.runtime.runtime.storage.world
              ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
                CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask)
              state.external.runtime.runtime.runtime.runtime.runtime.storage.complete = _
            rw [creatorKey]
            exact found)
          ((nonce_guard _).mpr exhausted))
      obtain ⟨finalRelated, closures⟩ := refused_related callPassive stateRelated localFinal frame
      exact ⟨_, final, .value (.word _), invoked available evaluated notStatic bounded, finalRelated, closures⟩

theorem Copy.deterministic {sourceWords : MemorySemantics.Entries} {destination source length : Word}
    {destinationWords first second : MemorySemantics.Entries}
    (left : MemoryCopySemantics.Copy sourceWords destination source length destinationWords first)
    (right : MemoryCopySemantics.Copy sourceWords destination source length destinationWords second) :
    first = second := by
  induction left generalizing second with
  | empty =>
      cases right with
      | empty => rfl
      | step nonempty _ => exact absurd rfl nonempty
  | step nonempty rest ih =>
      cases right with
      | empty => exact absurd rfl nonempty
      | step _ rest' => exact ih rest'

/-- An admitted attempt without an init frame publishes the cleared caller
cells and the handler's shared account changes. -/
private theorem admitted_related (passive : CallPassive layout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    {final : Store} {size : Word} {next : AccountCallSemantics.Shared}
    (localFinal : CallTransportCorrespondence.StateRel (localLocations layout)
      (CreationCorrespondence.cleared (RuntimeCallEffectsSemantics.transport state.external) size) final)
    (sharedFinal : AccountCallCorrespondence.LinkedSharedStateRel anchors (sharedLocations layout) next final)
    (frame : RuntimeCallEffectsCorrespondence.Frame layout store final) :
    StateRel (model layout baseline slots image handlers anchors context) world
      {state with external := (RuntimeCallEffectsSemantics.withTransport state.external
        (CreationCorrespondence.cleared (RuntimeCallEffectsSemantics.transport state.external) size) next)} final ∧
    ClosuresPreserved store final := by
  have base := base_related stateRelated
  have baseFinal := RuntimeCallEffectsCorrespondence.transport_updated passive base localFinal sharedFinal.shared frame
  refine ⟨of_base baseFinal ?_ (context.updated base baseFinal stateRelated.external.2.2.1.2),
    RuntimeCallEffectsCorrespondence.frame_closures base frame⟩
  have same : RuntimeChildCallEffectsCorrespondence.sourceWorld (RuntimeCallEffectsSemantics.withTransport state.external
      (CreationCorrespondence.cleared (RuntimeCallEffectsSemantics.transport state.external) size) next) = next.world := by
    simp only [RuntimeChildCallEffectsCorrespondence.sourceWorld, RuntimeCallEffectsSemantics.withTransport,
      RuntimeCallEffectsSemantics.shared_withReturned, RuntimeCallEffectsSemantics.shared_withShared]
  rw [same]
  exact sharedFinal.linked

/-- Admitted attempts that run no init frame, through the actual transport and
dispatcher: a collision returns zero, a deployment returns the new address with
the account changes published in the shared cells, and the faults after the
nonce advance return their reason with only the advance kept. -/
theorem expression_admitted
    (compiled : CompiledReferences scope references)
    (invalidCompiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid)
    {scheme : CreationAddressSemantics.Scheme}
    (selected : (if create2 then CreationAddressSemantics.Scheme.create2 salt else .create) = scheme)
    (computed : CreationSemantics.Admitted scheme value offset length state.external result finalState)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {gasLocation : Nat} (gasMember : ⟨"availableGas", .sum .unit .word, gasLocation⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (handler : Handler layout store)
    (handlerMember : ⟨"createHandler", OptionalCell.cellType Creation.callbackType, handler.location⟩ ∈ slots)
    (lengthEvaluated : Evaluates environment store (lengthExpr.rename mapping) (.word length) store)
    (valueWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((valueExpr.rename mapping).weakenAt 0) (.word value) store)
    (offsetWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((offsetExpr.rename mapping).weakenAt 0) (.word offset) store)
    (lengthWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((lengthExpr.rename mapping).weakenAt 0) (.word length) store)
    (saltWeakened : ∀ inserted, Evaluates (inserted :: environment) store
      ((saltExpr.rename mapping).weakenAt 0) (.word salt) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment store
        ((expression references create2 invalid valueExpr offsetExpr lengthExpr saltExpr).rename mapping)
        resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  rw [expression_rename]
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memory := RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storage := RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have observed := RuntimeEnvironmentEffectsCorrespondence.observations_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have staticEvaluated : Evaluates environment store (Core.Expr.loadCell (references.isStatic.rename mapping))
      (.bool state.external.runtime.runtime.runtime.runtime.runtime.storage.isStatic) store :=
    .loadCell (reference_evaluates runtime staticMember compiled.isStatic store) storage.isStatic
  have gasRead := observed _ gasMember _ (show EnvironmentBuiltinCorrespondence.observation
    state.external.runtime.runtime.runtime.runtime.environment "availableGas" (.sum .unit .word) =
      some (EnvironmentBuiltinCorrespondence.wordOption state.external.runtime.runtime.runtime.runtime.environment.gas) from rfl)
  have gasLoaded : Evaluates environment store (Core.Expr.loadCell (references.gas.rename mapping))
      (EnvironmentBuiltinCorrespondence.wordOption state.external.runtime.runtime.runtime.runtime.environment.gas) store :=
    .loadCell (reference_evaluates runtime gasMember compiled.gas store) gasRead
  have lengthGuard : Evaluates environment store
      (.binary .wordGt (lengthExpr.rename mapping) (.word (Word.ofNatModulo 49152)))
      (.bool (decide (CreationSemantics.maxInitCodeSize < length.val))) store :=
    .binary lengthEvaluated .word (by simp only [BinaryOp.apply, length_guard])
  have staticGuard (isStatic : Bool)
      (same : (CreationSemantics.frame state.external).storage.isStatic = isStatic) :
      Evaluates environment store (Core.Expr.loadCell (references.isStatic.rename mapping)) (.bool isStatic) store := by
    rw [← same]
    exact staticEvaluated
  have halted : ∃ resultValue final, ResultRel .word (RuntimeCallEffectsSemantics.invalid state.external).1 resultValue ∧
      Evaluates environment store (LanguageResult.bind .word (invalid.rename mapping)
        (LanguageResult.success (.word Word.zero))) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := (RuntimeCallEffectsSemantics.invalid state.external).2} final ∧
      ClosuresPreserved store final := by
    have terminated := TerminationBuiltinCorrespondence.terminate_evaluates invalidCompiled runtime
      memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
      (fun _ _ => .word) (fun _ _ => .word)
    obtain ⟨_, memoryFinal, storageFinal, frame⟩ :=
      TerminationBuiltinCorrespondence.terminate_state memory storage 3 Word.zero Word.zero
    have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base
      (RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base) memoryFinal storageFinal frame) rfl
    have strengthened := of_base finalRelated (invalid_linked stateRelated)
      (context.updated base finalRelated stateRelated.external.2.2.1.2)
    exact ⟨.inLeft .word (.word Word.maximum), _, .language _, LanguageResult.bind_failure .word terminated,
      strengthened, TerminationBuiltinCorrespondence.terminate_closures memory storage 3 Word.zero Word.zero⟩
  have invoked {gas : Word} (available : CreationSemantics.availableGas state.external = some gas)
      {target : Value} {final : Store}
      (called : Evaluates (.word gas :: environment) store
        (Creation.invoke (references.memory.rename mapping.lift) (references.memorySize.rename mapping.lift)
          (references.returnData.rename mapping.lift) (references.returnDataSize.rename mapping.lift)
          (references.handler.rename mapping.lift) (.loadCell (references.address.rename mapping.lift))
          (.loadCell (references.depth.rename mapping.lift)) ((valueExpr.rename mapping).weakenAt 0)
          ((saltExpr.rename mapping).weakenAt 0) (.bool create2) (.var 0) ((offsetExpr.rename mapping).weakenAt 0)
          ((lengthExpr.rename mapping).weakenAt 0)) target final)
      (notStatic : (CreationSemantics.frame state.external).storage.isStatic = false)
      (bounded : length.val ≤ CreationSemantics.maxInitCodeSize) :
      Evaluates environment store
        ((expression (references.rename mapping) create2 (invalid.rename mapping) (valueExpr.rename mapping)
          (offsetExpr.rename mapping) (lengthExpr.rename mapping) (saltExpr.rename mapping))) target final := by
    have gasSome : Evaluates environment store (Core.Expr.loadCell (references.gas.rename mapping))
        (.inRight .unit (.word gas)) store := by
      have same : state.external.runtime.runtime.runtime.runtime.environment.gas = some gas := available
      simpa only [same, EnvironmentBuiltinCorrespondence.wordOption] using gasLoaded
    apply Evaluates.ifFalse (staticGuard false notStatic)
    apply Evaluates.ifFalse (by simpa only [decide_eq_false_iff_not, Nat.not_lt] using
      (show decide (CreationSemantics.maxInitCodeSize < length.val) = false by simpa using bounded) ▸ lengthGuard)
    exact .caseRight gasSome called
  have inner {gas : Word} := runtime.temporary .word (.word gas)
  have packedInvoke (gas : Word) : Evaluates (.word gas :: environment) store
      (bundle [references.memory.rename mapping.lift, references.memorySize.rename mapping.lift,
        references.returnData.rename mapping.lift, references.returnDataSize.rename mapping.lift,
        references.handler.rename mapping.lift, .loadCell (references.address.rename mapping.lift),
        .loadCell (references.depth.rename mapping.lift), (valueExpr.rename mapping).weakenAt 0,
        (saltExpr.rename mapping).weakenAt 0, .bool create2, .var 0, (offsetExpr.rename mapping).weakenAt 0,
        (lengthExpr.rename mapping).weakenAt 0])
      (bundleValues (CreationCorrespondence.argumentValues (localLocations layout) handler.location
        ⟨state.external.runtime.runtime.runtime.runtime.runtime.storage.address, state.external.callDepth,
          value, salt, create2, gas, offset, length⟩)) store :=
    .pair (reference_evaluates (inner (gas := gas)) memoryMember compiled.memory store)
      (.pair (reference_evaluates (inner (gas := gas)) memorySizeMember compiled.memorySize store)
      (.pair (reference_evaluates (inner (gas := gas)) dataMember compiled.returnData store)
      (.pair (reference_evaluates (inner (gas := gas)) dataSizeMember compiled.returnDataSize store)
      (.pair (reference_evaluates (inner (gas := gas)) handlerMember compiled.handler store)
      (.pair (.loadCell (reference_evaluates (inner (gas := gas)) addressMember compiled.address store) storage.address)
      (.pair (.loadCell (reference_evaluates (inner (gas := gas)) depthMember compiled.depth store)
          (RuntimeCallEffectsCorrespondence.depth_related base))
      (.pair (valueWeakened _) (.pair (saltWeakened _) (.pair .bool (.pair (.var rfl)
        (.pair (offsetWeakened _) (lengthWeakened _))))))))))))
  have separate : ∀ location ∈ (sharedLocations layout).all,
      location ∉ (localLocations layout).resources.all := by
    intro location member
    apply RuntimeCallEffectsCorrespondence.shared_local_separation layout
    simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.all, List.mem_cons,
      List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
  have creatorKey : (state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
      CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask =
      CreationSemantics.creator state.external :=
    CreationCorrespondence.mask_idempotent _
  have allowedDepth {depth : Word} (allowed : depth.val < CreationSemantics.depthLimit) :
      ¬depth > Word.ofNatModulo 1023 := by
    have limit : (Word.ofNatModulo 1023).val = 1023 := Nat.mod_eq_of_lt (by decide)
    simp only [CreationSemantics.depthLimit] at allowed
    simp only [GT.gt, Fin.lt_def, limit]
    omega
  have sharedLinked : AccountCallCorrespondence.LinkedSharedStateRel anchors (sharedLocations layout)
      (RuntimeCallEffectsSemantics.shared state.external) store :=
    ⟨RuntimeCallEffectsCorrespondence.shared_related base, linked_related stateRelated⟩
  have localRelated := RuntimeCallEffectsCorrespondence.local_related base
  have mutableFrame {final : Store} (lengthLe : store.length ≤ final.length)
      (kept : ∀ location value, location ∉ (localLocations layout).resources.all →
        location ∉ [(sharedLocations layout).world, (sharedLocations layout).balances] →
        store.read? location = some value → final.read? location = some value) :
      RuntimeCallEffectsCorrespondence.Frame layout store final := by
    refine ⟨lengthLe, fun location value outside found => kept location value ?_ ?_ found⟩
    · intro member
      apply outside
      simp only [localLocations, CallTransportCorrespondence.Locations.resources, LogsCorrespondence.Locations.all,
        List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [RuntimeCallEffectsCorrespondence.callMutable, List.mem_cons, List.not_mem_nil, or_false]
      rcases member with rfl | rfl | rfl | rfl <;> simp
    · intro member
      apply outside
      simp only [sharedLocations, List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [RuntimeCallEffectsCorrespondence.callMutable, List.mem_cons, List.not_mem_nil, or_false]
      rcases member with rfl | rfl <;> simp
  have keyed {property : Word → Prop}
      (holds : property (CreationSemantics.creator state.external)) :
      property ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
        CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask) := by
    rw [creatorKey]
    exact holds
  have nonceBelow {account : AccountState.Account} (below : account.nonce.val < CreationSemantics.maxNonce) :
      ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2) := fun large => Nat.not_le.mpr below ((nonce_guard _).mp large)
  cases computed with
  | collision admitted copied derived occupied used =>
      rename_i size target account existing initCode
      obtain ⟨gas, available⟩ := admitted.available
      obtain ⟨final, evaluated, localFinal, sharedFinal, lengthLe, kept⟩ :=
        CreationCorrespondence.invoke_admitted (address := Word.zero)
          (next := {RuntimeCallEffectsSemantics.shared state.external with
            world := CreationCorrespondence.advancedWorld (RuntimeCallEffectsSemantics.shared state.external)
              ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
                CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask) account})
          (packedInvoke gas) localRelated admitted.touched
          (allowedDepth admitted.allowed) admitted.bounded handler.read handler.outside handler.closure sharedLinked separate
          (fun initCode' copiedInit => by
            obtain rfl := Copy.deterministic copiedInit copied
            refine .collision (account := account) (existing := existing) (target := target)
              (keyed (property := fun key =>
                ¬value > StorageSemantics.readWord key state.external.runtime.runtime.balances)
                (Nat.not_lt.mpr admitted.funded))
              (keyed (property := fun key => StorageSemantics.get state.external.runtime.runtime.runtime.runtime.runtime.storage.world
                key state.external.runtime.runtime.runtime.runtime.runtime.storage.complete = .ok account) admitted.found)
              (nonceBelow admitted.belowLimit) admitted.bounded ?_ ?_ used
            · rw [← selected] at derived
              exact keyed (property := fun key => CreationAddressSemantics.Derived key account.nonce initCode' length
                (if create2 then CreationAddressSemantics.Scheme.create2 salt else .create) target) derived
            · exact keyed (property := fun key => StorageSemantics.lookup target (CreationCorrespondence.advancedWorld
                (RuntimeCallEffectsSemantics.shared state.external) key account) = some existing) occupied)
      obtain ⟨finalRelated, closures⟩ := admitted_related callPassive stateRelated localFinal sharedFinal
        (mutableFrame lengthLe kept)
      rw [creatorKey] at finalRelated
      exact ⟨_, final, .value (.word _), invoked available evaluated admitted.notStatic admitted.bounded,
        finalRelated, closures⟩
  | deployed admitted copied derived absent complete emptyInit transferred =>
      rename_i size target account initCode balances
      obtain ⟨gas, available⟩ := admitted.available
      obtain ⟨final, evaluated, localFinal, sharedFinal, lengthLe, kept⟩ :=
        CreationCorrespondence.invoke_admitted (address := target)
          (next := {RuntimeCallEffectsSemantics.shared state.external with
            world := (StorageSemantics.put target (CreationSemantics.createdAccount target)
              (CreationCorrespondence.advancedWorld (RuntimeCallEffectsSemantics.shared state.external)
                ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
                  CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask) account))
            balances := balances})
          (packedInvoke gas) localRelated admitted.touched
          (allowedDepth admitted.allowed) admitted.bounded handler.read handler.outside handler.closure sharedLinked separate
          (fun initCode' copiedInit => by
            obtain rfl := Copy.deterministic copiedInit copied
            refine .deployed (account := account) (target := target)
              (keyed (property := fun key =>
                ¬value > StorageSemantics.readWord key state.external.runtime.runtime.balances)
                (Nat.not_lt.mpr admitted.funded))
              (keyed (property := fun key => StorageSemantics.get state.external.runtime.runtime.runtime.runtime.runtime.storage.world
                key state.external.runtime.runtime.runtime.runtime.runtime.storage.complete = .ok account) admitted.found)
              (nonceBelow admitted.belowLimit) admitted.bounded ?_ ?_ complete emptyInit ?_
            · rw [← selected] at derived
              exact keyed (property := fun key => CreationAddressSemantics.Derived key account.nonce initCode' length
                (if create2 then CreationAddressSemantics.Scheme.create2 salt else .create) target) derived
            · exact keyed (property := fun key => StorageSemantics.lookup target (CreationCorrespondence.advancedWorld
                (RuntimeCallEffectsSemantics.shared state.external) key account) = none) absent
            · exact keyed (property := fun key => AccountCallSemantics.transfer key target value
                state.external.runtime.runtime.balances = .ok balances) transferred)
      obtain ⟨finalRelated, closures⟩ := admitted_related callPassive stateRelated localFinal sharedFinal
        (mutableFrame lengthLe kept)
      rw [creatorKey] at finalRelated
      exact ⟨_, final, .value (.word _), invoked available evaluated admitted.notStatic admitted.bounded,
        finalRelated, closures⟩
  | unknown admitted copied derived unknown =>
      rename_i size target account initCode
      obtain ⟨gas, available⟩ := admitted.available
      obtain ⟨final, evaluated, localFinal, sharedFinal, lengthLe, kept⟩ :=
        CreationCorrespondence.invoke_failed (reason := Word.ofNatModulo 7)
          (next := {RuntimeCallEffectsSemantics.shared state.external with
            world := CreationCorrespondence.advancedWorld (RuntimeCallEffectsSemantics.shared state.external)
              ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
                CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask) account})
          (packedInvoke gas) localRelated admitted.touched
          (allowedDepth admitted.allowed) admitted.bounded handler.read handler.outside handler.closure sharedLinked separate
          (fun initCode' copiedInit => by
            obtain rfl := Copy.deterministic copiedInit copied
            refine .unknown (account := account) (target := target)
              (keyed (property := fun key =>
                ¬value > StorageSemantics.readWord key state.external.runtime.runtime.balances)
                (Nat.not_lt.mpr admitted.funded))
              (keyed (property := fun key => StorageSemantics.get state.external.runtime.runtime.runtime.runtime.runtime.storage.world
                key state.external.runtime.runtime.runtime.runtime.runtime.storage.complete = .ok account) admitted.found)
              (nonceBelow admitted.belowLimit) admitted.bounded ?_ ?_
            · rw [← selected] at derived
              exact keyed (property := fun key => CreationAddressSemantics.Derived key account.nonce initCode' length
                (if create2 then CreationAddressSemantics.Scheme.create2 salt else .create) target) derived
            · exact keyed (property := fun key => CreationSemantics.Unknown (CreationCorrespondence.advancedWorld
                (RuntimeCallEffectsSemantics.shared state.external) key account) target
                state.external.runtime.runtime.runtime.runtime.runtime.storage.complete) unknown)
      obtain ⟨finalRelated, closures⟩ := admitted_related callPassive stateRelated localFinal sharedFinal
        (mutableFrame lengthLe kept)
      rw [creatorKey] at finalRelated
      exact ⟨_, final, .language _, invoked available evaluated admitted.notStatic admitted.bounded,
        finalRelated, closures⟩
  | overflow admitted copied derived absent complete overflowed =>
      rename_i size target account initCode
      obtain ⟨gas, available⟩ := admitted.available
      obtain ⟨final, evaluated, localFinal, sharedFinal, lengthLe, kept⟩ :=
        CreationCorrespondence.invoke_failed (reason := Word.ofNatModulo 12)
          (next := {RuntimeCallEffectsSemantics.shared state.external with
            world := CreationCorrespondence.advancedWorld (RuntimeCallEffectsSemantics.shared state.external)
              ((state.external.runtime.runtime.runtime.runtime.runtime.storage.address.bitAnd
                CreationCorrespondence.addressMask).bitAnd CreationCorrespondence.addressMask) account})
          (packedInvoke gas) localRelated admitted.touched
          (allowedDepth admitted.allowed) admitted.bounded handler.read handler.outside handler.closure sharedLinked separate
          (fun initCode' copiedInit => by
            obtain rfl := Copy.deterministic copiedInit copied
            refine .overflow (account := account) (target := target)
              (keyed (property := fun key =>
                ¬value > StorageSemantics.readWord key state.external.runtime.runtime.balances)
                (Nat.not_lt.mpr admitted.funded))
              (keyed (property := fun key => StorageSemantics.get state.external.runtime.runtime.runtime.runtime.runtime.storage.world
                key state.external.runtime.runtime.runtime.runtime.runtime.storage.complete = .ok account) admitted.found)
              (nonceBelow admitted.belowLimit) admitted.bounded ?_ ?_ complete ?_
            · rw [← selected] at derived
              exact keyed (property := fun key => CreationAddressSemantics.Derived key account.nonce initCode' length
                (if create2 then CreationAddressSemantics.Scheme.create2 salt else .create) target) derived
            · exact keyed (property := fun key => StorageSemantics.lookup target (CreationCorrespondence.advancedWorld
                (RuntimeCallEffectsSemantics.shared state.external) key account) = none) absent
            · exact keyed (property := fun key => AccountCallSemantics.transfer key target value
                state.external.runtime.runtime.balances = .error (Word.ofNatModulo 12)) overflowed)
      obtain ⟨finalRelated, closures⟩ := admitted_related callPassive stateRelated localFinal sharedFinal
        (mutableFrame lengthLe kept)
      rw [creatorKey] at finalRelated
      exact ⟨_, final, .language _, invoked available evaluated admitted.notStatic admitted.bounded,
        finalRelated, closures⟩

theorem projectArgument_rename (index count : Nat) (expr : Core.Expr) (mapping : Renaming) :
    (projectArgument index count expr).rename mapping = projectArgument index count (expr.rename mapping) := by
  induction count generalizing index expr with
  | zero => simp [projectArgument, Core.Expr.rename]
  | succ count ih =>
      cases count with
      | zero => simp [projectArgument]
      | succ count =>
          by_cases zero : index = 0
          · simp [projectArgument, zero, Core.Expr.rename]
          · simp only [projectArgument, zero, ↓reduceIte]
            rw [ih]
            simp [Core.Expr.rename]

theorem projectArgument_weakenAt (index count : Nat) (expr : Core.Expr) (cutoff : Nat) :
    (projectArgument index count expr).weakenAt cutoff = projectArgument index count (expr.weakenAt cutoff) := by
  induction count generalizing index expr with
  | zero => simp [projectArgument, Core.Expr.weakenAt]
  | succ count ih =>
      cases count with
      | zero => simp [projectArgument]
      | succ count =>
          by_cases zero : index = 0
          · simp [projectArgument, zero, Core.Expr.weakenAt]
          · simp only [projectArgument, zero, ↓reduceIte]
            rw [ih]
            simp [Core.Expr.weakenAt]

/-- A packed argument projection, weakened under the gas binder, reads the
same packed value one binder further out. -/
private theorem weakened {mapping : Renaming} {environment : Environment} {store : Store}
    {index count : Nat} {input : Value} {value : Word}
    (projected : ∀ inserted : Value, Evaluates (inserted :: input :: environment) store
      (projectArgument index count (.var 1)) (.word value) store) :
    ∀ inserted : Value, Evaluates (inserted :: input :: environment) store
      (((projectArgument index count (.var 0)).rename mapping.lift).weakenAt 0) (.word value) store := by
  intro inserted
  have shifted : ((Core.Expr.var 0).rename mapping.lift).weakenAt 0 = .var 1 := by
    simp [Core.Expr.rename, Core.Expr.weakenAt, Core.Renaming.lift]
  rw [projectArgument_rename, projectArgument_weakenAt, shifted]
  exact projected inserted

/-- CREATE preserves every refusal through actual argument packing, the
static and init-size guards, the gas read and the transport. -/
theorem create_preserves {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    {targets : List Core.Value} {initial : Store}
    (compiledBuiltin : lowerBuiltin scope "create" expected arguments = .ok lowered)
    (computed : CreationSemantics.Refused value offset length state.external result finalState)
    (related : ArgumentsRel arguments [.word value, .word offset, .word length] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {gasLocation : Nat} (gasMember : ⟨"availableGas", .sum .unit .word, gasLocation⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (handler : Handler layout store)
    (handlerMember : ⟨"createHandler", OptionalCell.cellType Creation.callbackType, handler.location⟩ ∈ slots)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiledBuiltin
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using create_arity rawCompiled
  obtain ⟨valueExpr, offsetExpr, lengthExpr, value', offset', length', rfl, same, rfl⟩ :=
    MemoryCopyBuiltinCorrespondence.three_words related words arity
  cases same
  obtain ⟨references, invalid, referencesCompiled, invalidCompiled, rfl⟩ := create_lowered rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word value, .word offset, .word length]
  have runtime' := runtime.temporary (bundleType [.word, .word, .word]) input
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    expression_preserves (create2 := false) (salt := Word.zero)
      (valueExpr := projectArgument 0 3 (.var 0)) (offsetExpr := projectArgument 1 3 (.var 0))
      (lengthExpr := projectArgument 2 3 (.var 0)) (saltExpr := .word Word.zero) referencesCompiled invalidCompiled computed runtime'
      passive callPassive memoryMember memorySizeMember dataMember dataSizeMember addressMember depthMember
      staticMember exitMember offsetMember sizeMember gasMember stateRelated handler handlerMember
      (.second (.second (.var rfl))) (weakened (fun _ => .first (.var rfl)))
      (weakened (fun _ => .first (.second (.var rfl)))) (weakened (fun _ => .second (.second (.var rfl))))
      (fun _ => by simp only [Core.Expr.rename, Core.Expr.weakenAt]; exact .word)
  exact ⟨resultValue, final, resultRelated, LanguageResult.bind_success .word packed evaluated, finalRelated, retained⟩

/-- CREATE2 refusals do not depend on the salt. -/
theorem create2_preserves {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    {targets : List Core.Value} {initial : Store}
    (compiledBuiltin : lowerBuiltin scope "create2" expected arguments = .ok lowered)
    (computed : CreationSemantics.Refused value offset length state.external result finalState)
    (related : ArgumentsRel arguments [.word value, .word offset, .word length, .word salt] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {gasLocation : Nat} (gasMember : ⟨"availableGas", .sum .unit .word, gasLocation⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (handler : Handler layout store)
    (handlerMember : ⟨"createHandler", OptionalCell.cellType Creation.callbackType, handler.location⟩ ∈ slots)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiledBuiltin
  have arity : arguments.length = 4 := by
    simpa only [List.length_map, List.length_range] using create2_arity rawCompiled
  obtain ⟨valueExpr, offsetExpr, lengthExpr, saltExpr, value', offset', length', salt', rfl, same, rfl⟩ :=
    AccountObservationBuiltinCorrespondence.four_words related words arity
  cases same
  obtain ⟨references, invalid, referencesCompiled, invalidCompiled, rfl⟩ := create2_lowered rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word value, .word offset, .word length, .word salt]
  have runtime' := runtime.temporary (bundleType [.word, .word, .word, .word]) input
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    expression_preserves (create2 := true) (salt := salt)
      (valueExpr := projectArgument 0 4 (.var 0)) (offsetExpr := projectArgument 1 4 (.var 0))
      (lengthExpr := projectArgument 2 4 (.var 0)) (saltExpr := projectArgument 3 4 (.var 0)) referencesCompiled invalidCompiled computed runtime'
      passive callPassive memoryMember memorySizeMember dataMember dataSizeMember addressMember depthMember
      staticMember exitMember offsetMember sizeMember gasMember stateRelated handler handlerMember
      (.first (.second (.second (.var rfl)))) (weakened (fun _ => .first (.var rfl)))
      (weakened (fun _ => .first (.second (.var rfl)))) (weakened (fun _ => .first (.second (.second (.var rfl)))))
      (weakened (fun _ => .second (.second (.second (.var rfl)))))
  exact ⟨resultValue, final, resultRelated, LanguageResult.bind_success .word packed evaluated, finalRelated, retained⟩

/-- Admitted CREATE attempts that run no init frame. -/
theorem createAdmitted_preserves {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    {targets : List Core.Value} {initial : Store}
    (compiledBuiltin : lowerBuiltin scope "create" expected arguments = .ok lowered)
    (computed : CreationSemantics.Admitted .create value offset length state.external result finalState)
    (related : ArgumentsRel arguments [.word value, .word offset, .word length] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {gasLocation : Nat} (gasMember : ⟨"availableGas", .sum .unit .word, gasLocation⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (handler : Handler layout store)
    (handlerMember : ⟨"createHandler", OptionalCell.cellType Creation.callbackType, handler.location⟩ ∈ slots)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiledBuiltin
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using create_arity rawCompiled
  obtain ⟨valueExpr, offsetExpr, lengthExpr, value', offset', length', rfl, same, rfl⟩ :=
    MemoryCopyBuiltinCorrespondence.three_words related words arity
  cases same
  obtain ⟨references, invalid, referencesCompiled, invalidCompiled, rfl⟩ := create_lowered rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word value, .word offset, .word length]
  have runtime' := runtime.temporary (bundleType [.word, .word, .word]) input
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    expression_admitted (create2 := false) (salt := Word.zero)
      (valueExpr := projectArgument 0 3 (.var 0)) (offsetExpr := projectArgument 1 3 (.var 0))
      (lengthExpr := projectArgument 2 3 (.var 0)) (saltExpr := .word Word.zero) referencesCompiled invalidCompiled rfl computed runtime'
      passive callPassive memoryMember memorySizeMember dataMember dataSizeMember addressMember depthMember
      staticMember exitMember offsetMember sizeMember gasMember stateRelated handler handlerMember
      (.second (.second (.var rfl))) (weakened (fun _ => .first (.var rfl)))
      (weakened (fun _ => .first (.second (.var rfl)))) (weakened (fun _ => .second (.second (.var rfl))))
      (fun _ => by simp only [Core.Expr.rename, Core.Expr.weakenAt]; exact .word)
  exact ⟨resultValue, final, resultRelated, LanguageResult.bind_success .word packed evaluated, finalRelated, retained⟩

/-- Admitted CREATE2 attempts that run no init frame; the salt enters the address. -/
theorem create2Admitted_preserves {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    {targets : List Core.Value} {initial : Store}
    (compiledBuiltin : lowerBuiltin scope "create2" expected arguments = .ok lowered)
    (computed : CreationSemantics.Admitted (.create2 salt) value offset length state.external result finalState)
    (related : ArgumentsRel arguments [.word value, .word offset, .word length, .word salt] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {gasLocation : Nat} (gasMember : ⟨"availableGas", .sum .unit .word, gasLocation⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (handler : Handler layout store)
    (handlerMember : ⟨"createHandler", OptionalCell.cellType Creation.callbackType, handler.location⟩ ∈ slots)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiledBuiltin
  have arity : arguments.length = 4 := by
    simpa only [List.length_map, List.length_range] using create2_arity rawCompiled
  obtain ⟨valueExpr, offsetExpr, lengthExpr, saltExpr, value', offset', length', salt', rfl, same, rfl⟩ :=
    AccountObservationBuiltinCorrespondence.four_words related words arity
  cases same
  obtain ⟨references, invalid, referencesCompiled, invalidCompiled, rfl⟩ := create2_lowered rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word value, .word offset, .word length, .word salt]
  have runtime' := runtime.temporary (bundleType [.word, .word, .word, .word]) input
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    expression_admitted (create2 := true) (salt := salt)
      (valueExpr := projectArgument 0 4 (.var 0)) (offsetExpr := projectArgument 1 4 (.var 0))
      (lengthExpr := projectArgument 2 4 (.var 0)) (saltExpr := projectArgument 3 4 (.var 0)) referencesCompiled invalidCompiled rfl computed runtime'
      passive callPassive memoryMember memorySizeMember dataMember dataSizeMember addressMember depthMember
      staticMember exitMember offsetMember sizeMember gasMember stateRelated handler handlerMember
      (.first (.second (.second (.var rfl)))) (weakened (fun _ => .first (.var rfl)))
      (weakened (fun _ => .first (.second (.var rfl)))) (weakened (fun _ => .first (.second (.second (.var rfl)))))
      (weakened (fun _ => .second (.second (.second (.var rfl)))))
  exact ⟨resultValue, final, resultRelated, LanguageResult.bind_success .word packed evaluated, finalRelated, retained⟩

end

end Solcore.Frontend.RustHull.CreationBuiltinCorrespondence
