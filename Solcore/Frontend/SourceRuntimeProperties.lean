import Solcore.Frontend.SourceRuntime
import Solcore.Core.Safety

/-! Focused executable checks for the finite runtime call graph. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- Deep typing for the Core-projectable part of `SourceRuntime.Value`.
Unlike `Value.HasType`, this validates Core closure bodies and captured
environments and relates cell references to one concrete store-typing world.
Source-native closures and named globals are intentionally outside this
boundary relation because `Value.toCore?` does not project them. -/
def Value.RuntimeHasType
    (world : Core.StoreTyping) (value : Value) (expected : Core.Ty)
    (definitions : Core.DataEnvironment := []) : Prop :=
  ∃ core,
    value.toCore? = some core ∧
    Core.RuntimeValueHasType world core expected definitions

/-- Pointwise deep typing for an ordered source-runtime value list. -/
def ValuesRuntimeHaveTypes
    (world : Core.StoreTyping) (values : List Value) (types : List Core.Ty)
    (definitions : Core.DataEnvironment := []) : Prop :=
  ∃ coreValues,
    values = coreValues.map Value.ofCore ∧
    Core.RuntimeEnvironmentHasTypes world coreValues types definitions

/-- Embedding a Core value and projecting it immediately is lossless. -/
@[simp] theorem Value.toCore?_ofCore : (value : Core.Value) →
    (Value.ofCore value).toCore? = some value
  | .unit => rfl
  | .bool _ => rfl
  | .word _ => rfl
  | .hostFunction _ => rfl
  | .pair left right => by
      simp [Value.ofCore, Value.toCore?, Value.toCore?_ofCore left,
        Value.toCore?_ofCore right]
  | .closure _ _ _ _ => rfl
  | .inLeft _ payload => by
      simp [Value.ofCore, Value.toCore?, Value.toCore?_ofCore payload]
  | .inRight _ payload => by
      simp [Value.ofCore, Value.toCore?, Value.toCore?_ofCore payload]
  | .cellRef _ _ => rfl
  | .constructed _ payload => by
      simp [Value.ofCore, Value.toCore?, Value.toCore?_ofCore payload]

/-- Any successful Core projection exposes the same shallow type tag on the
source-runtime side. -/
theorem Value.hasType_of_toCore?
    (program : Program) : (value : Value) → (core : Core.Value) →
    value.toCore? = some core → Value.HasType program value core.type
  | .unit, core, projected => by
      simp [Value.toCore?, Value.HasType] at projected ⊢
      cases projected
      rfl
  | .bool value, core, projected => by
      simp [Value.toCore?, Value.HasType] at projected ⊢
      cases projected
      rfl
  | .word value, core, projected => by
      simp [Value.toCore?, Value.HasType] at projected ⊢
      cases projected
      rfl
  | .hostFunction function, core, projected => by
      simp [Value.toCore?, Value.HasType] at projected ⊢
      cases projected
      rfl
  | .pair left right, core, projected => by
      cases leftProjection : left.toCore? with
      | none => simp [Value.toCore?, leftProjection] at projected
      | some coreLeft =>
          cases rightProjection : right.toCore? with
          | none =>
              simp [Value.toCore?, leftProjection, rightProjection] at projected
          | some coreRight =>
              simp [Value.toCore?, leftProjection, rightProjection] at projected
              cases projected
              have leftTyping :=
                Value.hasType_of_toCore? program left coreLeft leftProjection
              have rightTyping :=
                Value.hasType_of_toCore? program right coreRight rightProjection
              exact Value.HasType.pair leftTyping rightTyping
  | .closure _ _ _ _, core, projected => by
      simp [Value.toCore?] at projected
  | .global _, core, projected => by
      simp [Value.toCore?] at projected
  | .coreClosure _ _ _ _, core, projected => by
      simp [Value.toCore?, Value.HasType] at projected ⊢
      cases projected
      rfl
  | .inLeft rightType payload, core, projected => by
      cases payloadProjection : payload.toCore? with
      | none => simp [Value.toCore?, payloadProjection] at projected
      | some corePayload =>
          simp [Value.toCore?, payloadProjection] at projected
          cases projected
          have payloadTyping :=
            Value.hasType_of_toCore? program payload corePayload
              payloadProjection
          exact Value.HasType.inLeft payloadTyping
  | .inRight leftType payload, core, projected => by
      cases payloadProjection : payload.toCore? with
      | none => simp [Value.toCore?, payloadProjection] at projected
      | some corePayload =>
          simp [Value.toCore?, payloadProjection] at projected
          cases projected
          have payloadTyping :=
            Value.hasType_of_toCore? program payload corePayload
              payloadProjection
          exact Value.HasType.inRight payloadTyping
  | .cellRef _ _, core, projected => by
      simp [Value.toCore?, Value.HasType] at projected ⊢
      cases projected
      rfl
  | .constructed _ payload, core, projected => by
      cases payloadProjection : payload.toCore? with
      | none => simp [Value.toCore?, payloadProjection] at projected
      | some corePayload =>
          simp [Value.toCore?, payloadProjection] at projected
          cases projected
          rfl

/-- Deep Core typing transports across the public Core-to-source embedding. -/
theorem Value.runtimeHasType_ofCore
    {world : Core.StoreTyping} {core : Core.Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Core.RuntimeValueHasType world core expected definitions) :
    (Value.ofCore core).RuntimeHasType world expected definitions :=
  ⟨core, Value.toCore?_ofCore core, typing⟩

/-- The deep boundary relation always implies the public shallow tag
relation. -/
theorem Value.RuntimeHasType.hasType
    {world : Core.StoreTyping} {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : value.RuntimeHasType world expected definitions)
    (program : Program) :
    Value.HasType program value expected := by
  obtain ⟨core, projected, coreTyping⟩ := typing
  have shallow := Value.hasType_of_toCore? program value core projected
  simpa [coreTyping.type_eq] using shallow

/-- Projecting a deeply typed boundary value recovers a deeply typed Core
value, not merely a matching structural tag. -/
theorem Value.RuntimeHasType.toCore
    {world : Core.StoreTyping} {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : value.RuntimeHasType world expected definitions)
    {core : Core.Value} (projected : value.toCore? = some core) :
    Core.RuntimeValueHasType world core expected definitions := by
  obtain ⟨typedCore, typedProjection, coreTyping⟩ := typing
  rw [projected] at typedProjection
  cases typedProjection
  exact coreTyping

/-- A deeply typed Core environment remains deeply typed, pointwise, after
the runner's `Value.ofCore` input conversion. -/
theorem ValuesRuntimeHaveTypes.ofCore
    {world : Core.StoreTyping} {environment : Core.Environment}
    {context : Core.Context} {definitions : Core.DataEnvironment}
    (typing : Core.RuntimeEnvironmentHasTypes world environment context
      definitions) :
    ValuesRuntimeHaveTypes world (environment.map Value.ofCore) context
      definitions := by
  exact ⟨environment, rfl, typing⟩

/-- Deep premises for calling one finite graph entry.  Static program validity
is deliberately separate because `CheckedProgram` remains a forgeable public
carrier; this structure records only the selected definition, Core input
typing, and the store world they share. -/
structure CheckedProgram.RuntimeInputsHaveType
    (checked : CheckedProgram) (entry : Key)
    (arguments : List Core.Value) (store : Core.Store)
    (definition : Definition) (world : Core.StoreTyping)
    (definitions : Core.DataEnvironment := []) : Prop where
  found : checked.program.findDefinition? entry = some definition
  argumentsTyping : Core.RuntimeEnvironmentHasTypes world arguments
    definition.signature.parameterTypes definitions
  storeTyping : Core.StoreHasTypes world store

/-- The runner's input conversion preserves every deep Core input premise. -/
theorem CheckedProgram.RuntimeInputsHaveType.convertedArguments
    {checked : CheckedProgram} {entry : Key}
    {arguments : List Core.Value} {store : Core.Store}
    {definition : Definition} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typing : checked.RuntimeInputsHaveType entry arguments store definition
      world definitions) :
    ValuesRuntimeHaveTypes world (arguments.map Value.ofCore)
      definition.signature.parameterTypes definitions :=
  ValuesRuntimeHaveTypes.ofCore typing.argumentsTyping

/-- Deeply typed inputs necessarily pass the shallow entry gate.  Zero
execution fuel is therefore reported as fuel exhaustion with the exact initial
store, rather than as an argument fault. -/
theorem CheckedProgram.RuntimeInputsHaveType.run_zero
    {checked : CheckedProgram} {entry : Key}
    {arguments : List Core.Value} {store : Core.Store}
    {definition : Definition} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typing : checked.RuntimeInputsHaveType entry arguments store definition
      world definitions) :
    checked.run 0 entry arguments store = .outOfFuel store :=
  checked.run_zero_of_matching_types entry definition arguments store
    typing.found typing.argumentsTyping.type_tags

@[simp] theorem Program.findDefinition?_empty (key : Key) :
    ({ definitions := [] : Program }).findDefinition? key = none := by
  rfl

@[simp] theorem Program.findSignature?_empty (key : Key) :
    ({ definitions := [] : Program }).findSignature? key = none := by
  rfl

/-- Public signature-facing form of successful result-tag preservation. -/
theorem CheckedProgram.run_done_has_signature_type
    (checked : CheckedProgram) (fuel : Nat) (entry : Key)
    (arguments : List Core.Value) (initialStore finalStore : Core.Store)
    (value : Value) (signature : Signature)
    (found : checked.entrySignature? entry = some signature)
    (completed : checked.run fuel entry arguments initialStore =
      .done value finalStore) :
    Value.HasType checked.program value signature.resultType := by
  obtain ⟨definition, _, definitionSignature, valueType⟩ :=
    checked.run_done_hasType fuel entry arguments initialStore finalStore value
      completed
  rw [found] at definitionSignature
  cases definitionSignature
  exact valueType

/-- First outer-run preservation bridge.  It retains the deeply typed input
conversion and initial store invariant while adding the declared shallow type
of a successful result.  Proving a typed *final* store requires the subsequent
evaluator preservation theorem. -/
theorem CheckedProgram.RuntimeInputsHaveType.run_done_boundary
    {checked : CheckedProgram} {fuel : Nat} {entry : Key}
    {arguments : List Core.Value} {initialStore finalStore : Core.Store}
    {value : Value} {definitions : Core.DataEnvironment}
    {definition : Definition} {world : Core.StoreTyping}
    (typing : checked.RuntimeInputsHaveType entry arguments initialStore
      definition world definitions)
    (completed : checked.run fuel entry arguments initialStore =
      .done value finalStore) :
    ValuesRuntimeHaveTypes world (arguments.map Value.ofCore)
        definition.signature.parameterTypes definitions ∧
      Core.StoreHasTypes world initialStore ∧
      Value.HasType checked.program value definition.resultType := by
  have signatureFound : checked.entrySignature? entry =
      some definition.signature := by
    simp [CheckedProgram.entrySignature?, Program.findSignature?, typing.found]
  exact ⟨typing.convertedArguments, typing.storeTyping,
    checked.run_done_has_signature_type fuel entry arguments initialStore
      finalStore value definition.signature signatureFound completed⟩

private def testPath : Workspace.ModulePath :=
  ⟨[⟨"Runtime", by decide⟩], by decide⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, testPath⟩, index⟩

private def key (index : Nat) : Key :=
  ⟨declaration index, []⟩

private def localId (owner binder : Nat) : Resolved.LocalId :=
  ⟨declaration owner, binder⟩

private def leftParameter : Parameter := (localId 0 0, .bool)
private def rightParameter : Parameter := (localId 1 0, .bool)

/-- A deliberately nonterminating mutual cycle.  Checking succeeds because all
global signatures are collected before either body is inspected. -/
private def cyclicProgram : Program := {
  definitions := [
    {
      key := key 0
      parameters := [leftParameter]
      resultType := .bool
      body := .apply (.global (key 1)) [.local leftParameter.1]
    },
    {
      key := key 1
      parameters := [rightParameter]
      resultType := .bool
      body := .apply (.global (key 0)) [.local rightParameter.1]
    }
  ]
}

example : cyclicProgram.check = .ok ⟨cyclicProgram⟩ := by
  rfl

example (store : Core.Store) :
    (⟨cyclicProgram⟩ : CheckedProgram).run 12 (key 0) [.bool true] store =
      .outOfFuel store := by
  rfl

private def captureParameter : Parameter := (localId 2 0, .bool)
private def lambdaBinder : Resolved.LocalId := localId 2 1
private def lambdaParameter : Parameter := (localId 2 2, .bool)

/-- The lambda ignores its argument and returns a captured entry parameter. -/
private def closureDefinition : Definition := {
    key := key 2
    parameters := [captureParameter]
    resultType := .bool
    body := .letE lambdaBinder
      (.lambda [lambdaParameter] .bool (.local captureParameter.1))
      (.apply (.local lambdaBinder) [.bool false])
}

private def closureProgram : Program := {
  definitions := [closureDefinition]
}

private theorem closureInputsHaveType :
    (⟨closureProgram⟩ : CheckedProgram).RuntimeInputsHaveType
      (key 2) [.bool true] [] closureDefinition [] := by
  exact {
    found := rfl
    argumentsTyping := .cons .bool .nil
    storeTyping := .nil
  }

private theorem closedCoreClosureHasType :
    Core.RuntimeValueHasType []
      (.closure .unit .unit .unit []) (.function .unit .unit) := by
  exact .closure .nil .unit

example : closureProgram.check = .ok ⟨closureProgram⟩ := by
  rfl

example (store : Core.Store) :
    (⟨closureProgram⟩ : CheckedProgram).run 8 (key 2) [.bool true] store =
      .done (.bool true) store := by
  rfl

example (store : Core.Store) :
    Value.HasType closureProgram (.bool true) .bool := by
  apply CheckedProgram.run_done_has_signature_type
    (⟨closureProgram⟩ : CheckedProgram) 8 (key 2) [.bool true]
      store store (.bool true)
      { parameterTypes := [.bool], resultType := .bool }
  · rfl
  · rfl

example :
    ValuesRuntimeHaveTypes [] [Value.ofCore (.bool true)] [.bool] := by
  simpa [closureDefinition, Definition.signature, captureParameter] using
    closureInputsHaveType.convertedArguments

example : Value.HasType closureProgram (.bool true) .bool := by
  have boundary := closureInputsHaveType.run_done_boundary
    (fuel := 8) (finalStore := []) (value := .bool true) (by rfl)
  exact boundary.2.2

example :
    (Value.ofCore (.closure .unit .unit .unit [])).RuntimeHasType []
      (.function .unit .unit) :=
  Value.runtimeHasType_ofCore closedCoreClosureHasType

example :
    (⟨closureProgram⟩ : CheckedProgram).run 0 (key 2) [.bool true] [] =
      .outOfFuel [] :=
  closureInputsHaveType.run_zero

example (store : Core.Store) :
    (⟨closureProgram⟩ : CheckedProgram).run 8 (key 2) [] store =
      .fault (.entryArgumentArityMismatch (key 2) 1 0) store := by
  rfl

example (store : Core.Store) :
    (⟨closureProgram⟩ : CheckedProgram).run 8 (key 2)
        [.word Core.Word.zero] store =
      .fault (.entryArgumentTypeMismatch (key 2) 0 .bool .word) store := by
  rfl

end Solcore.Frontend.SourceRuntime
