import Solcore.Frontend.SourceRuntime.Checking
import Solcore.Core.Safety

/-! Runtime values and evaluation for the checked finite source call graph.

The import of `SourceRuntime.Checking` keeps the original
`Solcore.Frontend.SourceRuntime` import path compatible with callers that
also use its syntax and checker declarations.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | hostFunction (function : Core.HostFunction)
  | pair (left right : Value)
  | closure
      (parameters : List Parameter)
      (resultType : Core.Ty)
      (body : Expr)
      (environment : List (Resolved.LocalId × Value))
  | global (key : Key)
  | coreClosure
      (parameterType resultType : Core.Ty)
      (body : Core.Expr)
      (environment : Core.Environment)
  | inLeft (rightType : Core.Ty) (payload : Value)
  | inRight (leftType : Core.Ty) (payload : Value)
  | cellRef (elementType : Core.Ty) (location : Core.Location)
  | constructed (constructor : Core.ConstructorId) (payload : Value)
  deriving Repr

abbrev Environment := List (Resolved.LocalId × Value)

def Value.ofCore : Core.Value → Value
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .hostFunction function => .hostFunction function
  | .pair left right => .pair (ofCore left) (ofCore right)
  | .closure parameter result body environment =>
      .coreClosure parameter result body environment
  | .inLeft rightType payload => .inLeft rightType (ofCore payload)
  | .inRight leftType payload => .inRight leftType (ofCore payload)
  | .cellRef elementType location => .cellRef elementType location
  | .constructed constructor payload => .constructed constructor (ofCore payload)

def Value.toCore? : Value → Option Core.Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .hostFunction function => some (.hostFunction function)
  | .pair left right => do
      let left ← left.toCore?
      let right ← right.toCore?
      pure (.pair left right)
  | .coreClosure parameter result body environment =>
      some (.closure parameter result body environment)
  | .inLeft rightType payload =>
      return .inLeft rightType (← payload.toCore?)
  | .inRight leftType payload =>
      return .inRight leftType (← payload.toCore?)
  | .cellRef elementType location => some (.cellRef elementType location)
  | .constructed constructor payload =>
      return .constructed constructor (← payload.toCore?)
  | .closure _ _ _ _
  | .global _ => none

def Value.type? (program : Program) : Value → Option Core.Ty
  | .unit => some .unit
  | .bool _ => some .bool
  | .word _ => some .word
  | .hostFunction function => some function.functionType
  | .pair left right => do
      return .product (← left.type? program) (← right.type? program)
  | .closure parameters result _ _ =>
      some (.function (parameterType parameters) result)
  | .global key => (program.findSignature? key).map Signature.toCoreType
  | .coreClosure parameter result _ _ => some (.function parameter result)
  | .inLeft rightType payload =>
      return .sum (← payload.type? program) rightType
  | .inRight leftType payload =>
      return .sum leftType (← payload.type? program)
  | .cellRef elementType _ => some (.cell elementType)
  | .constructed constructor _ => some (.namedData constructor.owner)

/-- Public shallow runtime typing.  This records the type tag reconstructed
from a value and the finite global signature table; it does not assert that a
Core closure body, captured environment, or referenced store is well typed. -/
def Value.HasType (program : Program) (value : Value)
    (expected : Core.Ty) : Prop :=
  value.type? program = some expected

namespace Value.HasType

theorem pair
    {program : Program} {left right : Value} {leftType rightType : Core.Ty}
    (leftTyping : Value.HasType program left leftType)
    (rightTyping : Value.HasType program right rightType) :
    Value.HasType program (.pair left right) (.product leftType rightType) := by
  simp only [Value.HasType] at leftTyping rightTyping ⊢
  simp [Value.type?, leftTyping, rightTyping]

theorem inLeft
    {program : Program} {payload : Value} {leftType rightType : Core.Ty}
    (payloadTyping : Value.HasType program payload leftType) :
    Value.HasType program (.inLeft rightType payload) (.sum leftType rightType) := by
  simp only [Value.HasType] at payloadTyping ⊢
  simp [Value.type?, payloadTyping]

theorem inRight
    {program : Program} {payload : Value} {leftType rightType : Core.Ty}
    (payloadTyping : Value.HasType program payload rightType) :
    Value.HasType program (.inRight leftType payload) (.sum leftType rightType) := by
  simp only [Value.HasType] at payloadTyping ⊢
  simp [Value.type?, payloadTyping]

end Value.HasType

mutual

  /-- Deep typing of the finite graph's own values.  The Core case checks the
  projected closure body, captured Core environment, and cell world using
  Core's runtime relation.  A source closure additionally carries a checked
  body and a pointwise-deep captured lexical environment. -/
  inductive Value.GraphHasType
      (program : Program) (world : Core.StoreTyping) :
      Value → Core.Ty → (definitions : Core.DataEnvironment := []) → Prop where
    | core
        {definitions : Core.DataEnvironment}
        {value : Value} {core : Core.Value} {expected : Core.Ty} :
        value.toCore? = some core →
        Core.RuntimeValueHasType world core expected definitions →
        Value.HasType program value expected →
        Value.GraphHasType program world value expected definitions
    | pair
        {definitions : Core.DataEnvironment}
        {left right : Value} {leftType rightType : Core.Ty} :
        Value.GraphHasType program world left leftType definitions →
        Value.GraphHasType program world right rightType definitions →
        Value.GraphHasType program world (.pair left right)
          (.product leftType rightType) definitions
    | inLeft
        {definitions : Core.DataEnvironment}
        {payload : Value} {leftType rightType : Core.Ty} :
        Value.GraphHasType program world payload leftType definitions →
        Value.GraphHasType program world (.inLeft rightType payload)
          (.sum leftType rightType) definitions
    | inRight
        {definitions : Core.DataEnvironment}
        {payload : Value} {leftType rightType : Core.Ty} :
        Value.GraphHasType program world payload rightType definitions →
        Value.GraphHasType program world (.inRight leftType payload)
          (.sum leftType rightType) definitions
    | sourceClosure
        {definitions : Core.DataEnvironment}
        {parameters : List Parameter} {resultType : Core.Ty}
        {body : Expr} {environment : Environment}
        {context : StaticContext} :
        EnvironmentGraphHasTypes program world environment context definitions →
        Expr.InfersType program
          ((parameters.map fun parameter =>
            (parameter.1, StaticType.value parameter.2)) ++ context)
          body resultType →
        Value.GraphHasType program world
          (.closure parameters resultType body environment)
          (.function (parameterType parameters) resultType) definitions
    | global
        {definitions : Core.DataEnvironment} {key : Key}
        {signature : Signature} :
        program.IsWellTyped →
        program.findSignature? key = some signature →
        Value.GraphHasType program world (.global key)
          signature.toCoreType definitions

  inductive EnvironmentGraphHasTypes
      (program : Program) (world : Core.StoreTyping) :
      Environment → StaticContext →
      (definitions : Core.DataEnvironment := []) → Prop where
    | nil {definitions : Core.DataEnvironment} :
        EnvironmentGraphHasTypes program world [] [] definitions
    | cons
        {definitions : Core.DataEnvironment}
        {id : Resolved.LocalId} {value : Value} {staticType : StaticType}
        {environment : Environment} {context : StaticContext} :
        Value.GraphHasType program world value staticType.erase definitions →
        EnvironmentGraphHasTypes program world environment context definitions →
        EnvironmentGraphHasTypes program world
          ((id, value) :: environment)
          ((id, staticType) :: context) definitions

end

/-- Deep graph typing always agrees with the runtime's shallow type tag. -/
theorem Value.GraphHasType.hasType
    {program : Program} {world : Core.StoreTyping}
    {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Value.GraphHasType program world value expected definitions) :
    Value.HasType program value expected := by
  induction typing using Value.GraphHasType.rec
      (motive_2 := fun _ _ _ _ => True) with
  | core _ _ shallow => exact shallow
  | pair _ _ leftIH rightIH => exact Value.HasType.pair leftIH rightIH
  | inLeft _ payloadIH => exact Value.HasType.inLeft payloadIH
  | inRight _ payloadIH => exact Value.HasType.inRight payloadIH
  | sourceClosure => simp [Value.HasType, Value.type?]
  | global _ found => simp [Value.HasType, Value.type?, found]
  | nil => trivial
  | cons => trivial

def lookupValue?
    (environment : Environment) (id : Resolved.LocalId) : Option Value :=
  (environment.find? fun entry => decide (entry.1 = id)).map Prod.snd

def packValues : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: values => .pair value (packValues values)

/-- Recover the source parameter view from its single structural argument
bundle.  Function types deliberately erase source arity: zero parameters and
one `Unit` parameter both have bundle `Unit`, while one product parameter and
several parameters can have the same product bundle.  Applications therefore
pack the caller's arguments and unpack them according to the selected runtime
closure, rather than comparing the two source arities. -/
def unpackValues? : List Parameter → Value → Option (List Value)
  | [], .unit => some []
  | [], _ => none
  | [_], value => some [value]
  | _ :: parameter :: parameters, .pair value values => do
      let remaining ← unpackValues? (parameter :: parameters) values
      pure (value :: remaining)
  | _ :: _ :: _, _ => none

def bindParameters
    (parameters : List Parameter)
    (arguments : List Value)
    (captured : Environment) : Environment :=
  List.zip (parameters.map Prod.fst) arguments ++ captured

inductive RuntimeError where
  | missingEntry (key : Key)
  | unboundLocal (id : Resolved.LocalId)
  | unknownGlobal (key : Key)
  | expectedBool (actual : Option Core.Ty)
  | expectedWord (actual : Option Core.Ty)
  | expectedFunction (actual : Option Core.Ty)
  | invalidUnaryOperand (op : Core.UnaryOp) (actual : Option Core.Ty)
  | invalidBinaryOperands
      (op : Core.BinaryOp) (left right : Option Core.Ty)
  | entryArgumentArityMismatch
      (key : Key) (expected actual : Nat)
  | entryArgumentTypeMismatch
      (key : Key) (index : Nat) (expected actual : Core.Ty)
  | argumentArityMismatch (expected actual : Nat)
  | argumentTypeMismatch
      (index : Nat) (expected : Core.Ty) (actual : Option Core.Ty)
  | resultTypeMismatch (expected : Core.Ty) (actual : Option Core.Ty)
  | nonCoreArgument (index : Nat)
  | coreFault (error : Core.MachineFault)
  deriving Repr, DecidableEq

inductive RunResult where
  | done (value : Value) (store : Core.Store)
  | outOfFuel (store : Core.Store)
  | fault (error : RuntimeError) (store : Core.Store)
  deriving Repr

inductive ArgumentsResult where
  | done (values : List Value) (store : Core.Store)
  | outOfFuel (store : Core.Store)
  | fault (error : RuntimeError) (store : Core.Store)

def evaluateArguments
    (evaluateOne : Core.Store → Expr → RunResult) :
    Core.Store → List Expr → ArgumentsResult
  | store, [] => .done [] store
  | store, argument :: arguments =>
      match evaluateOne store argument with
      | .done value nextStore =>
          match evaluateArguments evaluateOne nextStore arguments with
          | .done values finalStore => .done (value :: values) finalStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | .outOfFuel finalStore => .outOfFuel finalStore
      | .fault error finalStore => .fault error finalStore

def applyValue
    (program : Program)
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (coreFuel : Nat)
    (function : Value)
    (arguments : List Value)
    (store : Core.Store) : RunResult :=
  let invoke
      (parameters : List Parameter)
      (resultType : Core.Ty)
      (body : Expr)
      (captured : Environment) : RunResult :=
    let bundled := packValues arguments
    let expectedType := parameterType parameters
    let actualType := bundled.type? program
    if actualType != some expectedType then
      .fault (.argumentTypeMismatch 0 expectedType actualType) store
    else
      match unpackValues? parameters bundled with
      | some normalized =>
          match evaluateBody
              (bindParameters parameters normalized captured) store body with
          | .done value finalStore =>
              if value.type? program = some resultType then
                .done value finalStore
              else
                .fault (.resultTypeMismatch resultType (value.type? program))
                  finalStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | none =>
          .fault (.argumentArityMismatch parameters.length arguments.length) store
  match function with
  | .closure parameters resultType body captured =>
      invoke parameters resultType body captured
  | .global key =>
      match program.findDefinition? key with
      | some definition =>
          invoke definition.parameters definition.resultType definition.body []
      | none => .fault (.unknownGlobal key) store
  | .coreClosure parameterType resultType body captured =>
      let bundled := packValues arguments
      if bundled.type? program != some parameterType then
        .fault (.argumentTypeMismatch 0 parameterType (bundled.type? program)) store
      else
        match bundled.toCore? with
        | none => .fault (.nonCoreArgument 0) store
        | some argument =>
            match Core.runStateful coreFuel
                (Core.State.initial body (argument :: captured) store) with
            | .done value finalStore =>
                if value.type = resultType then
                  .done (.ofCore value) finalStore
                else
                  .fault (.resultTypeMismatch resultType (some value.type))
                    finalStore
            | .outOfFuel state => .outOfFuel state.store
            | .fault error state => .fault (.coreFault error) state.store
  | actual => .fault (.expectedFunction (actual.type? program)) store

def evaluate
    (fuel : Nat)
    (program : Program)
    (environment : Environment)
    (store : Core.Store)
    (expression : Expr) : RunResult :=
  match fuel with
  | 0 => .outOfFuel store
  | remaining + 1 =>
      let descend := evaluate remaining program environment
      match expression with
      | .unit => .done .unit store
      | .bool value => .done (.bool value) store
      | .word value => .done (.word value) store
      | .local id =>
          match lookupValue? environment id with
          | some value => .done value store
          | none => .fault (.unboundLocal id) store
      | .pair left right =>
          match descend store left with
          | .done leftValue rightStore =>
              match descend rightStore right with
              | .done rightValue finalStore =>
                  .done (.pair leftValue rightValue) finalStore
              | .outOfFuel finalStore => .outOfFuel finalStore
              | .fault error finalStore => .fault error finalStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | .unary op operand =>
          match descend store operand with
          | .done value finalStore =>
              match value.toCore? with
              | some coreValue =>
                  match op.apply coreValue with
                  | some result => .done (.ofCore result) finalStore
                  | none =>
                      .fault (.invalidUnaryOperand op (value.type? program)) finalStore
              | none =>
                  .fault (.invalidUnaryOperand op (value.type? program)) finalStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | .binary op left right =>
          match descend store left with
          | .done leftValue rightStore =>
              match descend rightStore right with
              | .done rightValue finalStore =>
                  match leftValue.toCore?, rightValue.toCore? with
                  | some coreLeft, some coreRight =>
                      match op.apply coreLeft coreRight with
                      | some result => .done (.ofCore result) finalStore
                      | none => .fault
                          (.invalidBinaryOperands op
                            (leftValue.type? program) (rightValue.type? program))
                          finalStore
                  | _, _ => .fault
                      (.invalidBinaryOperands op
                        (leftValue.type? program) (rightValue.type? program))
                      finalStore
              | .outOfFuel finalStore => .outOfFuel finalStore
              | .fault error finalStore => .fault error finalStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | .wordLt left right =>
          match descend store left with
          | .done (.word leftValue) rightStore =>
              match descend rightStore right with
              | .done (.word rightValue) finalStore =>
                  .done (.bool (decide (leftValue < rightValue))) finalStore
              | .done actual finalStore =>
                  .fault (.expectedWord (actual.type? program)) finalStore
              | .outOfFuel finalStore => .outOfFuel finalStore
              | .fault error finalStore => .fault error finalStore
          | .done actual finalStore =>
              .fault (.expectedWord (actual.type? program)) finalStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | .letE binder value body =>
          match descend store value with
          | .done boundValue bodyStore =>
              evaluate remaining program ((binder, boundValue) :: environment)
                bodyStore body
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | .ifE condition thenBranch elseBranch =>
          match descend store condition with
          | .done (.bool true) branchStore => descend branchStore thenBranch
          | .done (.bool false) branchStore => descend branchStore elseBranch
          | .done actual branchStore =>
              .fault (.expectedBool (actual.type? program)) branchStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore
      | .global key =>
          if (program.findDefinition? key).isSome then
            .done (.global key) store
          else
            .fault (.unknownGlobal key) store
      | .lambda parameters resultType body =>
          .done (.closure parameters resultType body environment) store
      | .apply function arguments =>
          match descend store function with
          | .done functionValue argumentStore =>
              match evaluateArguments descend argumentStore arguments with
              | .done argumentValues finalStore =>
                  applyValue program
                    (evaluate remaining program) remaining
                    functionValue argumentValues finalStore
              | .outOfFuel finalStore => .outOfFuel finalStore
              | .fault error finalStore => .fault error finalStore
          | .outOfFuel finalStore => .outOfFuel finalStore
          | .fault error finalStore => .fault error finalStore

private def validateEntryArgumentTypes (key : Key) :
    Nat → List Core.Ty → List Core.Value → Option RuntimeError
  | index, expected :: expectedTypes, actual :: actualValues =>
      if actual.type = expected then
        validateEntryArgumentTypes key (index + 1) expectedTypes actualValues
      else
        some (.entryArgumentTypeMismatch key index expected actual.type)
  | _, _, _ => none

private def validateEntryArguments
    (key : Key)
    (signature : Signature)
    (arguments : List Core.Value) : Option RuntimeError :=
  if signature.parameterTypes.length != arguments.length then
    some (.entryArgumentArityMismatch
      key signature.parameterTypes.length arguments.length)
  else
    validateEntryArgumentTypes key 0 signature.parameterTypes arguments

private theorem validateEntryArgumentTypes_self
    (key : Key) (index : Nat) (arguments : List Core.Value) :
    validateEntryArgumentTypes key index
      (arguments.map Core.Value.type) arguments = none := by
  induction arguments generalizing index with
  | nil => rfl
  | cons argument arguments ih =>
      simp [validateEntryArgumentTypes, ih]

private theorem validateEntryArguments_none_of_type_tags
    (key : Key) (signature : Signature) (arguments : List Core.Value)
    (typesEqual : arguments.map Core.Value.type = signature.parameterTypes) :
    validateEntryArguments key signature arguments = none := by
  unfold validateEntryArguments
  rw [← typesEqual]
  simp [validateEntryArgumentTypes_self]

/-- Execute a checked global entry.  Arguments are validated before any body
is entered, and recursive calls share the same finite global table. -/
def CheckedProgram.run
    (checked : CheckedProgram)
    (fuel : Nat)
    (entry : Key)
    (arguments : List Core.Value)
    (store : Core.Store := []) : RunResult :=
  match checked.program.findDefinition? entry with
  | none => .fault (.missingEntry entry) store
  | some definition =>
      match validateEntryArguments entry definition.signature
          arguments with
      | some error => .fault error store
      | none =>
          match fuel with
          | 0 => .outOfFuel store
          | _ =>
              applyValue checked.program
                (evaluate fuel checked.program) fuel
                (.global entry) (arguments.map Value.ofCore) store

/-- Deep runtime typing implies this shallow premise, but the executable entry
gate itself needs only exact ordered type tags.  At zero execution fuel a
matching invocation reaches the observable fuel boundary without changing the
store. -/
theorem CheckedProgram.run_zero_of_matching_types
    (checked : CheckedProgram) (entry : Key) (definition : Definition)
    (arguments : List Core.Value) (store : Core.Store)
    (found : checked.program.findDefinition? entry = some definition)
    (typesEqual : arguments.map Core.Value.type =
      definition.signature.parameterTypes) :
    checked.run 0 entry arguments store = .outOfFuel store := by
  simp [CheckedProgram.run, found,
    validateEntryArguments_none_of_type_tags entry definition.signature
      arguments typesEqual]

/-- Every successful entry run carries the result type declared by the
selected definition.  This shallow result-tag property follows from the
runtime's outer result check, so it also holds for a manually constructed
`CheckedProgram`; no static-checking premise is required. -/
theorem CheckedProgram.run_done_hasType
    (checked : CheckedProgram) (fuel : Nat) (entry : Key)
    (arguments : List Core.Value) (initialStore finalStore : Core.Store)
    (value : Value)
    (completed : checked.run fuel entry arguments initialStore =
      .done value finalStore) :
    ∃ definition,
      checked.program.findDefinition? entry = some definition ∧
      checked.entrySignature? entry = some definition.signature ∧
      Value.HasType checked.program value definition.resultType := by
  unfold CheckedProgram.run at completed
  split at completed
  · contradiction
  · rename_i definition found
    split at completed
    · contradiction
    · split at completed
      · contradiction
      · refine ⟨definition, found, ?_, ?_⟩
        · simp [CheckedProgram.entrySignature?, Program.findSignature?, found]
        · unfold applyValue at completed
          simp only [found] at completed
          split at completed <;> try contradiction
          split at completed <;> try contradiction
          split at completed <;> try contradiction
          split at completed <;> try contradiction
          rename_i resultTypeMatches
          cases completed
          exact resultTypeMatches

/-- Project a finished runtime value back to the Core value boundary.  Lexical
closures and named globals deliberately have no Core projection. -/
def RunResult.toCore? : RunResult → Option (Core.Value × Core.Store)
  | .done value store => value.toCore?.map fun core => (core, store)
  | .outOfFuel _
  | .fault _ _ => none


end Solcore.Frontend.SourceRuntime

/-!
## Consolidated module: `Solcore.Frontend.SourceRuntimeProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.SourceRuntimeStaticInversionProperties`
-/

/-! Inversion lemmas for the finite graph's executable static checker. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- A checked pair exposes both checked children and the product result. -/
theorem Expr.InfersType.pair_components
    {program : Program} {context : StaticContext}
    {left right : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.pair left right) expected) :
    ∃ leftType rightType,
      Expr.InfersType program context left leftType ∧
      Expr.InfersType program context right rightType ∧
      expected = .product leftType rightType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases leftResult : infer program context left with
  | error error =>
      simp [leftResult, bind, Except.bind] at inferredAt
  | ok leftStatic =>
      cases rightResult : infer program context right with
      | error error =>
          simp [leftResult, rightResult, bind, Except.bind] at inferredAt
      | ok rightStatic =>
          simp [leftResult, rightResult, bind, Except.bind] at inferredAt
          cases inferredAt
          exact ⟨leftStatic.erase, rightStatic.erase,
            ⟨leftStatic, leftResult, rfl⟩,
            ⟨rightStatic, rightResult, rfl⟩,
            by simpa [StaticType.erase] using erased.symm⟩

/-- A successful nonempty argument inference consists of a successful head
inference followed by successful inference of the tail, with no omitted or
reordered result types. -/
theorem inferList_cons_ok
    (program : Program) (context : StaticContext)
    (expression : Expr) (expressions : List Expr)
    (types : List StaticType)
    (success : inferList program context (expression :: expressions) =
      .ok types) :
    ∃ head tail,
      infer program context expression = .ok head ∧
      inferList program context expressions = .ok tail ∧
      types = head :: tail := by
  unfold inferList at success
  cases headResult : infer program context expression with
  | error error =>
      simp [headResult, bind, Except.bind] at success
  | ok head =>
      cases tailResult : inferList program context expressions with
      | error error =>
          simp [headResult, tailResult, bind, Except.bind] at success
      | ok tail =>
          simp [headResult, tailResult, bind, Except.bind] at success
          simp only [pure, Pure.pure, Except.pure] at success
          exact ⟨head, tail, rfl, rfl, (Except.ok.inj success).symm⟩

/-- Successful inference preserves argument-list length. -/
theorem inferList_ok_length
    (program : Program) (context : StaticContext) :
    ∀ (expressions : List Expr) (types : List StaticType),
      inferList program context expressions = .ok types →
      expressions.length = types.length := by
  intro expressions
  induction expressions with
  | nil =>
      intro types success
      simp [inferList] at success
      cases success
      rfl
  | cons expression expressions ih =>
      intro types success
      obtain ⟨head, tail, _, tailOk, typesEq⟩ :=
        inferList_cons_ok program context expression expressions types success
      subst types
      simp [ih tail tailOk]

end Solcore.Frontend.SourceRuntime

/-!
## Consolidated module: `Solcore.Frontend.SourceRuntimeStaticOperatorProperties`
-/

/-! Inversions of successful source-graph inference for primitive operations. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

theorem Expr.InfersType.unary_components
    {program : Program} {context : StaticContext}
    {op : Core.UnaryOp} {operand : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.unary op operand) expected) :
    Expr.InfersType program context operand op.operandType ∧
      expected = op.resultType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases operandResult : infer program context operand with
  | error error =>
      simp [operandResult, bind, Except.bind] at inferredAt
  | ok operandType =>
      by_cases equal : operandType.erase = op.operandType
      · simp [operandResult, checkExpected, equal, bind, Except.bind]
          at inferredAt
        cases inferredAt
        exact ⟨⟨operandType, operandResult, equal⟩,
          by simpa [StaticType.erase] using erased.symm⟩
      · simp [operandResult, checkExpected, equal, bind, Except.bind]
          at inferredAt

theorem Expr.InfersType.binary_components
    {program : Program} {context : StaticContext}
    {op : Core.BinaryOp} {left right : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.binary op left right) expected) :
    Expr.InfersType program context left op.leftType ∧
      Expr.InfersType program context right op.rightType ∧
      expected = op.resultType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases leftResult : infer program context left with
  | error error =>
      simp [leftResult, bind, Except.bind] at inferredAt
  | ok leftType =>
      by_cases leftMatches : leftType.erase = op.leftType
      · cases rightResult : infer program context right with
        | error error =>
            simp [leftResult, rightResult, checkExpected, leftMatches,
              bind, Except.bind] at inferredAt
            change Except.error error = Except.ok inferred at inferredAt
            cases inferredAt
        | ok rightType =>
            by_cases rightMatches : rightType.erase = op.rightType
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              cases inferredAt
              exact ⟨⟨leftType, leftResult, leftMatches⟩,
                ⟨rightType, rightResult, rightMatches⟩,
                by simpa [StaticType.erase] using erased.symm⟩
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              change Except.error (TypeError.typeMismatch op.rightType rightType.erase) =
                Except.ok inferred at inferredAt
              cases inferredAt
      · simp [leftResult, checkExpected, leftMatches, bind, Except.bind]
          at inferredAt

theorem Expr.InfersType.wordLt_components
    {program : Program} {context : StaticContext}
    {left right : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.wordLt left right) expected) :
    Expr.InfersType program context left .word ∧
      Expr.InfersType program context right .word ∧
      expected = .bool := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases leftResult : infer program context left with
  | error error =>
      simp [leftResult, bind, Except.bind] at inferredAt
  | ok leftType =>
      by_cases leftMatches : leftType.erase = Core.Ty.word
      · cases rightResult : infer program context right with
        | error error =>
            simp [leftResult, rightResult, checkExpected, leftMatches,
              bind, Except.bind] at inferredAt
            change Except.error error = Except.ok inferred at inferredAt
            cases inferredAt
        | ok rightType =>
            by_cases rightMatches : rightType.erase = Core.Ty.word
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              cases inferredAt
              exact ⟨⟨leftType, leftResult, leftMatches⟩,
                ⟨rightType, rightResult, rightMatches⟩,
                by simpa [StaticType.erase] using erased.symm⟩
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              change Except.error (TypeError.typeMismatch .word rightType.erase) =
                Except.ok inferred at inferredAt
              cases inferredAt
      · simp [leftResult, checkExpected, leftMatches, bind, Except.bind]
          at inferredAt

theorem Expr.InfersType.ifE_components
    {program : Program} {context : StaticContext}
    {condition thenBranch elseBranch : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context
      (.ifE condition thenBranch elseBranch) expected) :
    Expr.InfersType program context condition .bool ∧
      Expr.InfersType program context thenBranch expected ∧
      Expr.InfersType program context elseBranch expected := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases conditionResult : infer program context condition with
  | error error =>
      simp [conditionResult, bind, Except.bind] at inferredAt
  | ok conditionType =>
      by_cases conditionMatches : conditionType.erase = Core.Ty.bool
      · cases thenResult : infer program context thenBranch with
        | error error =>
            simp [conditionResult, thenResult, checkExpected,
              conditionMatches, bind, Except.bind] at inferredAt
            change Except.error error = Except.ok inferred at inferredAt
            cases inferredAt
        | ok thenType =>
            cases elseResult : infer program context elseBranch with
            | error error =>
                simp [conditionResult, thenResult, elseResult,
                  checkExpected, conditionMatches, bind, Except.bind]
                  at inferredAt
                change Except.error error = Except.ok inferred at inferredAt
                cases inferredAt
            | ok elseType =>
                by_cases sameType : thenType = elseType
                · subst elseType
                  simp [conditionResult, thenResult, elseResult,
                    checkExpected, conditionMatches,
                    bind, Except.bind] at inferredAt
                  change Except.ok thenType = Except.ok inferred at inferredAt
                  have inferredEq : inferred = thenType :=
                    Except.ok.inj inferredAt.symm
                  subst inferred
                  exact ⟨⟨conditionType, conditionResult,
                    conditionMatches⟩,
                    ⟨thenType, thenResult, erased⟩,
                    ⟨thenType, elseResult, erased⟩⟩
                · by_cases sameErased : thenType.erase = elseType.erase
                  · simp [conditionResult, thenResult, elseResult,
                      checkExpected, conditionMatches, sameType,
                      sameErased, bind, Except.bind] at inferredAt
                    change Except.ok (.value elseType.erase) =
                      Except.ok inferred at inferredAt
                    have inferredEq : inferred = .value elseType.erase :=
                      Except.ok.inj inferredAt.symm
                    subst inferred
                    have elseErased : elseType.erase = expected := by
                      simpa [StaticType.erase] using erased
                    have thenErased : thenType.erase = expected :=
                      sameErased.trans elseErased
                    exact ⟨⟨conditionType, conditionResult,
                      conditionMatches⟩,
                      ⟨thenType, thenResult, thenErased⟩,
                      ⟨elseType, elseResult, elseErased⟩⟩
                  · simp [conditionResult, thenResult, elseResult,
                      checkExpected, conditionMatches, sameType,
                      sameErased, bind, Except.bind] at inferredAt
                    change Except.error (TypeError.typeMismatch
                      thenType.erase elseType.erase) =
                      Except.ok inferred at inferredAt
                    cases inferredAt
      · simp [conditionResult, checkExpected, conditionMatches,
          bind, Except.bind] at inferredAt

theorem Expr.InfersType.letE_components
    {program : Program} {context : StaticContext}
    {binder : Resolved.LocalId} {value body : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context
      (.letE binder value body) expected) :
    ∃ boundType,
      Expr.InfersType program context value boundType.erase ∧
      Expr.InfersType program ((binder, boundType) :: context) body expected := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  split at inferredAt
  · simp [bind, Except.bind] at inferredAt
  · cases valueResult : infer program context value with
    | error error =>
        simp [valueResult, bind, Except.bind] at inferredAt
    | ok boundType =>
        cases bodyResult : infer program ((binder, boundType) :: context) body with
        | error error =>
            simp [valueResult, bodyResult, bind, Except.bind] at inferredAt
        | ok bodyType =>
            simp [valueResult, bodyResult, bind, Except.bind] at inferredAt
            have inferredEq : inferred = bodyType :=
              inferredAt.symm
            subst inferred
            exact ⟨boundType,
              ⟨boundType, valueResult, rfl⟩,
              ⟨bodyType, bodyResult, erased⟩⟩

end Solcore.Frontend.SourceRuntime
