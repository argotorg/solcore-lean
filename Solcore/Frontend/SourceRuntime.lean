import Solcore.Frontend.SourceRuntime.Checking

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
