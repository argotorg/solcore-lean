import Solcore.Core.Machine
import Solcore.Frontend.SourceSpecialization

/-!
A finite, runtime-linked call graph for specialized source functions.

Unlike `Core.Expr`, this representation names global functions instead of
inlining their bodies.  Consequently a finite `Program` can represent direct
recursion and mutually recursive strongly-connected components.  Lambdas keep
their source-local parameter identities and evaluate to lexical closures.

The executable checker first collects every global signature and only then
checks bodies.  References around a cycle are therefore ordinary forward
references, not a special case in the checker.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

abbrev Key := SourceSpecialization.SpecializationKey

abbrev Parameter := Resolved.LocalId × Core.Ty

/-- The source convention for a function's argument bundle. -/
def parameterType : List Parameter → Core.Ty
  | [] => .unit
  | [parameter] => parameter.2
  | parameter :: parameters => .product parameter.2 (parameterType parameters)

inductive Expr where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | local (id : Resolved.LocalId)
  | pair (left right : Expr)
  | unary (op : Core.UnaryOp) (operand : Expr)
  | binary (op : Core.BinaryOp) (left right : Expr)
  | wordLt (left right : Expr)
  | letE (binder : Resolved.LocalId) (value body : Expr)
  | ifE (condition thenBranch elseBranch : Expr)
  | global (key : Key)
  | lambda
      (parameters : List Parameter)
      (resultType : Core.Ty)
      (body : Expr)
  | apply (function : Expr) (arguments : List Expr)
  deriving Repr

structure Signature where
  parameterTypes : List Core.Ty
  resultType : Core.Ty
  deriving Repr, BEq, DecidableEq

structure Definition where
  key : Key
  parameters : List Parameter
  resultType : Core.Ty
  body : Expr
  deriving Repr

def Definition.signature (definition : Definition) : Signature := {
  parameterTypes := definition.parameters.map Prod.snd
  resultType := definition.resultType
}

structure Program where
  definitions : List Definition
  deriving Repr

def Program.findDefinition? (program : Program) (key : Key) : Option Definition :=
  program.definitions.find? fun definition => definition.key == key

def Program.findSignature? (program : Program) (key : Key) : Option Signature :=
  (program.findDefinition? key).map Definition.signature

/-- The argument-bundle convention after binder identities have been erased. -/
def bundleType : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: types => .product type (bundleType types)

def Signature.toCoreType (signature : Signature) : Core.Ty :=
  .function (bundleType signature.parameterTypes) signature.resultType

private inductive StaticType where
  | value (type : Core.Ty)
  | callable (parameterTypes : List Core.Ty) (resultType : Core.Ty)
  deriving Repr, DecidableEq

private def StaticType.erase : StaticType → Core.Ty
  | .value type => type
  | .callable parameters result => .function (bundleType parameters) result

private abbrev StaticContext := List (Resolved.LocalId × StaticType)

inductive TypeError where
  | duplicateDefinition (key : Key)
  | duplicateLocal (id : Resolved.LocalId)
  | unknownLocal (id : Resolved.LocalId)
  | unknownGlobal (key : Key)
  | typeMismatch (expected actual : Core.Ty)
  | expectedFunction (actual : Core.Ty)
  | argumentArityMismatch (expected actual : Nat)
  | argumentTypeMismatch
      (index : Nat) (expected actual : Core.Ty)
  | definitionResultMismatch
      (key : Key) (expected actual : Core.Ty)
  deriving Repr, DecidableEq

private def lookupStatic?
    (context : StaticContext)
    (id : Resolved.LocalId) : Option StaticType :=
  (context.find? fun entry => decide (entry.1 = id)).map Prod.snd

private def containsLocal (context : StaticContext) (id : Resolved.LocalId) : Bool :=
  context.any fun entry => decide (entry.1 = id)

private def firstDuplicateLocal?
    (seen : List Resolved.LocalId) : List Parameter → Option Resolved.LocalId
  | [] => none
  | parameter :: parameters =>
      if parameter.1 ∈ seen then some parameter.1
      else firstDuplicateLocal? (parameter.1 :: seen) parameters

private def firstDuplicateDefinition?
    (seen : List Key) : List Definition → Option Key
  | [] => none
  | definition :: definitions =>
      if seen.any fun key => key == definition.key then some definition.key
      else firstDuplicateDefinition? (definition.key :: seen) definitions

private def checkExpected (expected : Core.Ty) (actual : StaticType) :
    Except TypeError Unit :=
  if actual.erase = expected then pure ()
  else throw (.typeMismatch expected actual.erase)

private def checkBundledArguments
    (expected : List Core.Ty)
    (actual : List StaticType) : Except TypeError Unit := do
  let expectedBundle := bundleType expected
  let actualBundle := bundleType (actual.map StaticType.erase)
  if actualBundle = expectedBundle then pure ()
  else throw (.typeMismatch expectedBundle actualBundle)

mutual

  private def infer
      (program : Program)
      (context : StaticContext) : Expr → Except TypeError StaticType
    | .unit => pure (.value .unit)
    | .bool _ => pure (.value .bool)
    | .word _ => pure (.value .word)
    | .local id =>
        match lookupStatic? context id with
        | some type => pure type
        | none => throw (.unknownLocal id)
    | .pair left right => do
        let leftType ← infer program context left
        let rightType ← infer program context right
        pure (.value (.product leftType.erase rightType.erase))
    | .unary op operand => do
        let operandType ← infer program context operand
        checkExpected op.operandType operandType
        pure (.value op.resultType)
    | .binary op left right => do
        let leftType ← infer program context left
        checkExpected op.leftType leftType
        let rightType ← infer program context right
        checkExpected op.rightType rightType
        pure (.value op.resultType)
    | .wordLt left right => do
        let leftType ← infer program context left
        checkExpected .word leftType
        let rightType ← infer program context right
        checkExpected .word rightType
        pure (.value .bool)
    | .letE binder value body => do
        if containsLocal context binder then
          throw (.duplicateLocal binder)
        let valueType ← infer program context value
        infer program ((binder, valueType) :: context) body
    | .ifE condition thenBranch elseBranch => do
        let conditionType ← infer program context condition
        checkExpected .bool conditionType
        let thenType ← infer program context thenBranch
        let elseType ← infer program context elseBranch
        if thenType = elseType then
          pure thenType
        else if thenType.erase = elseType.erase then
          pure (.value thenType.erase)
        else
          throw (.typeMismatch thenType.erase elseType.erase)
    | .global key =>
        match program.findSignature? key with
        | some signature =>
            pure (.callable signature.parameterTypes signature.resultType)
        | none => throw (.unknownGlobal key)
    | .lambda parameters resultType body => do
        match firstDuplicateLocal? (context.map Prod.fst) parameters with
        | some id => throw (.duplicateLocal id)
        | none => pure ()
        let parameterContext := parameters.map fun parameter =>
          (parameter.1, StaticType.value parameter.2)
        let bodyType ← infer program (parameterContext ++ context) body
        checkExpected resultType bodyType
        pure (.callable (parameters.map Prod.snd) resultType)
    | .apply function arguments => do
        let functionType ← infer program context function
        let argumentTypes ← inferList program context arguments
        match functionType with
        | .callable expected result =>
            checkBundledArguments expected argumentTypes
            pure (.value result)
        | .value (.function expected result) =>
            let actual := bundleType (argumentTypes.map StaticType.erase)
            if actual = expected then pure (.value result)
            else throw (.typeMismatch expected actual)
        | .value actual => throw (.expectedFunction actual)

  private def inferList
      (program : Program)
      (context : StaticContext) : List Expr → Except TypeError (List StaticType)
    | [] => pure []
    | expression :: expressions => do
        let type ← infer program context expression
        let types ← inferList program context expressions
        pure (type :: types)

end

/-- A program whose finite definition table and every body have been checked. -/
structure CheckedProgram where
  program : Program
  deriving Repr

def Program.check (program : Program) : Except TypeError CheckedProgram := do
  match firstDuplicateDefinition? [] program.definitions with
  | some key => throw (.duplicateDefinition key)
  | none => pure ()
  for definition in program.definitions do
    match firstDuplicateLocal? [] definition.parameters with
    | some id => throw (.duplicateLocal id)
    | none => pure ()
    let context := definition.parameters.map fun parameter =>
      (parameter.1, StaticType.value parameter.2)
    let actual ← infer program context definition.body
    if actual.erase != definition.resultType then
      throw (.definitionResultMismatch
        definition.key definition.resultType actual.erase)
  pure ⟨program⟩

def CheckedProgram.entrySignature?
    (checked : CheckedProgram) (key : Key) : Option Signature :=
  checked.program.findSignature? key

def CheckedProgram.inputTypes?
    (checked : CheckedProgram) (key : Key) : Option (List Core.Ty) :=
  (checked.entrySignature? key).map (fun signature => signature.parameterTypes)

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

private def Value.type? (program : Program) : Value → Option Core.Ty
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

private def lookupValue?
    (environment : Environment) (id : Resolved.LocalId) : Option Value :=
  (environment.find? fun entry => decide (entry.1 = id)).map Prod.snd

private def packValues : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: values => .pair value (packValues values)

/-- Recover the source parameter view from its single structural argument
bundle.  Function types deliberately erase source arity: zero parameters and
one `Unit` parameter both have bundle `Unit`, while one product parameter and
several parameters can have the same product bundle.  Applications therefore
pack the caller's arguments and unpack them according to the selected runtime
closure, rather than comparing the two source arities. -/
private def unpackValues? : List Parameter → Value → Option (List Value)
  | [], .unit => some []
  | [], _ => none
  | [_], value => some [value]
  | _ :: parameter :: parameters, .pair value values => do
      let remaining ← unpackValues? (parameter :: parameters) values
      pure (value :: remaining)
  | _ :: _ :: _, _ => none

private def bindParameters
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
  | nonCoreArgument (index : Nat)
  | coreFault (error : Core.MachineFault)
  deriving Repr, DecidableEq

inductive RunResult where
  | done (value : Value) (store : Core.Store)
  | outOfFuel (store : Core.Store)
  | fault (error : RuntimeError) (store : Core.Store)
  deriving Repr

private inductive ArgumentsResult where
  | done (values : List Value) (store : Core.Store)
  | outOfFuel (store : Core.Store)
  | fault (error : RuntimeError) (store : Core.Store)

private def evaluateArguments
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

private def firstArgumentMismatch?
    (program : Program)
    (expected : List Core.Ty)
    (actual : List Value) : Option (Nat × Core.Ty × Option Core.Ty) :=
  let rec loop (index : Nat) :
      List Core.Ty → List Value → Option (Nat × Core.Ty × Option Core.Ty)
    | expectedType :: expectedTypes, value :: values =>
        let actualType := value.type? program
        if actualType = some expectedType then
          loop (index + 1) expectedTypes values
        else
          some (index, expectedType, actualType)
    | _, _ => none
  loop 0 expected actual

private def applyValue
    (program : Program)
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (coreFuel : Nat)
    (function : Value)
    (arguments : List Value)
    (store : Core.Store) : RunResult :=
  let invoke
      (parameters : List Parameter)
      (_resultType : Core.Ty)
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
          evaluateBody (bindParameters parameters normalized captured) store body
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
  | .coreClosure parameterType _ body captured =>
      let bundled := packValues arguments
      if bundled.type? program != some parameterType then
        .fault (.argumentTypeMismatch 0 parameterType (bundled.type? program)) store
      else
        match bundled.toCore? with
        | none => .fault (.nonCoreArgument 0) store
        | some argument =>
            match Core.runStateful coreFuel
                (Core.State.initial body (argument :: captured) store) with
            | .done value finalStore => .done (.ofCore value) finalStore
            | .outOfFuel state => .outOfFuel state.store
            | .fault error state => .fault (.coreFault error) state.store
  | actual => .fault (.expectedFunction (actual.type? program)) store

private def evaluate
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

private def validateEntryArguments
    (key : Key)
    (signature : Signature)
    (arguments : List Core.Value) : Option RuntimeError :=
  if signature.parameterTypes.length != arguments.length then
    some (.entryArgumentArityMismatch
      key signature.parameterTypes.length arguments.length)
  else
    let rec loop (index : Nat) :
        List Core.Ty → List Core.Value → Option RuntimeError
      | expected :: expectedTypes, actual :: actualValues =>
          if actual.type = expected then
            loop (index + 1) expectedTypes actualValues
          else
            some (.entryArgumentTypeMismatch key index expected actual.type)
      | _, _ => none
    loop 0 signature.parameterTypes arguments

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

/-- Project a finished runtime value back to the Core value boundary.  Lexical
closures and named globals deliberately have no Core projection. -/
def RunResult.toCore? : RunResult → Option (Core.Value × Core.Store)
  | .done value store => value.toCore?.map fun core => (core, store)
  | .outOfFuel _
  | .fault _ _ => none

end Solcore.Frontend.SourceRuntime
