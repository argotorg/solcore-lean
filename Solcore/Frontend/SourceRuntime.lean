import Solcore.Core.Safety
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

/-- The distinction between a callable source value and an ordinary value of
function type, retained by the finite-graph checker. -/
inductive StaticType where
  | value (type : Core.Ty)
  | callable (parameterTypes : List Core.Ty) (resultType : Core.Ty)
  deriving Repr, DecidableEq

def StaticType.erase : StaticType → Core.Ty
  | .value type => type
  | .callable parameters result => .function (bundleType parameters) result

abbrev StaticContext := List (Resolved.LocalId × StaticType)

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

def lookupStatic?
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

def checkExpected (expected : Core.Ty) (actual : StaticType) :
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

  def infer
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

  def inferList
      (program : Program)
      (context : StaticContext) : List Expr → Except TypeError (List StaticType)
    | [] => pure []
    | expression :: expressions => do
        let type ← infer program context expression
        let types ← inferList program context expressions
        pure (type :: types)

end

/-- A reusable static certificate for a source expression.  The inferred
callability distinction is retained in the context, while the conclusion is
the public Core type of the resulting value. -/
def Expr.InfersType (program : Program) (context : StaticContext)
    (expression : Expr) (expected : Core.Ty) : Prop :=
  ∃ inferred, infer program context expression = .ok inferred ∧
    inferred.erase = expected

/-- Parameter identities do not affect the runtime's structural bundle type. -/
theorem parameterType_eq_bundleType_map
    (parameters : List Parameter) :
    parameterType parameters = bundleType (parameters.map Prod.snd) := by
  induction parameters with
  | nil => rfl
  | cons parameter parameters ih =>
      cases parameters with
      | nil => rfl
      | cons next rest =>
          simp [parameterType, bundleType, ih]

/-- A successful lambda inference certifies its actual body under the
captured context and the exact parameter binders, and fixes its erased
function type. -/
theorem Expr.InfersType.lambda_body
    {program : Program} {context : StaticContext}
    {parameters : List Parameter} {resultType : Core.Ty}
    {body : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context
      (.lambda parameters resultType body) expected) :
    Expr.InfersType program
        ((parameters.map fun parameter =>
          (parameter.1, StaticType.value parameter.2)) ++ context)
        body resultType ∧
      expected = .function (parameterType parameters) resultType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases duplicates : firstDuplicateLocal? (context.map Prod.fst) parameters with
  | some id =>
      simp [duplicates, bind, Except.bind] at inferredAt
  | none =>
      cases bodyResult : infer program
          ((parameters.map fun parameter =>
            (parameter.1, StaticType.value parameter.2)) ++ context)
          body with
      | error error =>
          simp [duplicates, bodyResult, bind, Except.bind] at inferredAt
      | ok bodyType =>
          by_cases equal : bodyType.erase = resultType
          · simp [duplicates, bodyResult, checkExpected, equal,
              bind, Except.bind] at inferredAt
            cases inferredAt
            refine ⟨⟨bodyType, bodyResult, equal⟩, ?_⟩
            simpa [StaticType.erase, parameterType_eq_bundleType_map] using
              erased.symm
          · simp [duplicates, bodyResult, checkExpected, equal,
              bind, Except.bind] at inferredAt

/-- Successful application inference exposes the exact structural argument
bundle and the function's erased input/output type, regardless of whether
the callee was statically callable or an ordinary function-valued expression. -/
theorem Expr.InfersType.apply_components
    {program : Program} {context : StaticContext}
    {function : Expr} {arguments : List Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context
      (.apply function arguments) expected) :
    ∃ functionType argumentTypes parameterType resultType,
      infer program context function = .ok functionType ∧
      inferList program context arguments = .ok argumentTypes ∧
      functionType.erase = .function parameterType resultType ∧
      bundleType (argumentTypes.map StaticType.erase) = parameterType ∧
      expected = resultType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases functionResult : infer program context function with
  | error error =>
      simp [functionResult, bind, Except.bind] at inferredAt
  | ok functionType =>
      cases argumentsResult : inferList program context arguments with
      | error error =>
          simp [functionResult, argumentsResult, bind, Except.bind]
            at inferredAt
      | ok argumentTypes =>
          cases functionType with
          | callable expectedTypes resultType =>
              by_cases bundleEqual :
                  bundleType (argumentTypes.map StaticType.erase) =
                    bundleType expectedTypes
              · simp [functionResult, argumentsResult,
                  checkBundledArguments, bundleEqual,
                  bind, Except.bind] at inferredAt
                cases inferredAt
                refine ⟨.callable expectedTypes resultType,
                  argumentTypes, bundleType expectedTypes, resultType,
                  rfl, rfl, rfl, bundleEqual, ?_⟩
                simpa [StaticType.erase] using erased.symm
              · simp [functionResult, argumentsResult,
                  checkBundledArguments, bundleEqual,
                  bind, Except.bind] at inferredAt
          | value actual =>
              cases actual with
              | function parameterType resultType =>
                  by_cases bundleEqual :
                      bundleType (argumentTypes.map StaticType.erase) =
                        parameterType
                  · simp [functionResult, argumentsResult, bundleEqual,
                      bind, Except.bind] at inferredAt
                    cases inferredAt
                    refine ⟨.value (.function parameterType resultType),
                      argumentTypes, parameterType, resultType,
                      rfl, rfl, rfl, bundleEqual, ?_⟩
                    simpa [StaticType.erase] using erased.symm
                  · simp [functionResult, argumentsResult, bundleEqual,
                      bind, Except.bind] at inferredAt
              | unit => simp [functionResult, argumentsResult,
                    bind, Except.bind] at inferredAt
              | bool => simp [functionResult, argumentsResult,
                    bind, Except.bind] at inferredAt
              | word => simp [functionResult, argumentsResult,
                    bind, Except.bind] at inferredAt
              | product _ _ => simp [functionResult, argumentsResult,
                    bind, Except.bind] at inferredAt
              | sum _ _ => simp [functionResult, argumentsResult,
                    bind, Except.bind] at inferredAt
              | cell _ => simp [functionResult, argumentsResult,
                    bind, Except.bind] at inferredAt
              | namedData _ => simp [functionResult, argumentsResult,
                    bind, Except.bind] at inferredAt

/-- A program whose finite definition table and every body have been checked. -/
structure CheckedProgram where
  program : Program
  deriving Repr

private def checkDefinitions (program : Program) :
    List Definition → Except TypeError Unit
  | [] => pure ()
  | definition :: definitions => do
      match firstDuplicateLocal? [] definition.parameters with
      | some id => throw (.duplicateLocal id)
      | none => pure ()
      let context := definition.parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2)
      let actual ← infer program context definition.body
      if actual.erase = definition.resultType then
        checkDefinitions program definitions
      else
        throw (.definitionResultMismatch
          definition.key definition.resultType actual.erase)

/-- Every definition traversed by a successful whole-table body check has a
body whose inferred type is its declared result type. -/
private theorem checkDefinitions_ok_forall (program : Program) :
    ∀ definitions,
      checkDefinitions program definitions = .ok () →
      ∀ definition, definition ∈ definitions →
        Expr.InfersType program
          (definition.parameters.map fun parameter =>
            (parameter.1, StaticType.value parameter.2))
          definition.body definition.resultType := by
  intro definitions
  induction definitions with
  | nil =>
      intro _ definition member
      cases member
  | cons head rest inductionHypothesis =>
      intro accepted definition member
      unfold checkDefinitions at accepted
      cases duplicate : firstDuplicateLocal? [] head.parameters with
      | some id =>
          simp [duplicate, bind, Except.bind] at accepted
      | none =>
          simp only [duplicate, bind, Except.bind] at accepted
          cases inferred : infer program
              (head.parameters.map fun parameter =>
                (parameter.1, StaticType.value parameter.2)) head.body with
          | error error =>
              simp [inferred] at accepted
          | ok actual =>
              simp only [inferred] at accepted
              by_cases same : actual.erase = head.resultType
              · have restAccepted : checkDefinitions program rest = .ok () := by
                  simpa [same] using accepted
                rcases List.mem_cons.mp member with selected | later
                · subst definition
                  exact ⟨actual, inferred, same⟩
                · exact inductionHypothesis restAccepted definition later
              · simp [same] at accepted

def Program.check (program : Program) : Except TypeError CheckedProgram := do
  match firstDuplicateDefinition? [] program.definitions with
  | some key => throw (.duplicateDefinition key)
  | none => pure ()
  checkDefinitions program program.definitions
  pure ⟨program⟩

/-- Whole-table checking supplies a static typing derivation for each actual
definition body. This is the global-call case needed by graph evaluation
preservation, and it depends on a real checker success rather than the
forgeable `CheckedProgram` wrapper alone. -/
theorem Program.check_definition_hasType
    (program : Program) (checked : CheckedProgram)
    (accepted : program.check = .ok checked)
    (definition : Definition) (member : definition ∈ program.definitions) :
    Expr.InfersType program
      (definition.parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2))
      definition.body definition.resultType := by
  unfold Program.check at accepted
  cases duplicate : firstDuplicateDefinition? [] program.definitions with
  | some key =>
      simp [duplicate, bind, Except.bind] at accepted
  | none =>
      simp only [duplicate, bind, Except.bind] at accepted
      cases bodies : checkDefinitions program program.definitions with
      | error error =>
          simp [bodies] at accepted
      | ok success =>
          cases success
          exact checkDefinitions_ok_forall program program.definitions bodies
            definition member

/-- Unlike the forgeable `CheckedProgram` carrier, this predicate records an
actual successful pass of the whole-program checker. -/
def Program.IsWellTyped (program : Program) : Prop :=
  ∃ checked, program.check = .ok checked

/-- A non-forgeable checked-program witness yields the body typing of a
definition selected by the executable lookup. -/
theorem Program.IsWellTyped.foundDefinition_hasType
    {program : Program} (wellTyped : program.IsWellTyped)
    {key : Key} {definition : Definition}
    (found : program.findDefinition? key = some definition) :
    Expr.InfersType program
      (definition.parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2))
      definition.body definition.resultType := by
  obtain ⟨checked, accepted⟩ := wellTyped
  exact program.check_definition_hasType checked accepted definition
    (List.mem_of_find?_eq_some found)

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
