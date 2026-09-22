import Solcore.Core.Safety
import Solcore.Frontend.SourceSpecialization

/-! Static syntax and whole-program checking for the finite source call graph.

Global signatures are collected before checking bodies, so recursive and
mutually recursive definitions use the same lookup as forward references.
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


end Solcore.Frontend.SourceRuntime
