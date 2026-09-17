import Solcore.Core.Typing

set_option autoImplicit false

namespace Solcore.Core

inductive CheckPathStep where
  | pairLeft
  | pairRight
  | firstOperand
  | secondOperand
  | lambdaBody
  | applyFunction
  | applyArgument
  | inLeftPayload
  | inRightPayload
  | caseScrutinee
  | caseLeftBranch
  | caseRightBranch
  | newCellInitializer
  | loadCellReference
  | storeCellReference
  | storeCellValue
  | constructPayload
  | matchScrutinee
  | matchBranch (index : Nat)
  | unaryOperand
  | binaryLeft
  | binaryRight
  | ternaryFirst
  | ternarySecond
  | ternaryThird
  | letValue
  | letBody
  | ifCondition
  | ifThen
  | ifElse
  deriving Repr, BEq, DecidableEq

abbrev CheckPath := List CheckPathStep

def CheckPath.child (path : CheckPath) (step : CheckPathStep) : CheckPath :=
  path ++ [step]

inductive CheckErrorCode where
  | unboundVariable
  | expectedBool
  | expectedProduct
  | expectedFunction
  | functionArgumentTypeMismatch
  | lambdaResultTypeMismatch
  | expectedSum
  | caseBranchTypeMismatch
  | invalidCellPayload
  | cellInitializerTypeMismatch
  | expectedCell
  | cellValueTypeMismatch
  | invalidDefinitionPayload
  | unknownNamedDataType
  | unknownDataType
  | unknownConstructor
  | constructorPayloadTypeMismatch
  | expectedNamedData
  | matchDataTypeMismatch
  | matchBranchCountMismatch
  | matchBranchResultTypeMismatch
  | invalidResultType
  | primitiveOperandTypeMismatch
  | branchTypeMismatch
  | declaredResultTypeMismatch
  | inferenceFailure
  deriving Repr, BEq, DecidableEq

def CheckErrorCode.name : CheckErrorCode → String
  | .unboundVariable => "core.check.unbound-variable"
  | .expectedBool => "core.check.expected-bool"
  | .expectedProduct => "core.check.expected-product"
  | .expectedFunction => "core.check.expected-function"
  | .functionArgumentTypeMismatch =>
      "core.check.function-argument-type-mismatch"
  | .lambdaResultTypeMismatch => "core.check.lambda-result-type-mismatch"
  | .expectedSum => "core.check.expected-sum"
  | .caseBranchTypeMismatch => "core.check.case-branch-type-mismatch"
  | .invalidCellPayload => "core.check.invalid-cell-payload"
  | .cellInitializerTypeMismatch =>
      "core.check.cell-initializer-type-mismatch"
  | .expectedCell => "core.check.expected-cell"
  | .cellValueTypeMismatch => "core.check.cell-value-type-mismatch"
  | .invalidDefinitionPayload => "core.check.invalid-definition-payload"
  | .unknownNamedDataType => "core.check.unknown-named-data-type"
  | .unknownDataType => "core.check.unknown-data-type"
  | .unknownConstructor => "core.check.unknown-constructor"
  | .constructorPayloadTypeMismatch =>
      "core.check.constructor-payload-type-mismatch"
  | .expectedNamedData => "core.check.expected-named-data"
  | .matchDataTypeMismatch => "core.check.match-data-type-mismatch"
  | .matchBranchCountMismatch => "core.check.match-branch-count-mismatch"
  | .matchBranchResultTypeMismatch =>
      "core.check.match-branch-result-type-mismatch"
  | .invalidResultType => "core.check.invalid-result-type"
  | .primitiveOperandTypeMismatch =>
      "core.check.primitive-operand-type-mismatch"
  | .branchTypeMismatch => "core.check.branch-type-mismatch"
  | .declaredResultTypeMismatch => "core.check.declared-result-type-mismatch"
  | .inferenceFailure => "core.check.inference-failure"

inductive CheckErrorData where
  | unboundVariable (index contextSize : Nat)
  | expectedBool (actual : Ty)
  | expectedProduct (actual : Ty)
  | expectedFunction (actual : Ty)
  | functionArgumentTypeMismatch (expected actual : Ty)
  | lambdaResultTypeMismatch (declared actual : Ty)
  | expectedSum (actual : Ty)
  | caseBranchTypeMismatch (leftType rightType : Ty)
  | invalidCellPayload (actual : Ty)
  | cellInitializerTypeMismatch (expected actual : Ty)
  | expectedCell (actual : Ty)
  | cellValueTypeMismatch (expected actual : Ty)
  | invalidDefinitionPayload
      (dataTypeIndex constructorIndex : Nat)
      (actual : Ty)
  | unknownNamedDataType (dataType : DataTypeId)
  | unknownDataType (dataType : DataTypeId)
  | unknownConstructor (constructor : ConstructorId)
  | constructorPayloadTypeMismatch (expected actual : Ty)
  | expectedNamedData (actual : Ty)
  | matchDataTypeMismatch (expected actual : DataTypeId)
  | matchBranchCountMismatch (expected actual : Nat)
  | matchBranchResultTypeMismatch
      (branchIndex : Nat)
      (expected actual : Ty)
  | invalidResultType (actual : Ty)
  | primitiveOperandTypeMismatch (expected actual : Ty)
  | branchTypeMismatch (thenType elseType : Ty)
  | declaredResultTypeMismatch (declaredType inferredType : Ty)
  | inferenceFailure
  deriving Repr, BEq, DecidableEq

def CheckErrorData.code : CheckErrorData → CheckErrorCode
  | .unboundVariable .. => .unboundVariable
  | .expectedBool .. => .expectedBool
  | .expectedProduct .. => .expectedProduct
  | .expectedFunction .. => .expectedFunction
  | .functionArgumentTypeMismatch .. => .functionArgumentTypeMismatch
  | .lambdaResultTypeMismatch .. => .lambdaResultTypeMismatch
  | .expectedSum .. => .expectedSum
  | .caseBranchTypeMismatch .. => .caseBranchTypeMismatch
  | .invalidCellPayload .. => .invalidCellPayload
  | .cellInitializerTypeMismatch .. => .cellInitializerTypeMismatch
  | .expectedCell .. => .expectedCell
  | .cellValueTypeMismatch .. => .cellValueTypeMismatch
  | .invalidDefinitionPayload .. => .invalidDefinitionPayload
  | .unknownNamedDataType .. => .unknownNamedDataType
  | .unknownDataType .. => .unknownDataType
  | .unknownConstructor .. => .unknownConstructor
  | .constructorPayloadTypeMismatch .. => .constructorPayloadTypeMismatch
  | .expectedNamedData .. => .expectedNamedData
  | .matchDataTypeMismatch .. => .matchDataTypeMismatch
  | .matchBranchCountMismatch .. => .matchBranchCountMismatch
  | .matchBranchResultTypeMismatch .. => .matchBranchResultTypeMismatch
  | .invalidResultType .. => .invalidResultType
  | .primitiveOperandTypeMismatch .. => .primitiveOperandTypeMismatch
  | .branchTypeMismatch .. => .branchTypeMismatch
  | .declaredResultTypeMismatch .. => .declaredResultTypeMismatch
  | .inferenceFailure => .inferenceFailure

structure CheckError where
  path : CheckPath
  data : CheckErrorData
  deriving Repr, BEq, DecidableEq

def CheckError.code (error : CheckError) : CheckErrorCode :=
  error.data.code

def CheckError.codeName (error : CheckError) : String :=
  error.code.name

private def firstUnknownNamedDataType?
    (definitions : DataEnvironment) : Ty → Option DataTypeId
  | .unit
  | .bool
  | .word => none
  | .product left right
  | .function left right
  | .sum left right =>
      match firstUnknownNamedDataType? definitions left with
      | some dataType => some dataType
      | none => firstUnknownNamedDataType? definitions right
  | .cell elementType => firstUnknownNamedDataType? definitions elementType
  | .namedData dataType =>
      match definitions.lookupDataType? dataType with
      | some _ => none
      | none => some dataType

private def invalidTypeError
    (definitions : DataEnvironment)
    (path : CheckPath)
    (type : Ty) : CheckError :=
  match firstUnknownNamedDataType? definitions type with
  | some dataType => { path, data := .unknownNamedDataType dataType }
  | none => { path, data := .invalidResultType type }

private def firstInvalidPayloadInDefinition?
    (definitions : DataEnvironment)
    (dataTypeIndex constructorIndex : Nat) : List Ty → Option CheckErrorData
  | [] => none
  | payloadType :: payloadTypes =>
      if payloadType.isConstructorPayload definitions then
        firstInvalidPayloadInDefinition?
          definitions dataTypeIndex (constructorIndex + 1) payloadTypes
      else
        some (.invalidDefinitionPayload
          dataTypeIndex constructorIndex payloadType)

private def firstInvalidDefinitionPayloadAux?
    (definitions : DataEnvironment)
    (dataTypeIndex : Nat) : List DataDefinition → Option CheckErrorData
  | [] => none
  | definition :: remaining =>
      match firstInvalidPayloadInDefinition?
          definitions dataTypeIndex 0 definition.constructorPayloadTypes with
      | some error => some error
      | none =>
          firstInvalidDefinitionPayloadAux?
            definitions (dataTypeIndex + 1) remaining

def DataEnvironment.firstInvalidPayload?
    (definitions : DataEnvironment) : Option CheckErrorData :=
  firstInvalidDefinitionPayloadAux? definitions 0 definitions

private def definitionTableError (definitions : DataEnvironment) : CheckError :=
  match definitions.firstInvalidPayload? with
  | some data => { path := [], data }
  | none => { path := [], data := .inferenceFailure }

mutual

  private def diagnoseWithFuel :
      Nat → DataEnvironment → Context → CheckPath → Expr → CheckError
    | 0, _, _, path, _ => { path, data := .inferenceFailure }
    | fuel + 1, definitions, context, path, expr =>
        match expr with
        | .unit
        | .bool _
        | .word _ => { path, data := .inferenceFailure }
        | .var index =>
            { path, data := .unboundVariable index context.length }
        | .pair left right =>
            match infer? context left definitions with
            | none =>
                diagnoseWithFuel fuel definitions context
                  (path.child .pairLeft) left
            | some _ =>
                diagnoseWithFuel fuel definitions context
                  (path.child .pairRight) right
        | .first operand =>
            let operandPath := path.child .firstOperand
            match infer? context operand definitions with
            | none =>
                diagnoseWithFuel fuel definitions context operandPath operand
            | some (.product _ _) => { path, data := .inferenceFailure }
            | some actual => { path := operandPath, data := .expectedProduct actual }
        | .second operand =>
            let operandPath := path.child .secondOperand
            match infer? context operand definitions with
            | none =>
                diagnoseWithFuel fuel definitions context operandPath operand
            | some (.product _ _) => { path, data := .inferenceFailure }
            | some actual => { path := operandPath, data := .expectedProduct actual }
        | .lambda parameterType resultType body =>
            if parameterType.isWellFormed definitions then
              if resultType.isWellFormed definitions then
                let bodyPath := path.child .lambdaBody
                match infer? (parameterType :: context) body definitions with
                | none =>
                    diagnoseWithFuel fuel definitions (parameterType :: context)
                      bodyPath body
                | some actual =>
                    { path := bodyPath,
                      data := .lambdaResultTypeMismatch resultType actual }
              else
                invalidTypeError definitions path resultType
            else
              invalidTypeError definitions path parameterType
        | .apply function argument =>
            let functionPath := path.child .applyFunction
            match infer? context function definitions with
            | none =>
                diagnoseWithFuel fuel definitions context functionPath function
            | some (.function parameterType _) =>
                let argumentPath := path.child .applyArgument
                match infer? context argument definitions with
                | none =>
                    diagnoseWithFuel fuel definitions context argumentPath argument
                | some actual =>
                    { path := argumentPath,
                      data := .functionArgumentTypeMismatch parameterType actual }
            | some actual =>
                { path := functionPath, data := .expectedFunction actual }
        | .inLeft rightType payload =>
            if rightType.isWellFormed definitions then
              diagnoseWithFuel fuel definitions context
                (path.child .inLeftPayload) payload
            else
              invalidTypeError definitions path rightType
        | .inRight leftType payload =>
            if leftType.isWellFormed definitions then
              diagnoseWithFuel fuel definitions context
                (path.child .inRightPayload) payload
            else
              invalidTypeError definitions path leftType
        | .caseE scrutinee leftBranch rightBranch =>
            let scrutineePath := path.child .caseScrutinee
            match infer? context scrutinee definitions with
            | none =>
                diagnoseWithFuel fuel definitions context scrutineePath scrutinee
            | some (.sum leftType rightType) =>
                let leftPath := path.child .caseLeftBranch
                match infer? (leftType :: context) leftBranch definitions with
                | none =>
                    diagnoseWithFuel fuel definitions (leftType :: context)
                      leftPath leftBranch
                | some leftResultType =>
                    let rightPath := path.child .caseRightBranch
                    match infer? (rightType :: context) rightBranch definitions with
                    | none =>
                        diagnoseWithFuel fuel definitions (rightType :: context)
                          rightPath rightBranch
                    | some rightResultType =>
                        { path := rightPath,
                          data := .caseBranchTypeMismatch
                            leftResultType rightResultType }
            | some actual =>
                { path := scrutineePath, data := .expectedSum actual }
        | .newCell elementType initializer =>
            let initializerPath := path.child .newCellInitializer
            match infer? context initializer definitions with
            | none =>
                diagnoseWithFuel fuel definitions context initializerPath initializer
            | some actual =>
                if actual = elementType then
                  { path, data := .invalidCellPayload elementType }
                else
                  { path := initializerPath,
                    data := .cellInitializerTypeMismatch elementType actual }
        | .loadCell reference =>
            let referencePath := path.child .loadCellReference
            match infer? context reference definitions with
            | none =>
                diagnoseWithFuel fuel definitions context referencePath reference
            | some (.cell elementType) =>
                { path := referencePath, data := .invalidCellPayload elementType }
            | some actual => { path := referencePath, data := .expectedCell actual }
        | .storeCell reference value =>
            let referencePath := path.child .storeCellReference
            match infer? context reference definitions with
            | none =>
                diagnoseWithFuel fuel definitions context referencePath reference
            | some (.cell elementType) =>
                if elementType.isCellPayload then
                  let valuePath := path.child .storeCellValue
                  match infer? context value definitions with
                  | none =>
                      diagnoseWithFuel fuel definitions context valuePath value
                  | some actual =>
                      { path := valuePath,
                        data := .cellValueTypeMismatch elementType actual }
                else
                  { path := referencePath, data := .invalidCellPayload elementType }
            | some actual => { path := referencePath, data := .expectedCell actual }
        | .construct constructor payload =>
            match definitions.lookupDataType? constructor.owner with
            | none => { path, data := .unknownDataType constructor.owner }
            | some definition =>
                match definition.constructorPayloadTypes[constructor.index]? with
                | none => { path, data := .unknownConstructor constructor }
                | some payloadType =>
                    let payloadPath := path.child .constructPayload
                    match infer? context payload definitions with
                    | none =>
                        diagnoseWithFuel fuel definitions context payloadPath payload
                    | some actual =>
                        { path := payloadPath,
                          data := .constructorPayloadTypeMismatch payloadType actual }
        | .matchData dataType resultType scrutinee branches =>
            if resultType.isWellFormed definitions then
              match definitions.lookupDataType? dataType with
              | none => { path, data := .unknownDataType dataType }
              | some definition =>
                  let scrutineePath := path.child .matchScrutinee
                  match infer? context scrutinee definitions with
                  | none =>
                      diagnoseWithFuel fuel definitions context
                        scrutineePath scrutinee
                  | some (.namedData actualDataType) =>
                      if actualDataType = dataType then
                        let expectedCount :=
                          definition.constructorPayloadTypes.length
                        if branches.length = expectedCount then
                          diagnoseBranchesWithFuel fuel definitions context path
                            resultType definition.constructorPayloadTypes branches 0
                        else
                          { path,
                            data := .matchBranchCountMismatch
                              expectedCount branches.length }
                      else
                        { path := scrutineePath,
                          data := .matchDataTypeMismatch dataType actualDataType }
                  | some actual =>
                      { path := scrutineePath, data := .expectedNamedData actual }
            else
              invalidTypeError definitions path resultType
        | .unary op operand =>
            let operandPath := path.child .unaryOperand
            match infer? context operand definitions with
            | none =>
                diagnoseWithFuel fuel definitions context operandPath operand
            | some actual =>
                { path := operandPath,
                  data := .primitiveOperandTypeMismatch op.operandType actual }
        | .binary op left right =>
            let leftPath := path.child .binaryLeft
            match infer? context left definitions with
            | none => diagnoseWithFuel fuel definitions context leftPath left
            | some leftType =>
                if leftType = op.leftType then
                  let rightPath := path.child .binaryRight
                  match infer? context right definitions with
                  | none =>
                      diagnoseWithFuel fuel definitions context rightPath right
                  | some rightType =>
                      { path := rightPath,
                        data := .primitiveOperandTypeMismatch
                          op.rightType rightType }
                else
                  { path := leftPath,
                    data := .primitiveOperandTypeMismatch op.leftType leftType }
        | .ternary op firstExpr secondExpr thirdExpr =>
            let firstPath := path.child .ternaryFirst
            match infer? context firstExpr definitions with
            | none =>
                diagnoseWithFuel fuel definitions context firstPath firstExpr
            | some firstType =>
                if firstType = op.firstType then
                  let secondPath := path.child .ternarySecond
                  match infer? context secondExpr definitions with
                  | none =>
                      diagnoseWithFuel fuel definitions context secondPath secondExpr
                  | some secondType =>
                      if secondType = op.secondType then
                        let thirdPath := path.child .ternaryThird
                        match infer? context thirdExpr definitions with
                        | none =>
                            diagnoseWithFuel fuel definitions context thirdPath thirdExpr
                        | some thirdType =>
                            { path := thirdPath,
                              data := .primitiveOperandTypeMismatch
                                op.thirdType thirdType }
                      else
                        { path := secondPath,
                          data := .primitiveOperandTypeMismatch
                            op.secondType secondType }
                else
                  { path := firstPath,
                    data := .primitiveOperandTypeMismatch op.firstType firstType }
        | .letE value body =>
            let valuePath := path.child .letValue
            match infer? context value definitions with
            | none => diagnoseWithFuel fuel definitions context valuePath value
            | some valueType =>
                diagnoseWithFuel fuel definitions (valueType :: context)
                  (path.child .letBody) body
        | .ifE condition thenBranch elseBranch =>
            let conditionPath := path.child .ifCondition
            match infer? context condition definitions with
            | none =>
                diagnoseWithFuel fuel definitions context conditionPath condition
            | some conditionType =>
                if conditionType = .bool then
                  let thenPath := path.child .ifThen
                  match infer? context thenBranch definitions with
                  | none =>
                      diagnoseWithFuel fuel definitions context thenPath thenBranch
                  | some thenType =>
                      let elsePath := path.child .ifElse
                      match infer? context elseBranch definitions with
                      | none =>
                          diagnoseWithFuel fuel definitions context elsePath elseBranch
                      | some elseType =>
                          { path := elsePath,
                            data := .branchTypeMismatch thenType elseType }
                else
                  { path := conditionPath, data := .expectedBool conditionType }

  private def diagnoseBranchesWithFuel :
      Nat → DataEnvironment → Context → CheckPath → Ty →
        List Ty → List Expr → Nat → CheckError
    | 0, _, _, path, _, _, _, _ => { path, data := .inferenceFailure }
    | fuel + 1, definitions, context, path, resultType,
        payloadTypes, branches, branchIndex =>
        match payloadTypes, branches with
        | payloadType :: remainingPayloadTypes, branch :: remainingBranches =>
            let branchPath := path.child (.matchBranch branchIndex)
            match infer? (payloadType :: context) branch definitions with
            | none =>
                diagnoseWithFuel fuel definitions (payloadType :: context)
                  branchPath branch
            | some actual =>
                if actual = resultType then
                  diagnoseBranchesWithFuel fuel definitions context path resultType
                    remainingPayloadTypes remainingBranches (branchIndex + 1)
                else
                  { path := branchPath,
                    data := .matchBranchResultTypeMismatch
                      branchIndex resultType actual }
        | _, _ => { path, data := .inferenceFailure }

end

mutual

  private def diagnosticFuelExpr : Expr → Nat
    | .unit
    | .bool _
    | .word _
    | .var _ => 1
    | .first operand
    | .second operand
    | .loadCell operand
    | .unary _ operand => diagnosticFuelExpr operand + 1
    | .pair left right
    | .apply left right
    | .storeCell left right
    | .letE left right =>
        diagnosticFuelExpr left + diagnosticFuelExpr right + 1
    | .lambda _ _ body
    | .inLeft _ body
    | .inRight _ body
    | .newCell _ body
    | .construct _ body => diagnosticFuelExpr body + 1
    | .caseE scrutinee leftBranch rightBranch
    | .ifE scrutinee leftBranch rightBranch =>
        diagnosticFuelExpr scrutinee +
          diagnosticFuelExpr leftBranch + diagnosticFuelExpr rightBranch + 1
    | .matchData _ _ scrutinee branches =>
        diagnosticFuelExpr scrutinee + diagnosticFuelList branches + 1
    | .binary _ left right =>
        diagnosticFuelExpr left + diagnosticFuelExpr right + 1
    | .ternary _ firstExpr secondExpr thirdExpr =>
        diagnosticFuelExpr firstExpr + diagnosticFuelExpr secondExpr +
          diagnosticFuelExpr thirdExpr + 1

  private def diagnosticFuelList : List Expr → Nat
    | [] => 1
    | expr :: expressions =>
        diagnosticFuelExpr expr + diagnosticFuelList expressions + 1

end

private def diagnose
    (definitions : DataEnvironment)
    (context : Context)
    (path : CheckPath)
    (expr : Expr) : CheckError :=
  diagnoseWithFuel (diagnosticFuelExpr expr + 1) definitions context path expr

def inferDetailedWithDefinitions
    (definitions : DataEnvironment)
    (context : Context)
    (path : CheckPath)
    (expr : Expr) : Except CheckError Ty :=
  match infer? context expr definitions with
  | some type => .ok type
  | none => .error (diagnose definitions context path expr)

/--
Detailed checking keeps the historical argument order. The immutable data
definition table is the optional final argument so pre-ADT call sites keep
their meaning.
-/
def inferDetailed
    (context : Context)
    (path : CheckPath := [])
    (expr : Expr)
    (definitions : DataEnvironment := []) : Except CheckError Ty :=
  inferDetailedWithDefinitions definitions context path expr

theorem inferDetailed_toOption
    (context : Context)
    (path : CheckPath)
    (expr : Expr)
    (definitions : DataEnvironment := []) :
    (inferDetailed context path expr definitions).toOption =
      infer? context expr definitions := by
  cases inferred : infer? context expr definitions <;>
    simp [inferDetailed, inferDetailedWithDefinitions, inferred, Except.toOption]

theorem inferDetailed_iff_infer
    {context : Context}
    {path : CheckPath}
    {expr : Expr}
    {type : Ty}
    {definitions : DataEnvironment} :
    inferDetailed context path expr definitions = .ok type ↔
      infer? context expr definitions = some type := by
  rw [← inferDetailed_toOption context path expr definitions]
  cases inferDetailed context path expr definitions <;> simp [Except.toOption]

theorem inferDetailed_iff_typing
    {context : Context}
    {path : CheckPath}
    {expr : Expr}
    {type : Ty}
    {definitions : DataEnvironment} :
    inferDetailed context path expr definitions = .ok type ↔
      HasType context expr type definitions := by
  rw [inferDetailed_iff_infer, typing_iff_infer]

set_option doc.verso true in
/-- Check {lean}`program` under the initial typing context {lean}`context`,
returning its declared result type on success or a {lean}`CheckError` on failure.

Checks the data-definition table, the declared result type, and the body's
inferred type, in that order. Success corresponds to {lean}`Program.WellTypedIn`.
This function checks typing; it does not evaluate the program.
-/
def Program.checkDetailedIn
    (program : Program)
    (context : Context) : Except CheckError Ty :=
  if program.dataDefinitions.isWellFormed then
    if program.resultType.isWellFormed program.dataDefinitions then
      match inferDetailed context [] program.body program.dataDefinitions with
      | .error error => .error error
      | .ok inferredType =>
          if inferredType = program.resultType then
            .ok program.resultType
          else
            .error {
              path := []
              data := .declaredResultTypeMismatch
                program.resultType inferredType
            }
    else
      .error (invalidTypeError
        program.dataDefinitions [] program.resultType)
  else
    .error (definitionTableError program.dataDefinitions)

theorem Program.checkDetailedIn_iff_checkIn
    {program : Program}
    {context : Context} :
    program.checkDetailedIn context = .ok program.resultType ↔
      program.checkIn context = true := by
  by_cases definitionsAccepted :
      program.dataDefinitions.isWellFormed = true
  · by_cases resultAccepted :
        program.resultType.isWellFormed program.dataDefinitions = true
    · cases detailed :
        inferDetailed context [] program.body program.dataDefinitions with
      | error error =>
          have notInferred :
              infer? context program.body program.dataDefinitions = none := by
            simpa [detailed, Except.toOption] using
              (inferDetailed_toOption
                context [] program.body program.dataDefinitions).symm
          simp [
            Program.checkDetailedIn,
            Program.checkIn,
            definitionsAccepted,
            resultAccepted,
            detailed,
            notInferred
          ]
      | ok inferredType =>
          have inferred :
              infer? context program.body program.dataDefinitions =
                some inferredType := by
            simpa [detailed, Except.toOption] using
              (inferDetailed_toOption
                context [] program.body program.dataDefinitions).symm
          by_cases equalTypes : inferredType = program.resultType
          · subst inferredType
            simp [
              Program.checkDetailedIn,
              Program.checkIn,
              definitionsAccepted,
              resultAccepted,
              detailed,
              inferred
            ]
          · simp [
              Program.checkDetailedIn,
              Program.checkIn,
              definitionsAccepted,
              resultAccepted,
              detailed,
              inferred,
              equalTypes
            ]
    · simp [
        Program.checkDetailedIn,
        Program.checkIn,
        definitionsAccepted,
        resultAccepted
      ]
  · simp [Program.checkDetailedIn, Program.checkIn, definitionsAccepted]

set_option doc.verso true in
/-- The diagnostic checker {lean}`Program.checkDetailedIn` succeeds with
{lean}`program.resultType` exactly when {lean}`program.WellTypedIn context` holds.

The forward implication turns a successful checker result into declarative
typing evidence. The reverse implication ensures that every program satisfying
the specification is accepted in the same context.
-/
theorem Program.checkDetailedIn_iff_wellTyped
    {program : Program}
    {context : Context} :
    program.checkDetailedIn context = .ok program.resultType ↔
      program.WellTypedIn context := by
  rw [Program.checkDetailedIn_iff_checkIn, Program.checkIn_iff_wellTyped]

theorem Program.checkDetailedIn_iff_typing
    {program : Program}
    {context : Context} :
    program.checkDetailedIn context = .ok program.resultType ↔
      program.WellTypedIn context :=
  Program.checkDetailedIn_iff_wellTyped

theorem Program.checkDetailedIn_full_sound
    {program : Program}
    {context : Context}
    (checked : program.checkDetailedIn context = .ok program.resultType) :
    program.WellTypedIn context :=
  Program.checkDetailedIn_iff_wellTyped.mp checked

theorem Program.checkDetailedIn_sound
    {program : Program}
    {context : Context}
    (checked : program.checkDetailedIn context = .ok program.resultType) :
    HasType context program.body program.resultType program.dataDefinitions :=
  (Program.checkDetailedIn_full_sound checked).bodyHasType

theorem Program.checkDetailedIn_complete
    {program : Program}
    {context : Context}
    (wellTyped : program.WellTypedIn context) :
    program.checkDetailedIn context = .ok program.resultType :=
  Program.checkDetailedIn_iff_wellTyped.mpr wellTyped

/-- The historical detailed checker is the empty-context specialization. -/
def Program.checkDetailed (program : Program) : Except CheckError Ty :=
  program.checkDetailedIn []

@[simp] theorem Program.checkDetailedIn_nil (program : Program) :
    program.checkDetailedIn [] = program.checkDetailed :=
  rfl

theorem Program.checkDetailed_iff_check {program : Program} :
    program.checkDetailed = .ok program.resultType ↔
      program.check = true :=
  Program.checkDetailedIn_iff_checkIn

theorem Program.checkDetailed_iff_wellTyped {program : Program} :
    program.checkDetailed = .ok program.resultType ↔ program.WellTyped := by
  rw [Program.checkDetailed_iff_check, Program.check_iff_wellTyped]

/-- Historical theorem name. Full program checking now includes table and
result-type validity, so its right-hand side is `Program.WellTyped`. -/
theorem Program.checkDetailed_iff_typing {program : Program} :
    program.checkDetailed = .ok program.resultType ↔ program.WellTyped :=
  Program.checkDetailed_iff_wellTyped

theorem Program.checkDetailed_full_sound
    {program : Program}
    (checked : program.checkDetailed = .ok program.resultType) :
    program.WellTyped :=
  Program.checkDetailed_iff_wellTyped.mp checked

theorem Program.checkDetailed_sound
    {program : Program}
    (checked : program.checkDetailed = .ok program.resultType) :
    HasType [] program.body program.resultType program.dataDefinitions :=
  (Program.checkDetailed_full_sound checked).bodyHasType

theorem Program.checkDetailed_complete
    {program : Program}
    (wellTyped : program.WellTyped) :
    program.checkDetailed = .ok program.resultType :=
  Program.checkDetailed_iff_wellTyped.mpr wellTyped

end Solcore.Core
