import Solcore.Core.Data
import Solcore.Core.Primitive

set_option autoImplicit false

namespace Solcore.Core

mutual

  inductive HasType :
      Context → Expr → Ty → (definitions : DataEnvironment := []) → Prop where
    | unit {context : Context} {definitions : DataEnvironment} :
        HasType context .unit .unit definitions
    | bool {context : Context} {definitions : DataEnvironment} {value : Bool} :
        HasType context (.bool value) .bool definitions
    | word {context : Context} {definitions : DataEnvironment} {value : Word} :
        HasType context (.word value) .word definitions
    | var
        {context : Context} {definitions : DataEnvironment}
        {index : Nat} {type : Ty} :
        context[index]? = some type →
        HasType context (.var index) type definitions
    | pair
        {context : Context} {definitions : DataEnvironment}
        {left right : Expr} {leftType rightType : Ty} :
        HasType context left leftType definitions →
        HasType context right rightType definitions →
        HasType context (.pair left right) (.product leftType rightType) definitions
    | first
        {context : Context} {definitions : DataEnvironment}
        {operand : Expr} {leftType rightType : Ty} :
        HasType context operand (.product leftType rightType) definitions →
        HasType context (.first operand) leftType definitions
    | second
        {context : Context} {definitions : DataEnvironment}
        {operand : Expr} {leftType rightType : Ty} :
        HasType context operand (.product leftType rightType) definitions →
        HasType context (.second operand) rightType definitions
    | lambda
        {context : Context} {definitions : DataEnvironment}
        {parameterType resultType : Ty} {body : Expr} :
        Ty.WellFormed definitions parameterType →
        Ty.WellFormed definitions resultType →
        HasType (parameterType :: context) body resultType definitions →
        HasType context
          (.lambda parameterType resultType body)
          (.function parameterType resultType)
          definitions
    | apply
        {context : Context} {definitions : DataEnvironment}
        {function argument : Expr} {parameterType resultType : Ty} :
        HasType context function (.function parameterType resultType) definitions →
        HasType context argument parameterType definitions →
        HasType context (.apply function argument) resultType definitions
    | inLeft
        {context : Context} {definitions : DataEnvironment}
        {rightType leftType : Ty} {payload : Expr} :
        Ty.WellFormed definitions rightType →
        HasType context payload leftType definitions →
        HasType context (.inLeft rightType payload) (.sum leftType rightType) definitions
    | inRight
        {context : Context} {definitions : DataEnvironment}
        {leftType rightType : Ty} {payload : Expr} :
        Ty.WellFormed definitions leftType →
        HasType context payload rightType definitions →
        HasType context (.inRight leftType payload) (.sum leftType rightType) definitions
    | caseE
        {context : Context} {definitions : DataEnvironment}
        {scrutinee leftBranch rightBranch : Expr}
        {leftType rightType resultType : Ty} :
        HasType context scrutinee (.sum leftType rightType) definitions →
        HasType (leftType :: context) leftBranch resultType definitions →
        HasType (rightType :: context) rightBranch resultType definitions →
        HasType context (.caseE scrutinee leftBranch rightBranch) resultType definitions
    | newCell
        {context : Context} {definitions : DataEnvironment}
        {elementType : Ty} {initializer : Expr} :
        HasType context initializer elementType definitions →
        CellPayload elementType →
        HasType context (.newCell elementType initializer) (.cell elementType) definitions
    | loadCell
        {context : Context} {definitions : DataEnvironment}
        {elementType : Ty} {reference : Expr} :
        HasType context reference (.cell elementType) definitions →
        CellPayload elementType →
        HasType context (.loadCell reference) elementType definitions
    | storeCell
        {context : Context} {definitions : DataEnvironment}
        {elementType : Ty} {reference value : Expr} :
        HasType context reference (.cell elementType) definitions →
        HasType context value elementType definitions →
        CellPayload elementType →
        HasType context (.storeCell reference value) .unit definitions
    | construct
        {context : Context} {definitions : DataEnvironment}
        {constructor : ConstructorId} {payload : Expr} {payloadType : Ty} :
        definitions.lookupConstructorPayloadType? constructor = some payloadType →
        HasType context payload payloadType definitions →
        HasType context
          (.construct constructor payload)
          (.namedData constructor.owner)
          definitions
    | matchData
        {context : Context} {definitions : DataEnvironment}
        {dataType : DataTypeId} {definition : DataDefinition}
        {resultType : Ty} {scrutinee : Expr} {branches : List Expr} :
        definitions.lookupDataType? dataType = some definition →
        Ty.WellFormed definitions resultType →
        HasType context scrutinee (.namedData dataType) definitions →
        BranchesHaveType
          context resultType definition.constructorPayloadTypes branches definitions →
        HasType context
          (.matchData dataType resultType scrutinee branches)
          resultType
          definitions
    | unary
        {context : Context} {definitions : DataEnvironment}
        {op : UnaryOp} {operand : Expr} :
        HasType context operand op.operandType definitions →
        HasType context (.unary op operand) op.resultType definitions
    | binary
        {context : Context} {definitions : DataEnvironment}
        {op : BinaryOp} {left right : Expr} :
        HasType context left op.leftType definitions →
        HasType context right op.rightType definitions →
        HasType context (.binary op left right) op.resultType definitions
    | letE
        {context : Context} {definitions : DataEnvironment}
        {value body : Expr} {valueType bodyType : Ty} :
        HasType context value valueType definitions →
        HasType (valueType :: context) body bodyType definitions →
        HasType context (.letE value body) bodyType definitions
    | ifE
        {context : Context} {definitions : DataEnvironment}
        {condition thenBranch elseBranch : Expr} {resultType : Ty} :
        HasType context condition .bool definitions →
        HasType context thenBranch resultType definitions →
        HasType context elseBranch resultType definitions →
        HasType context (.ifE condition thenBranch elseBranch) resultType definitions

  inductive BranchesHaveType :
      Context → Ty → List Ty → List Expr →
        (definitions : DataEnvironment := []) → Prop where
    | nil {context : Context} {resultType : Ty} {definitions : DataEnvironment} :
        BranchesHaveType context resultType [] [] definitions
    | cons
        {context : Context} {resultType : Ty} {definitions : DataEnvironment}
        {payloadType : Ty} {payloadTypes : List Ty}
        {branch : Expr} {branches : List Expr} :
        HasType (payloadType :: context) branch resultType definitions →
        BranchesHaveType context resultType payloadTypes branches definitions →
        BranchesHaveType
          context resultType (payloadType :: payloadTypes) (branch :: branches) definitions

end

mutual

  private def inferWithDefinitions?
      (definitions : DataEnvironment)
      (context : Context) : Expr → Option Ty
    | .unit => some .unit
    | .bool _ => some .bool
    | .word _ => some .word
    | .var index => context[index]?
    | .pair left right =>
        match
            inferWithDefinitions? definitions context left,
            inferWithDefinitions? definitions context right with
        | some leftType, some rightType => some (.product leftType rightType)
        | _, _ => none
    | .first operand =>
        match inferWithDefinitions? definitions context operand with
        | some (.product leftType _) => some leftType
        | _ => none
    | .second operand =>
        match inferWithDefinitions? definitions context operand with
        | some (.product _ rightType) => some rightType
        | _ => none
    | .lambda parameterType resultType body =>
        if parameterType.isWellFormed definitions then
          if resultType.isWellFormed definitions then
            if inferWithDefinitions? definitions (parameterType :: context) body =
                some resultType then
              some (.function parameterType resultType)
            else
              none
          else
            none
        else
          none
    | .apply function argument =>
        match inferWithDefinitions? definitions context function with
        | some (.function parameterType resultType) =>
            if inferWithDefinitions? definitions context argument = some parameterType then
              some resultType
            else
              none
        | _ => none
    | .inLeft rightType payload =>
        if rightType.isWellFormed definitions then
          match inferWithDefinitions? definitions context payload with
          | some leftType => some (.sum leftType rightType)
          | none => none
        else
          none
    | .inRight leftType payload =>
        if leftType.isWellFormed definitions then
          match inferWithDefinitions? definitions context payload with
          | some rightType => some (.sum leftType rightType)
          | none => none
        else
          none
    | .caseE scrutinee leftBranch rightBranch =>
        match inferWithDefinitions? definitions context scrutinee with
        | some (.sum leftType rightType) =>
            match
                inferWithDefinitions? definitions (leftType :: context) leftBranch,
                inferWithDefinitions? definitions (rightType :: context) rightBranch with
            | some leftResultType, some rightResultType =>
                if leftResultType = rightResultType then some leftResultType else none
            | _, _ => none
        | _ => none
    | .newCell elementType initializer =>
        if inferWithDefinitions? definitions context initializer = some elementType then
          if elementType.isCellPayload then some (.cell elementType) else none
        else
          none
    | .loadCell reference =>
        match inferWithDefinitions? definitions context reference with
        | some (.cell elementType) =>
            if elementType.isCellPayload then some elementType else none
        | _ => none
    | .storeCell reference value =>
        match inferWithDefinitions? definitions context reference with
        | some (.cell elementType) =>
            if elementType.isCellPayload then
              if inferWithDefinitions? definitions context value = some elementType then
                some .unit
              else
                none
            else
              none
        | _ => none
    | .construct constructor payload =>
        match definitions.lookupConstructorPayloadType? constructor with
        | some payloadType =>
            if inferWithDefinitions? definitions context payload = some payloadType then
              some (.namedData constructor.owner)
            else
              none
        | none => none
    | .matchData dataType resultType scrutinee branches =>
        if resultType.isWellFormed definitions then
          match definitions.lookupDataType? dataType with
          | some definition =>
              if inferWithDefinitions? definitions context scrutinee =
                  some (.namedData dataType) then
                if branchesHaveType?
                    definitions context resultType
                    definition.constructorPayloadTypes branches then
                  some resultType
                else
                  none
              else
                none
          | none => none
        else
          none
    | .unary op operand =>
        if inferWithDefinitions? definitions context operand = some op.operandType then
          some op.resultType
        else
          none
    | .binary op left right =>
        if inferWithDefinitions? definitions context left = some op.leftType then
          if inferWithDefinitions? definitions context right = some op.rightType then
            some op.resultType
          else
            none
        else
          none
    | .letE value body =>
        match inferWithDefinitions? definitions context value with
        | some valueType =>
            inferWithDefinitions? definitions (valueType :: context) body
        | none => none
    | .ifE condition thenBranch elseBranch =>
        match
            inferWithDefinitions? definitions context condition,
            inferWithDefinitions? definitions context thenBranch,
            inferWithDefinitions? definitions context elseBranch with
        | some .bool, some thenType, some elseType =>
            if thenType = elseType then some thenType else none
        | _, _, _ => none

  private def branchesHaveType?
      (definitions : DataEnvironment)
      (context : Context)
      (resultType : Ty) : List Ty → List Expr → Bool
    | [], [] => true
    | payloadType :: payloadTypes, branch :: branches =>
        if inferWithDefinitions? definitions (payloadType :: context) branch =
            some resultType then
          branchesHaveType? definitions context resultType payloadTypes branches
        else
          false
    | _, _ => false

end


def infer?
    (context : Context)
    (expr : Expr)
    (definitions : DataEnvironment := []) : Option Ty :=
  inferWithDefinitions? definitions context expr


theorem infer_complete
    {context : Context} {expr : Expr} {type : Ty}
    {definitions : DataEnvironment}
    (typing : HasType context expr type definitions) :
    infer? context expr definitions = some type := by
  change inferWithDefinitions? definitions context expr = some type
  induction typing using HasType.rec
      (motive_2 := fun context resultType payloadTypes branches definitions _ =>
        branchesHaveType? definitions context resultType payloadTypes branches = true) with
  | unit | bool | word | var => simp_all [inferWithDefinitions?]
  | pair _ _ leftIH rightIH =>
      simp [inferWithDefinitions?, leftIH, rightIH]
  | first _ operandIH => simp [inferWithDefinitions?, operandIH]
  | second _ operandIH => simp [inferWithDefinitions?, operandIH]
  | lambda parameterWellFormed resultWellFormed _ bodyIH =>
      simp [
        inferWithDefinitions?,
        Ty.isWellFormed_complete parameterWellFormed,
        Ty.isWellFormed_complete resultWellFormed,
        bodyIH
      ]
  | apply _ _ functionIH argumentIH =>
      simp [inferWithDefinitions?, functionIH, argumentIH]
  | inLeft annotationWellFormed _ payloadIH =>
      simp [
        inferWithDefinitions?,
        Ty.isWellFormed_complete annotationWellFormed,
        payloadIH
      ]
  | inRight annotationWellFormed _ payloadIH =>
      simp [
        inferWithDefinitions?,
        Ty.isWellFormed_complete annotationWellFormed,
        payloadIH
      ]
  | caseE _ _ _ scrutineeIH leftIH rightIH =>
      simp [inferWithDefinitions?, scrutineeIH, leftIH, rightIH]
  | newCell _ payload initializerIH =>
      simp [
        inferWithDefinitions?,
        initializerIH,
        Ty.isCellPayload_complete payload
      ]
  | loadCell _ payload referenceIH =>
      simp [
        inferWithDefinitions?,
        referenceIH,
        Ty.isCellPayload_complete payload
      ]
  | storeCell _ _ payload referenceIH valueIH =>
      simp [
        inferWithDefinitions?,
        referenceIH,
        valueIH,
        Ty.isCellPayload_complete payload
      ]
  | construct lookup _ payloadIH =>
      simp [inferWithDefinitions?, lookup, payloadIH]
  | matchData lookup resultWellFormed _ _ scrutineeIH branchesIH =>
      simp [
        inferWithDefinitions?,
        lookup,
        Ty.isWellFormed_complete resultWellFormed,
        scrutineeIH,
        branchesIH
      ]
  | unary _ operandIH => simp [inferWithDefinitions?, operandIH]
  | binary _ _ leftIH rightIH =>
      simp [inferWithDefinitions?, leftIH, rightIH]
  | letE _ _ valueIH bodyIH =>
      simp [inferWithDefinitions?, valueIH, bodyIH]
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp [inferWithDefinitions?, conditionIH, thenIH, elseIH]
  | nil => rfl
  | cons _ _ branchIH branchesIH =>
      simp [branchesHaveType?, branchIH, branchesIH]


theorem infer_sound
    {context : Context} {expr : Expr} {type : Ty}
    {definitions : DataEnvironment}
    (inferred : infer? context expr definitions = some type) :
    HasType context expr type definitions := by
  change inferWithDefinitions? definitions context expr = some type at inferred
  induction expr using Expr.rec
      (motive_2 := fun branches =>
        ∀ (context : Context) (resultType : Ty) (payloadTypes : List Ty)
          (definitions : DataEnvironment),
          branchesHaveType? definitions context resultType payloadTypes branches = true →
          BranchesHaveType context resultType payloadTypes branches definitions)
      generalizing context type definitions with
  | unit =>
      simp [inferWithDefinitions?] at inferred
      cases inferred
      exact .unit
  | bool =>
      simp [inferWithDefinitions?] at inferred
      cases inferred
      exact .bool
  | word =>
      simp [inferWithDefinitions?] at inferred
      cases inferred
      exact .word
  | var index => exact .var inferred
  | pair left right leftIH rightIH =>
      cases leftInferred : inferWithDefinitions? definitions context left with
      | none => simp [inferWithDefinitions?, leftInferred] at inferred
      | some leftType =>
          cases rightInferred : inferWithDefinitions? definitions context right with
          | none =>
              simp [inferWithDefinitions?, leftInferred, rightInferred] at inferred
          | some rightType =>
              have resultEquality : Ty.product leftType rightType = type := by
                exact Option.some.inj (by
                  simpa [inferWithDefinitions?, leftInferred, rightInferred] using inferred)
              subst type
              exact .pair (leftIH leftInferred) (rightIH rightInferred)
  | first operand operandIH =>
      cases operandInferred : inferWithDefinitions? definitions context operand with
      | none => simp [inferWithDefinitions?, operandInferred] at inferred
      | some operandType =>
          cases operandType with
          | product leftType rightType =>
              have resultEquality : leftType = type := by
                exact Option.some.inj (by
                  simpa [inferWithDefinitions?, operandInferred] using inferred)
              subst type
              exact .first (operandIH operandInferred)
          | unit | bool | word | function | sum | cell | namedData =>
              simp [inferWithDefinitions?, operandInferred] at inferred
  | second operand operandIH =>
      cases operandInferred : inferWithDefinitions? definitions context operand with
      | none => simp [inferWithDefinitions?, operandInferred] at inferred
      | some operandType =>
          cases operandType with
          | product leftType rightType =>
              have resultEquality : rightType = type := by
                exact Option.some.inj (by
                  simpa [inferWithDefinitions?, operandInferred] using inferred)
              subst type
              exact .second (operandIH operandInferred)
          | unit | bool | word | function | sum | cell | namedData =>
              simp [inferWithDefinitions?, operandInferred] at inferred
  | lambda parameterType resultType body bodyIH =>
      by_cases parameterAccepted : parameterType.isWellFormed definitions = true
      · by_cases resultAccepted : resultType.isWellFormed definitions = true
        · by_cases bodyInferred :
            inferWithDefinitions? definitions (parameterType :: context) body =
              some resultType
          · have resultEquality : Ty.function parameterType resultType = type := by
              exact Option.some.inj (by
                simpa [
                  inferWithDefinitions?,
                  parameterAccepted,
                  resultAccepted,
                  bodyInferred
                ] using inferred)
            subst type
            exact .lambda
              (Ty.isWellFormed_sound parameterAccepted)
              (Ty.isWellFormed_sound resultAccepted)
              (bodyIH bodyInferred)
          · simp [
              inferWithDefinitions?,
              parameterAccepted,
              resultAccepted,
              bodyInferred
            ] at inferred
        · simp [inferWithDefinitions?, parameterAccepted, resultAccepted] at inferred
      · simp [inferWithDefinitions?, parameterAccepted] at inferred
  | apply function argument functionIH argumentIH =>
      cases functionInferred : inferWithDefinitions? definitions context function with
      | none => simp [inferWithDefinitions?, functionInferred] at inferred
      | some functionType =>
          cases functionType with
          | function parameterType resultType =>
              by_cases argumentInferred :
                  inferWithDefinitions? definitions context argument = some parameterType
              · have resultEquality : resultType = type := by
                  exact Option.some.inj (by
                    simpa [inferWithDefinitions?, functionInferred, argumentInferred]
                      using inferred)
                subst type
                exact .apply
                  (functionIH functionInferred)
                  (argumentIH argumentInferred)
              · simp [inferWithDefinitions?, functionInferred, argumentInferred] at inferred
          | unit | bool | word | product | sum | cell | namedData =>
              simp [inferWithDefinitions?, functionInferred] at inferred
  | inLeft rightType payload payloadIH =>
      by_cases annotationAccepted : rightType.isWellFormed definitions = true
      · cases payloadInferred : inferWithDefinitions? definitions context payload with
        | none =>
            simp [inferWithDefinitions?, annotationAccepted, payloadInferred] at inferred
        | some leftType =>
            have resultEquality : Ty.sum leftType rightType = type := by
              exact Option.some.inj (by
                simpa [inferWithDefinitions?, annotationAccepted, payloadInferred]
                  using inferred)
            subst type
            exact .inLeft
              (Ty.isWellFormed_sound annotationAccepted)
              (payloadIH payloadInferred)
      · simp [inferWithDefinitions?, annotationAccepted] at inferred
  | inRight leftType payload payloadIH =>
      by_cases annotationAccepted : leftType.isWellFormed definitions = true
      · cases payloadInferred : inferWithDefinitions? definitions context payload with
        | none =>
            simp [inferWithDefinitions?, annotationAccepted, payloadInferred] at inferred
        | some rightType =>
            have resultEquality : Ty.sum leftType rightType = type := by
              exact Option.some.inj (by
                simpa [inferWithDefinitions?, annotationAccepted, payloadInferred]
                  using inferred)
            subst type
            exact .inRight
              (Ty.isWellFormed_sound annotationAccepted)
              (payloadIH payloadInferred)
      · simp [inferWithDefinitions?, annotationAccepted] at inferred
  | caseE scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      cases scrutineeInferred : inferWithDefinitions? definitions context scrutinee with
      | none => simp [inferWithDefinitions?, scrutineeInferred] at inferred
      | some scrutineeType =>
          cases scrutineeType with
          | sum leftType rightType =>
              cases leftInferred :
                  inferWithDefinitions? definitions (leftType :: context) leftBranch with
              | none =>
                  simp [inferWithDefinitions?, scrutineeInferred, leftInferred] at inferred
              | some leftResultType =>
                  cases rightInferred :
                      inferWithDefinitions? definitions (rightType :: context) rightBranch with
                  | none =>
                      simp [
                        inferWithDefinitions?,
                        scrutineeInferred,
                        leftInferred,
                        rightInferred
                      ] at inferred
                  | some rightResultType =>
                      by_cases equalTypes : leftResultType = rightResultType
                      · subst rightResultType
                        have resultEquality : leftResultType = type := by
                          exact Option.some.inj (by
                            simpa [
                              inferWithDefinitions?,
                              scrutineeInferred,
                              leftInferred,
                              rightInferred
                            ] using inferred)
                        subst type
                        exact .caseE
                          (scrutineeIH scrutineeInferred)
                          (leftIH leftInferred)
                          (rightIH rightInferred)
                      · simp [
                          inferWithDefinitions?,
                          scrutineeInferred,
                          leftInferred,
                          rightInferred,
                          equalTypes
                        ] at inferred
          | unit | bool | word | product | function | cell | namedData =>
              simp [inferWithDefinitions?, scrutineeInferred] at inferred
  | newCell elementType initializer initializerIH =>
      by_cases initializerInferred :
          inferWithDefinitions? definitions context initializer = some elementType
      · by_cases payloadAccepted : elementType.isCellPayload = true
        · have resultEquality : Ty.cell elementType = type := by
            exact Option.some.inj (by
              simpa [inferWithDefinitions?, initializerInferred, payloadAccepted]
                using inferred)
          subst type
          exact .newCell
            (initializerIH initializerInferred)
            (Ty.isCellPayload_sound payloadAccepted)
        · simp [inferWithDefinitions?, initializerInferred, payloadAccepted] at inferred
      · simp [inferWithDefinitions?, initializerInferred] at inferred
  | loadCell reference referenceIH =>
      cases referenceInferred : inferWithDefinitions? definitions context reference with
      | none => simp [inferWithDefinitions?, referenceInferred] at inferred
      | some referenceType =>
          cases referenceType with
          | cell elementType =>
              by_cases payloadAccepted : elementType.isCellPayload = true
              · have resultEquality : elementType = type := by
                  exact Option.some.inj (by
                    simpa [inferWithDefinitions?, referenceInferred, payloadAccepted]
                      using inferred)
                subst type
                exact .loadCell
                  (referenceIH referenceInferred)
                  (Ty.isCellPayload_sound payloadAccepted)
              · simp [inferWithDefinitions?, referenceInferred, payloadAccepted] at inferred
          | unit | bool | word | product | function | sum | namedData =>
              simp [inferWithDefinitions?, referenceInferred] at inferred
  | storeCell reference value referenceIH valueIH =>
      cases referenceInferred : inferWithDefinitions? definitions context reference with
      | none => simp [inferWithDefinitions?, referenceInferred] at inferred
      | some referenceType =>
          cases referenceType with
          | cell elementType =>
              by_cases payloadAccepted : elementType.isCellPayload = true
              · by_cases valueInferred :
                    inferWithDefinitions? definitions context value = some elementType
                · have resultEquality : Ty.unit = type := by
                    exact Option.some.inj (by
                      simpa [
                        inferWithDefinitions?,
                        referenceInferred,
                        payloadAccepted,
                        valueInferred
                      ] using inferred)
                  subst type
                  exact .storeCell
                    (referenceIH referenceInferred)
                    (valueIH valueInferred)
                    (Ty.isCellPayload_sound payloadAccepted)
                · simp [
                    inferWithDefinitions?,
                    referenceInferred,
                    payloadAccepted,
                    valueInferred
                  ] at inferred
              · simp [inferWithDefinitions?, referenceInferred, payloadAccepted] at inferred
          | unit | bool | word | product | function | sum | namedData =>
              simp [inferWithDefinitions?, referenceInferred] at inferred
  | construct constructor payload payloadIH =>
      cases payloadLookup : definitions.lookupConstructorPayloadType? constructor with
      | none => simp [inferWithDefinitions?, payloadLookup] at inferred
      | some payloadType =>
          by_cases payloadInferred :
              inferWithDefinitions? definitions context payload = some payloadType
          · have resultEquality : Ty.namedData constructor.owner = type := by
              exact Option.some.inj (by
                simpa [inferWithDefinitions?, payloadLookup, payloadInferred] using inferred)
            subst type
            exact .construct payloadLookup (payloadIH payloadInferred)
          · simp [inferWithDefinitions?, payloadLookup, payloadInferred] at inferred
  | matchData dataType resultType scrutinee branches scrutineeIH branchesIH =>
      by_cases resultAccepted : resultType.isWellFormed definitions = true
      · cases definitionLookup : definitions.lookupDataType? dataType with
        | none =>
            simp [inferWithDefinitions?, resultAccepted, definitionLookup] at inferred
        | some definition =>
            by_cases scrutineeInferred :
                inferWithDefinitions? definitions context scrutinee =
                  some (.namedData dataType)
            · by_cases branchesAccepted :
                  branchesHaveType?
                    definitions context resultType
                    definition.constructorPayloadTypes branches = true
              · have resultEquality : resultType = type := by
                  exact Option.some.inj (by
                    simpa [
                      inferWithDefinitions?,
                      resultAccepted,
                      definitionLookup,
                      scrutineeInferred,
                      branchesAccepted
                    ] using inferred)
                subst type
                exact .matchData
                  definitionLookup
                  (Ty.isWellFormed_sound resultAccepted)
                  (scrutineeIH scrutineeInferred)
                  (branchesIH
                    context resultType definition.constructorPayloadTypes definitions
                    branchesAccepted)
              · simp [
                  inferWithDefinitions?,
                  resultAccepted,
                  definitionLookup,
                  scrutineeInferred,
                  branchesAccepted
                ] at inferred
            · simp [
                inferWithDefinitions?,
                resultAccepted,
                definitionLookup,
                scrutineeInferred
              ] at inferred
      · simp [inferWithDefinitions?, resultAccepted] at inferred
  | unary op operand operandIH =>
      by_cases operandInferred :
          inferWithDefinitions? definitions context operand = some op.operandType
      · have resultEquality : op.resultType = type := by
          exact Option.some.inj (by
            simpa [inferWithDefinitions?, operandInferred] using inferred)
        subst type
        exact .unary (operandIH operandInferred)
      · simp [inferWithDefinitions?, operandInferred] at inferred
  | binary op left right leftIH rightIH =>
      by_cases leftInferred :
          inferWithDefinitions? definitions context left = some op.leftType
      · by_cases rightInferred :
            inferWithDefinitions? definitions context right = some op.rightType
        · have resultEquality : op.resultType = type := by
            exact Option.some.inj (by
              simpa [inferWithDefinitions?, leftInferred, rightInferred] using inferred)
          subst type
          exact .binary (leftIH leftInferred) (rightIH rightInferred)
        · simp [inferWithDefinitions?, leftInferred, rightInferred] at inferred
      · simp [inferWithDefinitions?, leftInferred] at inferred
  | letE value body valueIH bodyIH =>
      cases valueInferred : inferWithDefinitions? definitions context value with
      | none => simp [inferWithDefinitions?, valueInferred] at inferred
      | some valueType =>
          exact .letE
            (valueIH valueInferred)
            (bodyIH (by simpa [inferWithDefinitions?, valueInferred] using inferred))
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases conditionInferred : inferWithDefinitions? definitions context condition with
      | none => simp [inferWithDefinitions?, conditionInferred] at inferred
      | some conditionType =>
          cases conditionType with
          | bool =>
              cases thenInferred :
                  inferWithDefinitions? definitions context thenBranch with
              | none =>
                  simp [inferWithDefinitions?, conditionInferred, thenInferred] at inferred
              | some thenType =>
                  cases elseInferred :
                      inferWithDefinitions? definitions context elseBranch with
                  | none =>
                      simp [
                        inferWithDefinitions?,
                        conditionInferred,
                        thenInferred,
                        elseInferred
                      ] at inferred
                  | some elseType =>
                      by_cases equalTypes : thenType = elseType
                      · subst elseType
                        have resultEquality : thenType = type := by
                          exact Option.some.inj (by
                            simpa [
                              inferWithDefinitions?,
                              conditionInferred,
                              thenInferred,
                              elseInferred
                            ] using inferred)
                        subst type
                        exact .ifE
                          (conditionIH conditionInferred)
                          (thenIH thenInferred)
                          (elseIH elseInferred)
                      · simp [
                          inferWithDefinitions?,
                          conditionInferred,
                          thenInferred,
                          elseInferred,
                          equalTypes
                        ] at inferred
          | unit | word | product | function | sum | cell | namedData =>
              simp [inferWithDefinitions?, conditionInferred] at inferred
  | nil =>
      rename_i context resultType payloadTypes definitions accepted
      cases payloadTypes with
      | nil => exact .nil
      | cons payloadType payloadTypes =>
          simp [branchesHaveType?] at accepted
  | cons branch branches branchIH branchesIH =>
      rename_i context resultType payloadTypes definitions accepted
      cases payloadTypes with
      | nil => simp [branchesHaveType?] at accepted
      | cons payloadType payloadTypes =>
          by_cases branchInferred :
              inferWithDefinitions? definitions (payloadType :: context) branch =
                some resultType
          · exact .cons
              (branchIH branchInferred)
              (branchesIH context resultType payloadTypes definitions (by
                simpa [branchesHaveType?, branchInferred] using accepted))
          · simp [branchesHaveType?, branchInferred] at accepted


theorem typing_iff_infer
    {context : Context} {expr : Expr} {type : Ty}
    {definitions : DataEnvironment} :
    HasType context expr type definitions ↔
      infer? context expr definitions = some type :=
  ⟨infer_complete, infer_sound⟩


theorem typing_deterministic
    {context : Context} {expr : Expr} {leftType rightType : Ty}
    {definitions : DataEnvironment}
    (left : HasType context expr leftType definitions)
    (right : HasType context expr rightType definitions) :
    leftType = rightType := by
  rw [typing_iff_infer] at left right
  rw [left] at right
  exact Option.some.inj right


namespace Program

structure WellTyped (program : Program) : Prop where
  dataDefinitionsWellFormed : program.dataDefinitions.WellFormed
  resultTypeWellFormed : Ty.WellFormed program.dataDefinitions program.resultType
  bodyHasType :
    HasType [] program.body program.resultType program.dataDefinitions


def check (program : Program) : Bool :=
  if program.dataDefinitions.isWellFormed then
    if program.resultType.isWellFormed program.dataDefinitions then
      match infer? [] program.body program.dataDefinitions with
      | some inferredType => decide (inferredType = program.resultType)
      | none => false
    else
      false
  else
    false


theorem check_full_sound
    {program : Program}
    (checked : program.check = true) :
    program.WellTyped := by
  by_cases definitionsAccepted : program.dataDefinitions.isWellFormed = true
  · by_cases resultAccepted :
        program.resultType.isWellFormed program.dataDefinitions = true
    · cases inferred : infer? [] program.body program.dataDefinitions with
      | none =>
          simp [Program.check, definitionsAccepted, resultAccepted, inferred] at checked
      | some inferredType =>
          have typeEquality : inferredType = program.resultType := by
            simpa [Program.check, definitionsAccepted, resultAccepted, inferred]
              using checked
          subst inferredType
          exact ⟨
            DataEnvironment.isWellFormed_sound definitionsAccepted,
            Ty.isWellFormed_sound resultAccepted,
            infer_sound inferred
          ⟩
    · simp [Program.check, definitionsAccepted, resultAccepted] at checked
  · simp [Program.check, definitionsAccepted] at checked


theorem check_sound
    {program : Program}
    (checked : program.check = true) :
    HasType [] program.body program.resultType program.dataDefinitions :=
  (check_full_sound checked).bodyHasType


theorem check_complete
    {program : Program}
    (wellTyped : program.WellTyped) :
    program.check = true := by
  simp [
    Program.check,
    DataEnvironment.isWellFormed_complete wellTyped.dataDefinitionsWellFormed,
    Ty.isWellFormed_complete wellTyped.resultTypeWellFormed,
    infer_complete wellTyped.bodyHasType
  ]


theorem check_iff_wellTyped
    {program : Program} :
    program.check = true ↔ program.WellTyped :=
  ⟨check_full_sound, check_complete⟩

end Program

end Solcore.Core
