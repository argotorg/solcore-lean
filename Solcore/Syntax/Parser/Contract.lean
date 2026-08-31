import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.Derive
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.TypeAlias

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def contractField : Parser ContractField := do
  let name ← identifier .contractMember
  let _ ← symbol .colon .contractMember
  let type ← typeExpr
  let state ← getState
  let initializer ←
    if isSymbol state .equal then
      let _ ← symbol .equal .contractMember
      pure (some (← expression))
    else
      pure none
  let semicolon ← symbol .semicolon .contractMember
  pure {
    span := SourceSpan.cover name.span semicolon.span
    value := { name, type, initializer }
  }

private def wrapField (declaration : ContractField) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .field declaration
}

private def wrapContractFunction
    (declaration : FunctionDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .function declaration
}

private def wrapConstructor
    (declaration : ConstructorDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .constructor declaration
}

private def wrapFallback (declaration : FallbackDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .fallback declaration
}

private def wrapContractTypeAlias
    (declaration : TypeAliasDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .typeAlias declaration
}

private def wrapContractEnum (declaration : EnumDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .enum declaration
}

private def extendContractMemberStart (prefixSpan : SourceSpan)
    (member : ContractMember) : ContractMember :=
  let span := SourceSpan.cover prefixSpan member.span
  let value := match member.value with
    | .field declaration => .field { declaration with span }
    | .function declaration => .function { declaration with span }
    | .constructor declaration => .constructor { declaration with span }
    | .fallback declaration => .fallback { declaration with span }
    | .typeAlias declaration => .typeAlias { declaration with span }
    | .enum declaration => .enum { declaration with span }
    | .error => .error
  { member with span, value }

private def startsContractField (state : State) : Bool :=
  isIdentifier state && state.peekOffsetKind? 1 == some (.symbol .colon)

private def contractMemberCore : Parser ContractMember := fun state =>
  if startsContractField state then
    match contractField state with
    | .ok value next => .ok (wrapField value) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .functionKw then
    match functionDecl .contract state with
    | .ok value next => .ok (wrapContractFunction value) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .constructorKw then
    match constructorDecl state with
    | .ok value next => .ok (wrapConstructor value) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .fallbackKw then
    match fallbackDecl state with
    | .ok value next => .ok (wrapFallback value) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .typeKw then
    match typeAlias state with
    | .ok value next => .ok (wrapContractTypeAlias value) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isContextual state .enum then
    match enumDecl none state with
    | .ok value next => .ok (wrapContractEnum value) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    rejectAt state { head := .topItem, tail := [] } .contractMember

private def attachContractDerive (derive : DeriveAttribute)
    (member : ContractMember) : Parser ContractMember :=
  match member.value with
  | .enum declaration =>
      let span := SourceSpan.cover derive.span declaration.span
      pure {
        member with
        span
        value := .enum {
          declaration with
          span
          value := { declaration.value with deriveAttribute := some derive }
        }
      }
  | _ => do
      let _ ← emitDiagnostic {
        span := derive.span
        kind := .constraintViolation .deriveOnlyEnum
      }
      pure (extendContractMemberStart derive.span member)

private def contractMemberWithAttribute : Parser ContractMember := fun state =>
  if isSymbol state .hash then
    match deriveAttribute state with
    | .ok derive afterDerive =>
        match contractMemberCore afterDerive with
        | .ok member next => attachContractDerive derive member next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    contractMemberCore state

private def atContractRecoveryBoundary (state : State) : Bool :=
  isSymbol state .hash || isKeyword state .functionKw ||
    isKeyword state .constructorKw ||
    isKeyword state .fallbackKw || isKeyword state .typeKw ||
    isSymbol state .rightBrace || isContextual state .enum

private def finishRecoveredMember (first last : SourceSpan)
    (state : State) : Reply ContractMember :=
  let span := SourceSpan.cover first last
  .ok { span, leadingComments := [], value := .error } (state.emit {
    span
    kind := .recovered .contractMember
  })

private def recoverContractMemberAux (first last : SourceSpan) :
    Nat → State → Reply ContractMember
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || atContractRecoveryBoundary state then
        finishRecoveredMember first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverContractMemberAux first token.span fuel next
        | none => finishRecoveredMember first last state

private def recoverContractMember (state : State) : Reply ContractMember :=
  match state.advance? with
  | some (token, next) =>
      recoverContractMemberAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .topItem, tail := [] } .contractMember

private structure ContractBody where
  span : SourceSpan
  members : List ContractMember

private def closeContractBody (opening : Token)
    (membersRev : List ContractMember) : Parser ContractBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    members := membersRev.reverse
  }

private def contractMembers (opening : Token) :
    Nat → List ContractMember → State → Reply ContractBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, membersRev, state =>
      if isSymbol state .rightBrace then
        closeContractBody opening membersRev state
      else if state.atEnd then
        match symbol .rightBrace .topItem state with
        | .ok _ _ => .invariant (.noProgress .topLevel state.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        match contractMemberWithAttribute state with
        | .ok member next =>
            if next.cursor > state.cursor then
              contractMembers opening fuel (member :: membersRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure failedState =>
            let rewound := { failedState with cursor := state.cursor }
            if atContractRecoveryBoundary state then
              .reject failure rewound
            else
              match recoverContractMember rewound with
              | .ok member next =>
                  contractMembers opening fuel (member :: membersRev) next
              | .reject recoveryFailure next => .reject recoveryFailure next
              | .invariant error => .invariant error
        | .invariant error => .invariant error

private def contractBody : Parser ContractBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      contractMembers opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parse a canonical contract while preserving member source order. -/
def contractDecl : Parser ContractDecl := do
  let marker ← keyword .contractKw .topItem
  let name ← identifier .topItem
  let genericParameters ← optionalGenericParameters
  let body ← contractBody
  pure {
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      bodySpan := body.span
      members := body.members
    }
  }

end Solcore.Syntax.Parser
