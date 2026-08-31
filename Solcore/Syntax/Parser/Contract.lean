import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.Derive
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.TypeAlias

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ContractInternals

def optionalFieldInitializer
    (expression : Parser Expr) : Parser (Option Expr) := do
  let state ← getState
  if isSymbol state .equal then
    let _ ← symbol .equal .contractMember
    pure (some (← expression))
  else
    pure none

def contractField (expression : Parser Expr) : Parser ContractField := do
  let name ← identifier .contractMember
  let _ ← symbol .colon .contractMember
  let type ← typeExpr
  let initializer ← optionalFieldInitializer expression
  let semicolon ← symbol .semicolon .contractMember
  pure {
    span := SourceSpan.cover name.span semicolon.span
    value := { name, type, initializer }
  }

end ContractInternals

namespace ContractInternals

def wrapField (declaration : ContractField) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .field declaration
}

def wrapContractFunction
    (declaration : FunctionDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .function declaration
}

def wrapConstructor
    (declaration : ConstructorDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .constructor declaration
}

def wrapFallback (declaration : FallbackDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .fallback declaration
}

def wrapContractTypeAlias
    (declaration : TypeAliasDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .typeAlias declaration
}

def wrapContractEnum (declaration : EnumDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .enum declaration
}

def mapMember {alpha : Type} (parser : Parser alpha)
    (wrap : alpha → ContractMember) : Parser ContractMember := do
  pure (wrap (← parser))

end ContractInternals

def ContractInternals.extendContractMemberStart (prefixSpan : SourceSpan)
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

namespace ContractInternals

def startsContractField (state : State) : Bool :=
  isIdentifier state && state.peekOffsetKind? 1 == some (.symbol .colon)

def rejectedContractMember : Parser ContractMember := fun state =>
  rejectAt state { head := .topItem, tail := [] } .contractMember

def contractMemberParser (state : State) : Parser ContractMember :=
  if startsContractField state then
    mapMember (contractField expression) wrapField
  else if isKeyword state .functionKw then
    mapMember (functionDecl .contract) wrapContractFunction
  else if isKeyword state .constructorKw then
    mapMember constructorDecl wrapConstructor
  else if isKeyword state .fallbackKw then
    mapMember fallbackDecl wrapFallback
  else if isKeyword state .typeKw then
    mapMember typeAlias wrapContractTypeAlias
  else if isContextual state .enum then
    mapMember (enumDecl none) wrapContractEnum
  else
    rejectedContractMember

def contractMemberCore : Parser ContractMember := fun state =>
  contractMemberParser state state

end ContractInternals

def ContractInternals.attachContractDerive (derive : DeriveAttribute)
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
      pure (ContractInternals.extendContractMemberStart derive.span member)

def ContractInternals.contractMemberWithAttribute : Parser ContractMember :=
    fun state =>
  if isSymbol state .hash then
    match deriveAttribute state with
    | .ok derive afterDerive =>
        match ContractInternals.contractMemberCore afterDerive with
        | .ok member next =>
            ContractInternals.attachContractDerive derive member next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    ContractInternals.contractMemberCore state

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
        match ContractInternals.contractMemberWithAttribute state with
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
