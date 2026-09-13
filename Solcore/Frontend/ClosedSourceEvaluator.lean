import Solcore.Frontend.RuntimeWordMatchSelection
import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.LocalReference

/- Depth-bounded closed original fragment. Zero rejects even leaves; each child
gets the same predecessor. None does not distinguish unsupported paths, missing
values or exhausted depth. Stores and saved lexical fields remain literal. -/

set_option autoImplicit false
namespace Solcore.Frontend

mutual

/-- Search the closed original expression fragment up to a derivation-depth bound. -/
def evaluateClosedSourceExpression? (budget : Nat) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (source : Syntax.Expr) :
    Option (RuntimeValue × List RuntimeValue) :=
  match budget with
  | 0 => none
  | n + 1 =>
      match source with
      | ⟨_, .identifier name⟩ => do
          let id ← names.lookup? name.value
          let value ← captured.lookup? id
          return (value, store)
      | ⟨_, .literal literal⟩ => do
          return (.word (← interpretWordLiteral? literal), store)
      | ⟨_, .group inner⟩ => evaluateClosedSourceExpression? n owner names captured store inner
      | ⟨_, .tuple ⟨_, []⟩⟩ => some (.unit, store)
      | ⟨_, .tuple ⟨_, [left, right]⟩⟩ => do
          let (leftValue, middleStore) ← evaluateClosedSourceExpression? n owner names captured store left
          let (rightValue, finalStore) ← evaluateClosedSourceExpression? n owner names captured middleStore right
          return (.pair leftValue rightValue, finalStore)
      | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ => do
          let (headValue, middleStore) ← evaluateClosedSourceExpression? n owner names captured store first
          let (tailValue, finalStore) ← evaluateClosedSourceExpression? n owner names captured middleStore
            ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
          return (.pair headValue tailValue, finalStore)
      | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store condition | none
          evaluateClosedSourceExpression? n owner names captured middleStore
            (if choice then thenBranch else elseBranch)
      | ⟨_, .call callee ⟨_, [argument]⟩⟩ => do
          let (function, calleeStore) ← evaluateClosedSourceExpression? n owner names captured store callee
          let (argumentValue, argumentStore) ← evaluateClosedSourceExpression? n owner names captured calleeStore argument
          let .sourceClosure saved savedOwner savedNames savedCaptured := function | none
          let (name, body) ← sourceUnaryLambdaShape? saved
          let id := Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)
          evaluateClosedSourceBody? n savedOwner ((name.value, id) :: savedNames)
            ((id, argumentValue) :: savedCaptured) argumentStore body
      | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ => do
          let (.bool value, finalStore) ←
            evaluateClosedSourceExpression? n owner names captured store operand | none
          return (.bool (!value), finalStore)
      | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ => do
          let (.word value, finalStore) ←
            evaluateClosedSourceExpression? n owner names captured store operand | none
          return (.word value.bitNot, finalStore)
      | ⟨_, .binary left ⟨_, .logicalAnd⟩ right⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store left | none
          if choice then evaluateClosedSourceExpression? n owner names captured middleStore right
          else return (.bool false, middleStore)
      | ⟨_, .binary left ⟨_, .logicalOr⟩ right⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store left | none
          if choice then return (.bool true, middleStore)
          else evaluateClosedSourceExpression? n owner names captured middleStore right
      | _ => do
          let _ ← sourceUnaryLambdaShape? source
          return (.sourceClosure source owner names captured, store)
termination_by budget

/-- Search original body rules with the same predecessor bound for every child. -/
def evaluateClosedSourceBody? (budget : Nat) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (source : Syntax.Block) :
    Option (RuntimeValue × List RuntimeValue) :=
  match budget with
  | 0 => none
  | n + 1 =>
      match source with
      | ⟨_, [⟨_, .returnStmt none⟩]⟩ => some (.unit, store)
      | ⟨_, [⟨_, .returnStmt (some child)⟩]⟩ =>
          evaluateClosedSourceExpression? n owner names captured store child
      | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
          evaluateClosedSourceBody? n owner names captured store ⟨innerSpan, statements⟩
      | ⟨blockSpan, ⟨_, .letDecl name _ (some initializer)⟩ :: rest⟩ => do
          let (boundValue, middleStore) ← evaluateClosedSourceExpression? n owner names captured store initializer
          let id := Resolved.freshLocalId owner (names.map Prod.snd)
          evaluateClosedSourceBody? n owner ((name.value, id) :: names)
            ((id, boundValue) :: captured) middleStore ⟨blockSpan, rest⟩
      | ⟨blockSpan, ⟨_, .expression child true⟩ :: rest⟩ => do
          let (_, middleStore) ← evaluateClosedSourceExpression? n owner names captured store child
          evaluateClosedSourceBody? n owner names captured middleStore ⟨blockSpan, rest⟩
      | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store condition | none
          if choice then evaluateClosedSourceBody? n owner names captured middleStore thenBody
          else evaluateClosedSourceBody? n owner names captured middleStore elseBody
      | ⟨_, [⟨_, .matchWith ⟨_, ⟨scrutinee, []⟩⟩ ⟨_, ⟨cases, defaultBody⟩⟩⟩]⟩ => do
          let (actual, middleStore) ← evaluateClosedSourceExpression? n owner names captured store scrutinee
          let (selected, _) ← chooseRuntimeWordMatch? actual cases defaultBody
          evaluateClosedSourceBody? n owner names captured middleStore selected
      | _ => none
termination_by budget

end

end Solcore.Frontend
