import Solcore.Frontend.RuntimeValueOwner
import Solcore.Frontend.RuntimeValueOwnerProperties
import Solcore.Frontend.RuntimeCapturedOwnerProperties
import Solcore.Frontend.ClosedSourceEvaluator

/- One executable body layer preserves complete Option endpoints. The supplied
predecessor equations include failure, arbitrary captures and complete stores;
no original-success, typing, scope uniqueness or depth-existence premise is used. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Full predecessor covariance suffices for the next body budget, including absence. -/
theorem evaluateClosedSourceBody?_mapOwners_step
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (n : Nat)
    (expressionIH : ∀ owner names captured store source,
      evaluateClosedSourceExpression? n (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceExpression? n owner names captured store source).map
        (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))))
    (bodyIH : ∀ owner names captured store source,
      evaluateClosedSourceBody? n (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceBody? n owner names captured store source).map
        (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))))
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? (n+1) (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
    (evaluateClosedSourceBody? (n+1) owner names captured store source).map
      (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))) := by
  rcases source with ⟨blockSpan,statements⟩
  cases statements with
  | nil => simp only [evaluateClosedSourceBody?,Option.map_none]
  | cons statement rest =>
    rcases statement with ⟨statementSpan,payload⟩
    cases payload <;> try (solve | simp only [evaluateClosedSourceBody?,Option.map_none])
    case returnStmt child =>
      cases rest <;> cases child <;>
        simp only [evaluateClosedSourceBody?,expressionIH,Option.map_some,Option.map_none,RuntimeValue.mapOwners]
    case block statements =>
      cases rest <;> simp only [evaluateClosedSourceBody?,bodyIH,Option.map_none]
    case letDecl name annotation initializer =>
      cases initializer with
      | none => simp only [evaluateClosedSourceBody?,Option.map_none]
      | some initializer =>
        simp only [evaluateClosedSourceBody?,expressionIH]
        cases first : evaluateClosedSourceExpression? n owner names captured store initializer with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some result =>
          rcases result with ⟨value,middle⟩
          simp only [Option.map_some,bind,Option.bind_some]
          rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
          simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons] using
            bodyIH owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
              ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) middle ⟨blockSpan,rest⟩
    case expression child semicolon =>
      cases semicolon with
      | false => simp only [evaluateClosedSourceBody?,Option.map_none]
      | true =>
        simp only [evaluateClosedSourceBody?,expressionIH]
        cases first : evaluateClosedSourceExpression? n owner names captured store child with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some result =>
          rcases result with ⟨value,middle⟩
          simpa only [first,Option.map_some,bind,Option.bind_some] using
            bodyIH owner names captured middle ⟨blockSpan,rest⟩
    case ifThen condition thenBody elseBody =>
      cases rest with
      | cons _ _ => simp only [evaluateClosedSourceBody?,Option.map_none]
      | nil =>
        cases elseBody with
        | none => simp only [evaluateClosedSourceBody?,Option.map_none]
        | some elseBody =>
          simp only [evaluateClosedSourceBody?,expressionIH]
          cases first : evaluateClosedSourceExpression? n owner names captured store condition with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,middle⟩
            cases value <;> simp only [Option.map_some,bind,Option.bind_some,
              RuntimeValue.mapOwners,bodyIH,Option.map_none]
            case bool choice => cases choice <;> rfl
    case matchWith scrutinees arms =>
      cases rest with
      | cons _ _ => simp only [evaluateClosedSourceBody?,Option.map_none]
      | nil =>
        rcases scrutinees with ⟨scrutineesSpan,⟨scrutinee,additional⟩⟩
        cases additional with
        | cons _ _ => simp only [evaluateClosedSourceBody?,Option.map_none]
        | nil =>
          rcases arms with ⟨armsSpan,⟨cases,defaultBody⟩⟩
          simp only [evaluateClosedSourceBody?,expressionIH]
          cases first : evaluateClosedSourceExpression? n owner names captured store scrutinee with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,middle⟩
            simp only [Option.map_some,bind,Option.bind_some,chooseRuntimeWordMatch?_mapOwners]
            cases selected : chooseRuntimeWordMatch? value cases defaultBody with
            | none => simp only [Option.bind_none,Option.map_none]
            | some result =>
              rcases result with ⟨chosen,tests⟩
              simpa only [selected,Option.bind_some] using bodyIH owner names captured middle chosen

end Solcore.Frontend
