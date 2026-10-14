import Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchAmbientLowering

/-! Match receipts retain the actual callback action, its scrutinee action and
all emitted arm/default requests in source order. The body callback fixes its
predecessor budget and false execution mode exactly as the compiler does. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedMatchFlow
open Core Frontend SourceInference
open CompatibleMatchCertificates GenericMatchChildren SourceCoreCompatibleDataMatches

abbrev Callback := SourceCoreLoops.ExpressionLowerer → SourceCoreLoops.FlowLowerer → Nat →
  TypedSource → SourceCoreLocalCell.Scope → StatementId → MatchResolution → Ty →
  (ExpressionId → Word) → Word → Except SourceCoreBasic.Error Expr

def bodyCallback (policy : SourceCoreLoops.Policy) (fuel : Nat) : SourceCoreLoops.FlowLowerer :=
  fun _ source scope statements result reasonAt escaped =>
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements result reasonAt false escaped

structure Receipt (policy : SourceCoreLoops.Policy)
    (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : StatementId) (resolution : MatchResolution)
    (result : Ty) (reasonAt : ExpressionId → Word) (escaped : Word) (fuel : Nat) (code : Expr) where
  callback : Callback
  selected : policy.lowerMatch = some callback
  accepted : callback policy.lowerExpression (bodyCallback policy fuel) fuel source scope id resolution
    result reasonAt escaped = .ok code
  childFuel : Nat
  child : SourceCoreBasic.LoweredExpr
  generated : policy.lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok child
  requests : List Request
  certificate : Certificate compilation source scope id resolution result escaped
    (fun childScope expression lowered => childScope = scope ∧ expression = resolution.scrutinee ∧ lowered = child)
    (Occurs requests) code
  count : requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0)
  original : ∀ request ∈ requests,
    (∃ arm ∈ resolution.cases, request.statements = arm.body) ∨
      resolution.defaultBody = some request.statements
  bodies : ∀ request ∈ requests,
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source request.scope request.statements
      result reasonAt false escaped = .ok request.code

private theorem armRequests_original (scope : SourceCoreLocalCell.Scope)
    (cases : List TypedMatchCase) (arms : List (Pattern × Expr))
    (request : Request) (member : request ∈ armRequests scope cases arms) :
    ∃ arm ∈ cases, request.statements = arm.body := by
  induction cases generalizing arms with
  | nil => cases member
  | cons arm cases ih =>
    cases arms with
    | nil => cases member
    | cons head arms =>
      cases head with
      | mk pattern code =>
        cases member with
        | head => exact ⟨arm, List.mem_cons_self, rfl⟩
        | tail _ member =>
          obtain ⟨selected, included, same⟩ := ih arms member
          exact ⟨selected, List.mem_cons_of_mem _ included, same⟩

private theorem fallbackRequests_original (scope : SourceCoreLocalCell.Scope)
    (fallback : Option (List StatementId)) (code : Expr)
    (request : Request) (member : request ∈ fallbackRequests scope fallback code) :
    fallback = some request.statements := by
  cases fallback with
  | none => cases member
  | some statements =>
    cases member with
    | head => rfl
    | tail _ member => cases member

/-- The selected compiler callback supplies the complete finite receipt.
No source syntax or child execution premise is used. -/
theorem of_accepted {policy : SourceCoreLoops.Policy}
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reasonAt : ExpressionId → Word} {escaped : Word} {fuel : Nat} {code : Expr}
    {callback : Callback}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy compilation)
    (selected : policy.lowerMatch = some callback)
    (accepted : callback policy.lowerExpression (bodyCallback policy fuel) fuel source scope id resolution
      result reasonAt escaped = .ok code) :
    Nonempty (Receipt policy compilation source scope id resolution result reasonAt escaped fuel code) := by
  have actual := matchPolicy selected accepted
  have raw := CompatibleMatchCertificates.certificate_of_lowerWithReasons
    (expressionCertificate := fun childScope expression lowered => ∃ childFuel,
      policy.lowerExpression childFuel source childScope expression reasonAt = .ok lowered)
    (bodyCertificate := fun childScope statements code =>
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source childScope statements
        result reasonAt false escaped = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun _ _ _ _ generated => generated) actual
  cases raw with
  | @matchWith node statementType scrutineeNode type child arms fallback branches code
      read statementTypeValid form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    obtain ⟨childFuel, generated⟩ := expression
    obtain ⟨retainedArms, armMembers⟩ := Arms.requests armCertificates
    obtain ⟨retainedFallback, fallbackMembers⟩ := Fallback.requests fallbackCertificate
    refine ⟨⟨callback, selected, accepted, childFuel, child, generated,
      armRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.cases arms ++
        fallbackRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.defaultBody fallback,
      ?_, ?_, ?_, ?_⟩⟩
    · apply Certificate.matchWith read statementTypeValid form requirements hiddenOwned hiddenFresh
        scrutineeOwned scrutineeFound projection ⟨rfl, rfl, rfl⟩ sameType
      · apply Arms.mapBodies retainedArms
        intro scope statements code member
        exact List.mem_append_left _ member
      · apply Fallback.mapBodies retainedFallback
        intro scope statements code member
        exact List.mem_append_right _ member
      · exact branchesCertified
      · exact hiddenCompiled
    · rw [List.length_append, Arms.requests_length armCertificates]
      cases resolution.defaultBody <;> rfl
    · intro request member
      rcases List.mem_append.mp member with left | right
      · exact .inl (armRequests_original _ _ _ _ left)
      · exact .inr (fallbackRequests_original _ _ _ _ right)
    · intro request member
      rcases List.mem_append.mp member with left | right
      · exact armMembers _ left
      · exact fallbackMembers _ right

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedMatchFlow
