import Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchBranchesPrefix
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes

/-! Finite children of the actual compatible match compiler. Requests retain
exact scopes, statement lists and generated code. The receipt is structural;
no child evaluation is stored. The enclosing recursive statement Tree adds a
source context and a positive recursive premise for each member. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates

structure Request where
  scope : Scope
  statements : List StatementId
  code : Expr

/-- A callback certificate that can contain only the retained finite children. -/
def Occurs (requests : List Request) : BodyCertificate :=
  fun scope statements code => ⟨scope, statements, code⟩ ∈ requests

def armRequests (scope : Scope) : List TypedMatchCase → List (Pattern × Expr) → List Request
  | arm :: cases, (pattern, code) :: arms =>
      ⟨armScope scope pattern, arm.body, code⟩ :: armRequests scope cases arms
  | _, _ => []

def fallbackRequests (scope : Scope) (fallback : Option (List StatementId)) (code : Expr) : List Request :=
  match fallback with
  | none => []
  | some statements => [⟨scope, statements, code⟩]

theorem Arms.mapBodies {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {first second : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected first cases arms)
    (transport : ∀ scope statements code, first scope statements code → second scope statements code) :
    Arms compilation source site scope expected second cases arms := by
  induction certified with
  | nil => exact .nil
  | cons pattern typed body tail ih => exact .cons pattern typed (transport _ _ _ body) ih

theorem Fallback.mapBodies {first second : BodyCertificate} {scope : Scope} {type : Ty}
    {fallback : Option (List StatementId)} {code : Expr}
    (certified : Fallback first scope type fallback code)
    (transport : ∀ scope statements code, first scope statements code → second scope statements code) :
    Fallback second scope type fallback code := by
  cases certified with
  | none => exact .none
  | some body => exact .some (transport _ _ _ body)

theorem Arms.requests {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected bodyCertificate cases arms) :
    Arms compilation source site scope expected (Occurs (armRequests scope cases arms)) cases arms ∧
      ∀ request ∈ armRequests scope cases arms, bodyCertificate request.scope request.statements request.code := by
  induction certified with
  | nil => exact ⟨.nil, by intro request member; cases member⟩
  | @cons arm cases pattern code arms patternCertificate typed body tail ih =>
    obtain ⟨tailCertified, members⟩ := ih
    constructor
    · apply Arms.cons patternCertificate typed
      · exact List.mem_cons_self
      · apply Arms.mapBodies tailCertified
        intro scope statements code member
        exact List.mem_cons_of_mem _ member
    · intro request member
      cases member with
      | head => exact body
      | tail _ member => exact members _ member

theorem Fallback.requests {bodyCertificate : BodyCertificate} {scope : Scope} {type : Ty}
    {fallback : Option (List StatementId)} {code : Expr}
    (certified : Fallback bodyCertificate scope type fallback code) :
    Fallback (Occurs (fallbackRequests scope fallback code)) scope type fallback code ∧
      ∀ request ∈ fallbackRequests scope fallback code, bodyCertificate request.scope request.statements request.code := by
  cases certified with
  | none => exact ⟨.none, by intro request member; cases member⟩
  | some body =>
    constructor
    · exact .some List.mem_cons_self
    · intro request member
      cases member with
      | head => exact body
      | tail _ member => cases member

theorem Arms.requests_length {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected bodyCertificate cases arms) :
    (armRequests scope cases arms).length = cases.length := by
  induction certified with
  | nil => rfl
  | cons _ _ _ _ ih => exact congrArg Nat.succ ih

/-- Only the match's actual scrutinee occurrence needs an expression receipt. -/
theorem Certificate.mapExpressionAt
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {first second : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason first bodyCertificate code)
    (transport : ∀ lowered, first scope resolution.scrutinee lowered → second scope resolution.scrutinee lowered) :
    Certificate compilation source scope id resolution resultType internalReason second bodyCertificate code := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      (transport _ expression) sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled

/-- Every emitted arm and optional default remains in source order. Equal
requests are retained as duplicates; no set or lookup collapses occurrences. -/
theorem Certificate.finite_children
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) :
    ∃ requests,
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests, bodyCertificate request.scope request.statements request.code := by
  cases certificate with
  | @matchWith node statementType scrutineeNode type scrutinee arms fallback branches code
      read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    obtain ⟨retainedArms, armMembers⟩ := Arms.requests armCertificates
    obtain ⟨retainedFallback, fallbackMembers⟩ := Fallback.requests fallbackCertificate
    refine ⟨armRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.cases arms ++
      fallbackRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.defaultBody fallback, ?_, ?_, ?_⟩
    · apply Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType
      · apply Arms.mapBodies retainedArms
        intro scope statements code member
        exact List.mem_append_left _ member
      · apply Fallback.mapBodies retainedFallback
        intro scope statements code member
        exact List.mem_append_right _ member
      · exact branchesCertified
      · exact hiddenCompiled
    · have count := Arms.requests_length armCertificates
      rw [List.length_append, count]
      cases resolution.defaultBody <;> rfl
    · intro request member
      rcases List.mem_append.mp member with left | right
      · exact armMembers _ left
      · exact fallbackMembers _ right

/-- The finite certificate is extracted from the real callback invocations;
its child facts contain compiler equations, not semantic executions. -/
theorem finite_of_lower
    {compilation : SourceCoreCompatibleDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {resolution : MatchResolution} {resultType : Ty}
    {reasonAt : ExpressionId → Word} {internalReason : Word} {code : Expr}
    {expressionCertificate : ExpressionCertificate}
    (expressionExtract : ∀ childFuel result,
      lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok result →
      expressionCertificate scope resolution.scrutinee result)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code) :
    ∃ requests,
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests, ∃ childFuel,
        lowerBody childFuel source request.scope request.statements resultType reasonAt internalReason = .ok request.code := by
  have raw := certificate_of_lowerWithReasons
    (expressionCertificate := fun scope id lowered => ∃ childFuel,
      lowerExpression childFuel source scope id reasonAt = .ok lowered)
    (bodyCertificate := fun scope statements code => ∃ childFuel,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩) accepted
  apply Certificate.finite_children (bodyCertificate := fun scope statements code => ∃ childFuel,
    lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code)
  exact Certificate.mapExpressionAt raw (fun lowered ⟨childFuel, generated⟩ => expressionExtract childFuel lowered generated)

/-- A selected arm/default exposes a member of the same finite request list.
No-branch fallthrough has no body child and is kept as its own alternative. -/
theorem selected_request {requests : List Request} {scope : Scope}
    {environment finalEnvironment : Dynamic.Environment} {heap finalHeap : Dynamic.Heap}
    {type : Ty} {selection : Dynamic.MatchCaseSelection} {finalScope : Scope} {code : Expr}
    (selected : DataMatchBranchPrefix.SelectedBody (Occurs requests) scope environment heap type
      selection finalScope finalEnvironment finalHeap code) :
    (selection = .noBranch ∧ finalScope = scope ∧ finalEnvironment = environment ∧
      finalHeap = heap ∧ code = LocalLoop.fallthrough type) ∨
    ∃ request ∈ requests, request.scope = finalScope ∧ request.code = code ∧
      ((∃ bindings, selection = .arm request.statements bindings) ∨ selection = .default request.statements) := by
  cases selected with
  | @arm statements bindings compiledBindings finalEnvironment finalHeap code binders allocated certified =>
    exact .inr ⟨⟨_, statements, code⟩, certified, rfl, rfl, .inl ⟨bindings, rfl⟩⟩
  | @default statements code certified =>
    exact .inr ⟨⟨scope, statements, code⟩, certified, rfl, rfl, .inr rfl⟩
  | noBranch => exact .inl ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Source contexts are authenticated independently of native scope/type
projection. Several arms may share a request but have different source
contexts; every such source context remains a distinct child obligation. -/
inductive ContextFor (source : TypedSource) (parent : SourceSemantics.Context)
    (scrutineeType : TypeSystem.Ty) (cases : List TypedMatchCase)
    (fallback : Option (List StatementId)) (request : Request) : SourceSemantics.Context → Prop where
  | arm {arm binders arity context}
      (member : arm ∈ cases) (statements : request.statements = arm.body)
      (patternTyped : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
      (extended : BindersExtend source.owner parent binders context) :
      ContextFor source parent scrutineeType cases fallback request context
  | default (statements : fallback = some request.statements) :
      ContextFor source parent scrutineeType cases fallback request parent

/-- Independent pattern/body typing identifies the selected arm's context.
The actual request is compared only on its source statement list here; its
native scope/code remains the separate compiler receipt. -/
theorem ContextFor.selected_arm
    {source : TypedSource} {control : ControlContext} {parent : SourceSemantics.Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)} (request : Request)
    (sameBody : request.statements = body)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings)) :
    ∃ context finalContext bodyFacts,
      ContextFor source parent scrutineeType cases fallback request context ∧
      BindersExtend source.owner parent (bindings.map Prod.fst) context ∧
      StatementsHaveType source control context body finalContext bodyFacts ∧ bodyFacts ∈ facts := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro patternTyped extended bodyTyped =>
        exact ⟨_, _, _, .arm List.mem_cons_self sameBody patternTyped extended,
          DataMatchSourceScopes.PatternMatches.binders patternTyped matched ▸ extended,
          bodyTyped, List.mem_cons_self⟩
  | @tail arm rest _ _ notMatched selected =>
    cases typed with
    | cons head tail =>
      obtain ⟨context, finalContext, bodyFacts, child, extended, bodyTyped, member⟩ :=
        ContextFor.selected_arm request sameBody tail selected
      have lifted : ContextFor source parent scrutineeType (arm :: rest) fallback request context := by
        cases child with
        | arm member same typed extended => exact .arm (List.mem_cons_of_mem _ member) same typed extended
        | default same => exact .default same
      exact ⟨context, finalContext, bodyFacts, lifted, extended, bodyTyped, List.mem_cons_of_mem _ member⟩
termination_by cases.length


private theorem binder_context_unique {owner : Resolved.DeclarationId} {parent first second : SourceSemantics.Context}
    {binders : List TypedBinder} (left : BindersExtend owner parent binders first)
    (right : BindersExtend owner parent binders second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases head
    cases right with
    | cons head tail => cases head; exact ih tail

theorem ContextFor.selected_arm_at
    {source : TypedSource} {control : ControlContext} {parent armContext : SourceSemantics.Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)} (request : Request)
    (sameBody : request.statements = body)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings))
    (extended : BindersExtend source.owner parent (bindings.map Prod.fst) armContext) :
    ContextFor source parent scrutineeType cases fallback request armContext := by
  obtain ⟨context, _, _, selectedContext, sameExtension, _, _⟩ :=
    ContextFor.selected_arm request sameBody typed selected
  exact binder_context_unique sameExtension extended ▸ selectedContext

theorem ContextFor.closed_fields
    {source : TypedSource} {parent child : SourceSemantics.Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {request : Request}
    (selected : ContextFor source parent scrutineeType cases fallback request child) :
    child.signatures = parent.signatures ∧ child.typeVariables = parent.typeVariables ∧
      child.residualTypeVariables = parent.residualTypeVariables := by
  cases selected with
  | arm _ _ patternTyped extended =>
    clear patternTyped
    induction extended with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons head tail ih => cases head; exact ih
  | default => exact ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
