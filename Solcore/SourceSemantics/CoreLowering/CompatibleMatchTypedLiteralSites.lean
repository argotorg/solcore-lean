import Solcore.SourceSemantics.CoreLowering.CompatibleMatchDecision
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders

/-! Independent pattern typing supplies evidence for each numeric leaf in the
actual compiler tree, including nested tuple and constructor patterns. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedLiteralSites
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatiblePatternCertificates CompatiblePatternDecision

private theorem Tree.numeric_typed
    {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} {expected : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {compiled : Pattern}
    {tree : Tree compilation source site span scope expected instructions compiled rest}
    {numeric : IntegerLiteralResolution} (occurrence : Tree.NumericAt tree numeric) :
    ∀ {context : SourceSemantics.Context} {sourceType : TypeSystem.Ty}
      {requirements : List RequirementId} {binders : List TypedBinder}
      {sourceRest : List MatchPatternInstruction},
      PatternInstructionHasType context instructions sourceType requirements binders sourceRest →
      RequirementProves context numeric.requirement numeric.predicate := by
  induction occurrence using Tree.NumericAt.rec
      (motive_2 := fun {types instructions patterns rest} tree numeric _ =>
        ∀ {context : SourceSemantics.Context} {sourceTypes : List TypeSystem.Ty}
          {requirements : List RequirementId} {binders : List TypedBinder}
          {sourceRest : List MatchPatternInstruction},
          PatternInstructionsHaveTypes context instructions sourceTypes requirements binders sourceRest →
          sourceTypes.length = types.length →
          RequirementProves context numeric.requirement numeric.predicate) with
  | literal =>
      intro context sourceType requirements binders sourceRest typed
      cases typed with
      | integerLiteral valid =>
          cases valid with
          | word _ _ evidence | integer _ _ evidence => exact evidence
  | @tuple expected type count types instructions rest children coreTypes resolution projection unpacked tree projected child ih =>
      intro context sourceType requirements binders sourceRest typed
      cases typed with
      | tuple arity elements => exact ih elements (arity.symm.trans (unpackTypes_length unpacked).symm)
  | constructor child ih =>
      intro context sourceType requirements binders sourceRest typed
      cases typed with
      | constructor valid arity arguments => exact ih arguments rfl
  | @head type types instructions afterHead rest head tail resolution first remaining child ih =>
      rename_i context sourceTypes requirements binders sourceRest typed length
      cases sourceTypes with
      | nil => simp at length
      | cons sourceType sourceTypes =>
          cases typed with
          | cons firstTyped remainingTyped => exact ih firstTyped
  | @tail type types instructions afterHead rest head tail resolution first remaining child ih =>
      rename_i context sourceTypes requirements binders sourceRest typed length
      cases sourceTypes with
      | nil => simp at length
      | cons sourceType sourceTypes =>
          cases typed with
          | cons firstTyped remainingTyped =>
              have restEq := (CompatiblePatternSourceBinders.Tree.source_binders first firstTyped).1
              cases restEq
              exact ih remainingTyped (Nat.succ.inj length)

theorem pattern_sites
    {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
    {span : Syntax.SourceSpan} {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    {context : SourceSemantics.Context} {binders : List TypedBinder} {arity : Nat}
    (signatures : context.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType context pattern expected binders arity) :
    WithLiterals (fun numeric => RequirementProves context numeric.requirement numeric.predicate)
      compilation source scope site span expected pattern compiled := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨actualArity, sameInstructions, sourceRoot⟩ := rootInstructions_sound compilation context signatures
    pattern.source pattern.resolution instructions root
  have sameArity := CompatiblePatternSourceBinders.source_arity_unique sourceRoot typed.source_represents
  subst actualArity
  refine ⟨certificate, instructions, root, tree, ?_⟩
  intro numeric occurrence
  apply Tree.numeric_typed occurrence
  rw [sameInstructions]
  exact typed.resolution_type

theorem Arms.sites
    {compilation : Compilation} {source site scope expected bodyCertificate cases arms}
    (certificates : CompatibleMatchCertificates.Arms compilation source site scope expected bodyCertificate cases arms)
    {context : SourceSemantics.Context} {control : ControlContext} {caseFacts : List BodyFacts}
    (signatures : context.signatures = compilation.signatures)
    (typed : MatchCasesHaveType source control context expected cases caseFacts) :
    CompatibleMatchDecision.Arms.LiteralSites
      (fun numeric => RequirementProves context numeric.requirement numeric.predicate) certificates := by
  induction certificates generalizing caseFacts with
  | nil => exact .nil
  | cons pattern native body tail ih =>
      cases typed with
      | cons head remaining =>
          cases head with
          | intro patternTyped extended bodyTyped =>
              exact .cons (patternCertificate := pattern) (typed := native) (bodyCertified := body) (pattern_sites pattern signatures patternTyped) (ih remaining)

theorem Certificate.sites
    {compilation : Compilation} {source scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {context : SourceSemantics.Context} {control : ControlContext} {node : ExpressionNode} {caseFacts : List BodyFacts}
    (signatures : context.signatures = compilation.signatures)
    (found : source.lookupExpression? resolution.scrutinee = some node)
    (typed : MatchCasesHaveType source control context node.type resolution.cases caseFacts) :
    CompatibleMatchDecision.Certificate.LiteralSites
      (fun numeric => RequirementProves context numeric.requirement numeric.predicate) certificate := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
      have same := Option.some.inj (scrutineeFound.symm.trans found)
      cases same
      exact .matchWith (read := read) (statementTypeValid := allowed) (form := form) (requirements := requirements)
        (hiddenOwned := hiddenOwned) (hiddenFresh := hiddenFresh) (scrutineeOwned := scrutineeOwned)
        (scrutineeFound := scrutineeFound) (projection := projection) (expression := expression) (sameType := sameType)
        (fallbackCertificate := fallback) (branchesCertified := branches) (hiddenCompiled := hiddenCompiled)
        (Arms.sites arms signatures typed)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedLiteralSites
