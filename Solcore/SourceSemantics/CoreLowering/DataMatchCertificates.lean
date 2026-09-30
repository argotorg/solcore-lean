import Solcore.SourceSemantics.CoreLowering.DataPatternCertificates

/-! Static certificates for the actual general match compiler. Expression and
body certificates are supplied by the caller's structural compiler proof; the
extraction assumptions mention only successful compilation, never evaluation.
The hidden scrutinee occurs in the Core scope. It is not a source lexical binder;
a later heap/environment correspondence must retain that distinction. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
open Frontend Frontend.SourceInference SourceCoreDataMatches

abbrev ExpressionCertificate := Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop
abbrev BodyCertificate := Scope → List StatementId → Core.Expr → Prop

def armScope (scope : Scope) (pattern : Pattern) : Scope :=
  pattern.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope

inductive Arms (compilation : SourceCoreDataMatches.Context) (source : TypedSource) (site : StatementId)
    (scope : Scope) (expected : TypeSystem.Ty) (bodyCertificate : BodyCertificate) :
    List TypedMatchCase → List (Pattern × Core.Expr) → Prop where
  | nil : Arms compilation source site scope expected bodyCertificate [] []
  | cons {arm rest pattern body arms}
      (patternCertificate : DataPatternCertificates.Certificate compilation source scope site
        arm.span expected arm.pattern pattern)
      (typed : Core.HasType [] pattern.matcher pattern.functionType compilation.checked.catalog.definitions)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body)
      (tail : Arms compilation source site scope expected bodyCertificate rest arms) :
      Arms compilation source site scope expected bodyCertificate (arm :: rest) ((pattern, body) :: arms)

inductive Fallback (bodyCertificate : BodyCertificate) (scope : Scope) (resultType : Core.Ty) :
    Option (List StatementId) → Core.Expr → Prop where
  | none : Fallback bodyCertificate scope resultType none (Core.LocalLoop.fallthrough resultType)
  | some {statements body} (certificate : bodyCertificate scope statements body) :
      Fallback bodyCertificate scope resultType (some statements) body

/-- This constructor records the exact emitted layout, including both the
hidden cell reference and the loaded scrutinee temporary. -/
inductive Certificate (compilation : SourceCoreDataMatches.Context) (source : TypedSource) (scope : Scope)
    (id : StatementId) (resolution : MatchResolution) (resultType : Core.Ty)
    (internalReason : Core.Word) (expressionCertificate : ExpressionCertificate)
    (bodyCertificate : BodyCertificate) : Core.Expr → Prop where
  | matchWith {node statementType scrutineeNode type scrutinee arms fallback}
      (read : SourceCoreGeneralTypes.readStatement compilation.checked source id = .ok (node, statementType))
      (statementTypeValid : statementType = .unit ∨ statementType = resultType)
      (form : node.form = .matchWith resolution)
      (requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements))
      (hiddenOwned : resolution.hiddenScrutinee.owner = source.owner)
      (hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false)
      (scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (projection : projected compilation source scrutineeNode.type = .ok type)
      (expression : expressionCertificate scope resolution.scrutinee scrutinee)
      (sameType : type = scrutinee.type)
      (armCertificates : Arms compilation source id ((resolution.hiddenScrutinee, type) :: scope)
        scrutineeNode.type bodyCertificate resolution.cases arms)
      (fallbackCertificate : Fallback bodyCertificate ((resolution.hiddenScrutinee, type) :: scope)
        resultType resolution.defaultBody fallback) :
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) type scrutinee.expression
          (.caseE (.loadCell (.var 0))
            (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason))
            (arms.foldr (fun (pattern, body) next => attempt pattern (Core.LocalLoop.controlType resultType) body next)
              (fallback.weakenAt 0))))

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem arms_of_mapM {compilation : SourceCoreDataMatches.Context} {source : TypedSource} {site : StatementId}
    {scope : Scope} {expected : TypeSystem.Ty} {bodyCertificate : BodyCertificate}
    {lowerBody : BodyLowerer} {fuel : Nat} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word}
    (bodyExtract : ∀ scope statements code,
      lowerBody fuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    {cases : List TypedMatchCase} {arms : List (Pattern × Core.Expr)}
    (accepted : cases.mapM (fun arm => do
      let pattern ← compilePattern compilation fuel source scope site arm.span expected arm.pattern
      let body ← lowerBody fuel source (armScope scope pattern.pattern) arm.body resultType reasonAt internalReason
      pure (pattern.pattern, body)) = .ok arms) :
    Arms compilation source site scope expected bodyCertificate cases arms := by
  induction cases generalizing arms with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst arms
    exact .nil
  | cons arm rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨head, acceptedHead, accepted⟩ := bind_ok accepted
    obtain ⟨tail, acceptedTail, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst arms
    obtain ⟨pattern, compiled, acceptedHead⟩ := bind_ok acceptedHead
    obtain ⟨body, bodyAccepted, acceptedHead⟩ := bind_ok acceptedHead
    simp only [pure, Except.pure, Except.ok.injEq] at acceptedHead
    subst head
    exact .cons (DataPatternCertificates.certificate_of_compilePattern _ _ _ _ _ _ _ _ _ compiled)
      pattern.typed (bodyExtract _ _ _ bodyAccepted) (ih acceptedTail)

/-- The actual compiler's success supplies all match metadata and pattern
certificates. Callback extraction is static and uses the exact child budget and
scope; it can be discharged by an enclosing compiler's structural induction. -/
theorem certificate_of_lowerWithReasons
    {compilation : SourceCoreDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {resolution : MatchResolution} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word} {code : Core.Expr}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code) :
    Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate code := by
  cases fuel with
  | zero => simp [lowerWithReasons] at accepted
  | succ fuel =>
    simp only [lowerWithReasons] at accepted
    obtain ⟨⟨node, statementType⟩, read, accepted⟩ := bind_ok accepted
    by_cases allowed : statementType = .unit ∨ statementType = resultType
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at accepted
      simp only [allowed, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      by_cases form : node.form = .matchWith resolution
      · simp only [form, ↓reduceIte] at accepted
        by_cases requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements)
        · simp only [requirements, ↓reduceIte] at accepted
          by_cases hiddenOwned : resolution.hiddenScrutinee.owner = source.owner
          · simp only [hiddenOwned, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
            cases hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) with
            | true => simp [hiddenFresh] at accepted
            | false =>
              simp only [hiddenFresh, Bool.false_eq_true, ↓reduceIte] at accepted
              by_cases scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner
              · simp only [scrutineeOwned, not_true_eq_false, ↓reduceIte] at accepted
                cases scrutineeFound : source.lookupExpression? resolution.scrutinee with
                | none => simp [scrutineeFound] at accepted
                | some scrutineeNode =>
                  simp only [scrutineeFound] at accepted
                  obtain ⟨type, projection, accepted⟩ := bind_ok accepted
                  obtain ⟨scrutinee, loweredExpression, accepted⟩ := bind_ok accepted
                  obtain ⟨checked, typeAccepted, accepted⟩ := bind_ok accepted
                  have sameType : type = scrutinee.type := by
                    unfold SourceCoreBasic.ensureType at typeAccepted
                    split at typeAccepted
                    · assumption
                    · cases typeAccepted
                  obtain ⟨arms, compiledArms, accepted⟩ := bind_ok accepted
                  have armCertificates := arms_of_mapM (bodyExtract fuel) compiledArms
                  cases fallbackForm : resolution.defaultBody with
                  | none =>
                    simp only [fallbackForm, Except.ok.injEq] at accepted
                    subst code
                    exact Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh
                      scrutineeOwned scrutineeFound projection (expressionExtract _ _ _ _ loweredExpression)
                      sameType armCertificates (by rw [fallbackForm]; exact .none)
                  | some statements =>
                    simp only [fallbackForm] at accepted
                    cases compiledFallback : lowerBody fuel source ((resolution.hiddenScrutinee, type) :: scope)
                        statements resultType reasonAt internalReason with
                    | error error => simp only [compiledFallback] at accepted; cases accepted
                    | ok fallback =>
                      simp only [compiledFallback, Except.ok.injEq] at accepted
                      subst code
                      exact Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh
                        scrutineeOwned scrutineeFound projection (expressionExtract _ _ _ _ loweredExpression)
                        sameType armCertificates (by rw [fallbackForm]; exact .some (bodyExtract _ _ _ _ compiledFallback))
              · simp [scrutineeOwned] at accepted
          · simp [hiddenOwned] at accepted
        · simp [requirements] at accepted
      · simp [form] at accepted
    · simp [allowed, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
