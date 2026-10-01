import Solcore.SourceSemantics.CoreLowering.CompatiblePatternCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedTree

/-! Static certificates for the actual general match compiler. Expression and
body certificates are supplied by the caller's structural compiler proof; the
extraction assumptions mention only successful compilation, never evaluation.
The hidden scrutinee occurs in the Core scope. It is not a source lexical binder;
a later heap/environment correspondence must retain that distinction. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
open Frontend Frontend.SourceInference SourceCoreCompatibleDataMatches

abbrev ExpressionCertificate := Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop
abbrev BodyCertificate := Scope → List StatementId → Core.Expr → Prop

def armScope (scope : Scope) (pattern : Pattern) : Scope :=
  pattern.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope

inductive Arms (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource) (site : StatementId)
    (scope : Scope) (expected : TypeSystem.Ty) (bodyCertificate : BodyCertificate) :
    List TypedMatchCase → List (Pattern × Core.Expr) → Prop where
  | nil : Arms compilation source site scope expected bodyCertificate [] []
  | cons {arm rest pattern body arms}
      (patternCertificate : CompatiblePatternCertificates.Certificate compilation source scope site
        arm.span expected arm.pattern pattern)
      (typed : Core.HasType [] pattern.matcher pattern.functionType compilation.definitions)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body)
      (tail : Arms compilation source site scope expected bodyCertificate rest arms) :
      Arms compilation source site scope expected bodyCertificate (arm :: rest) ((pattern, body) :: arms)

inductive Fallback (bodyCertificate : BodyCertificate) (scope : Scope) (resultType : Core.Ty) :
    Option (List StatementId) → Core.Expr → Prop where
  | none : Fallback bodyCertificate scope resultType none (Core.LocalLoop.fallthrough resultType)
  | some {statements body} (certificate : bodyCertificate scope statements body) :
      Fallback bodyCertificate scope resultType (some statements) body

def hiddenBinder (_source : TypedSource) (node : StatementNode) (resolution : MatchResolution)
    (scrutinee : ExpressionNode) : TypedBinder := {
  id := resolution.hiddenScrutinee, name := "",
  scheme := ⟨[], SourceCoreRawMetadata.runtimeType scrutinee.type⟩, span := some node.span }

/-- The emitted arm fold stores only actual compiler receipts. Semantic
children are supplied by the enclosing concrete recursive statement tree. -/
inductive Branches (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (scope : Scope) (outputType : Core.Ty) (fallback : Core.Expr) :
    List (Pattern × Core.Expr) → Core.Expr → Prop where
  | nil : Branches compilation source scope outputType fallback [] (fallback.weakenAt 0)
  | cons {pattern body arms allocated next}
      (allocation : bindArmWithAllocator compilation source scope pattern.bindings outputType
        (body.weakenAt pattern.bindings.length) = .ok allocated)
      (tail : Branches compilation source scope outputType fallback arms next) :
      Branches compilation source scope outputType fallback ((pattern, body) :: arms)
        (.caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0) allocated)

/-- The certificate follows the actual hidden marked allocator and branch
fold, including the retained raw source scrutinee type and runtime marker type. -/
inductive Certificate (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource) (scope : Scope)
    (id : StatementId) (resolution : MatchResolution) (resultType : Core.Ty)
    (internalReason : Core.Word) (expressionCertificate : ExpressionCertificate)
    (bodyCertificate : BodyCertificate) : Core.Expr → Prop where
  | matchWith {node statementType scrutineeNode type scrutinee arms fallback branches code}
      (read : SourceCoreCompatibleDataExpressions.readStatement compilation.checked source id = .ok (node, statementType))
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
        resultType resolution.defaultBody fallback)
      (branchesCertified : Branches compilation source ((resolution.hiddenScrutinee, type) :: scope)
        (Core.LocalLoop.controlType resultType) fallback arms branches)
      (hiddenCompiled : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Core.Renaming.id
        (hiddenBinder source node resolution scrutineeNode) (Core.LocalLoop.controlType resultType) type scrutinee.expression
        (.caseE (.loadCell (.var 0))
          (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason)) branches) = .ok code) :
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate code

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem arms_of_mapM {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {site : StatementId}
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
    exact .cons (CompatiblePatternCertificates.certificate_of_compilePattern _ _ _ _ _ _ _ _ _ compiled)
      pattern.typed (bodyExtract _ _ _ bodyAccepted) (ih acceptedTail)

private theorem branches_of_fold
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {outputType : Core.Ty} {fallback code : Core.Expr} {arms : List (Pattern × Core.Expr)}
    (accepted : arms.foldrM (fun ((pattern, body) : Pattern × Core.Expr) (next : Core.Expr) => do
      let allocated ← bindArmWithAllocator compilation source scope pattern.bindings outputType
        (body.weakenAt pattern.bindings.length)
      pure (Core.Expr.caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0) allocated))
      (fallback.weakenAt 0) = .ok code) :
    Branches compilation source scope outputType fallback arms code := by
  induction arms generalizing code with
  | nil => simp only [List.foldrM_nil] at accepted; cases accepted; exact .nil
  | cons head rest ih =>
    obtain ⟨pattern, body⟩ := head
    simp only [List.foldrM_cons] at accepted
    obtain ⟨next, compiledNext, accepted⟩ := bind_ok accepted
    obtain ⟨allocated, compiledArm, accepted⟩ := bind_ok accepted
    cases accepted
    exact .cons compiledArm (ih compiledNext)

/-- The actual compiler's success supplies all match metadata and pattern
certificates. Callback extraction is static and uses the exact child budget and
scope; it can be discharged by an enclosing compiler's structural induction. -/
theorem certificate_of_lowerWithReasons
    {compilation : SourceCoreCompatibleDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
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
                  have finish : ∀ fallback,
                      Fallback bodyCertificate ((resolution.hiddenScrutinee, type) :: scope)
                        resultType resolution.defaultBody fallback →
                      ((do
                        let branches ← arms.foldrM (fun ((pattern, body) : Pattern × Core.Expr) (next : Core.Expr) => do
                          let allocated ← bindArmWithAllocator compilation source
                            ((resolution.hiddenScrutinee, type) :: scope) pattern.bindings
                            (Core.LocalLoop.controlType resultType) (body.weakenAt pattern.bindings.length)
                          pure (Core.Expr.caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0) allocated))
                          (fallback.weakenAt 0)
                        SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Core.Renaming.id
                          (hiddenBinder source node resolution scrutineeNode) (Core.LocalLoop.controlType resultType) type
                          scrutinee.expression (.caseE (.loadCell (.var 0))
                            (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason))
                            branches)) = .ok code) →
                      Certificate compilation source scope id resolution resultType internalReason
                        expressionCertificate bodyCertificate code := by
                    intro fallback certified accepted
                    obtain ⟨branches, compiledBranches, compiledHidden⟩ := bind_ok accepted
                    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh
                      scrutineeOwned scrutineeFound projection (expressionExtract _ _ _ _ loweredExpression) sameType
                      armCertificates certified (branches_of_fold compiledBranches) compiledHidden
                  cases fallbackForm : resolution.defaultBody with
                  | none =>
                    simp only [fallbackForm] at accepted
                    exact finish _ (by rw [fallbackForm]; exact .none) accepted
                  | some statements =>
                    simp only [fallbackForm] at accepted
                    obtain ⟨fallback, compiledFallback, accepted⟩ := bind_ok accepted
                    exact finish fallback (by rw [fallbackForm]; exact .some (bodyExtract _ _ _ _ compiledFallback)) accepted
              · simp [scrutineeOwned] at accepted
          · simp [hiddenOwned] at accepted
        · simp [requirements] at accepted
      · simp [form] at accepted
    · simp [allowed, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
