import Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision

/-! Ordered arm selection from the actual match compiler's static certificate.
Every tested matcher has an independent source match/non-match and a finite,
store-preserving Core execution. The selected binder bundle is authenticated at
its retained source declaration types. Nested statement execution and binder
allocation are subsequent consumers of this decision certificate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchDecision
open Core Frontend Frontend.SourceInference
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates DataPatternValues CompatiblePatternLeaves
open CompatiblePatternExecution CompatiblePatternSuccess CompatiblePayload CompatiblePatternDecision DataEquality
open CompatibleMatchCertificates GeneralHeap
variable {compilation : Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}


/-- Literal support is indexed by the same ordered compiler arm receipt. -/
inductive Arms.LiteralSites (literals : IntegerLiteralResolution → Prop)
    {source site scope expected bodyCertificate} :
    {cases : List TypedMatchCase} → {arms : List (Pattern × Expr)} →
    Arms compilation source site scope expected bodyCertificate cases arms → Prop where
  | nil : Arms.LiteralSites literals .nil
  | cons {arm : TypedMatchCase} {rest : List TypedMatchCase} {pattern : Pattern} {body : Expr} {arms : List (Pattern × Expr)}
      {patternCertificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern pattern}
      {typed : HasType [] pattern.matcher pattern.functionType compilation.definitions}
      {bodyCertified : bodyCertificate (armScope scope pattern) arm.body body}
      {tail : Arms compilation source site scope expected bodyCertificate rest arms}
      (head : CompatiblePatternDecision.WithLiterals literals compilation source scope site arm.span expected arm.pattern pattern)
      (remaining : Arms.LiteralSites literals tail) :
      Arms.LiteralSites literals (.cons patternCertificate typed bodyCertified tail)

/-- Actual accepted pattern leaves supply support for each occurrence, including
repeated patterns and repeated requirement IDs. -/
theorem Arms.literalSites {source site scope expected bodyCertificate cases arms}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (literals : IntegerLiteralResolution → Prop)
    (leaf : ∀ span expected literal resolution matcher,
      literalMatcher compilation site span expected literal resolution = .ok matcher → literals resolution) :
    Arms.LiteralSites literals certificates := by
  induction certificates with
  | nil => exact .nil
  | cons pattern typed body tail ih =>
    exact .cons (patternCertificate := pattern) (typed := typed) (bodyCertified := body) (CompatiblePatternDecision.WithLiterals.of_certificate pattern literals
      (fun expected literal resolution matcher accepted => leaf _ expected literal resolution matcher accepted)) ih

inductive Certificate.LiteralSites (literals : IntegerLiteralResolution → Prop)
    {source scope id resolution resultType internalReason expressionCertificate bodyCertificate} :
    {code : Expr} → CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code → Prop where
  | matchWith {node statementType scrutineeNode type scrutinee arms fallback branches code}
      {read : SourceCoreCompatibleDataExpressions.readStatement compilation.checked source id = .ok (node, statementType)}
      {statementTypeValid : statementType = .unit ∨ statementType = resultType}
      {form : node.form = .matchWith resolution}
      {requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements)}
      {hiddenOwned : resolution.hiddenScrutinee.owner = source.owner}
      {hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false}
      {scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner}
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {projection : projected compilation source scrutineeNode.type = .ok type}
      {expression : expressionCertificate scope resolution.scrutinee scrutinee}
      {sameType : type = scrutinee.type}
      {armCertificates : Arms compilation source id ((resolution.hiddenScrutinee, type) :: scope)
        scrutineeNode.type bodyCertificate resolution.cases arms}
      {fallbackCertificate : Fallback bodyCertificate ((resolution.hiddenScrutinee, type) :: scope)
        resultType resolution.defaultBody fallback}
      {branchesCertified : Branches compilation source ((resolution.hiddenScrutinee, type) :: scope)
        (Core.LocalLoop.controlType resultType) fallback arms branches}
      {hiddenCompiled : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Core.Renaming.id
        (hiddenBinder source node resolution scrutineeNode) (Core.LocalLoop.controlType resultType) type scrutinee.expression
        (.caseE (.loadCell (.var 0))
          (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason)) branches) = .ok code}
      (supported : Arms.LiteralSites literals armCertificates) :
      Certificate.LiteralSites literals (.matchWith read statementTypeValid form requirements hiddenOwned hiddenFresh
        scrutineeOwned scrutineeFound projection expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled)

theorem Certificate.literalSites
    {source scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (literals : IntegerLiteralResolution → Prop)
    (leaf : ∀ span expected literal resolution matcher,
      literalMatcher compilation id span expected literal resolution = .ok matcher → literals resolution) :
    Certificate.LiteralSites literals certificate := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
    exact .matchWith (read := read) (statementTypeValid := allowed) (form := form) (requirements := requirements)
      (hiddenOwned := hiddenOwned) (hiddenFresh := hiddenFresh) (scrutineeOwned := scrutineeOwned)
      (scrutineeFound := scrutineeFound) (projection := projection) (expression := expression) (sameType := sameType)
      (fallbackCertificate := fallback) (branchesCertified := branches) (hiddenCompiled := hiddenCompiled)
      (Arms.literalSites arms literals leaf)

private theorem ordinary_requirement {context : SourceSemantics.Context}
    (valid : ContextValid compilation context) {site span expected literal resolution matcher}
    (accepted : literalMatcher compilation site span expected literal resolution = .ok matcher) :
    RequirementProves context resolution.requirement resolution.predicate := by
  have code := literalMatcher_sound compilation site span expected literal resolution matcher accepted
  cases code with
  | word target meaning retained | integer target meaning retained =>
    obtain ⟨row, member, identifier, predicate⟩ := retained
    have inContext : row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
    refine ⟨row, ⟨inContext, identifier⟩, ?_, valid.valid.entriesValid row inContext⟩
    simpa [IntegerLiteralResolution.predicate, target] using predicate

theorem Arms.ordinary_sites {source site scope expected bodyCertificate cases arms}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {context : SourceSemantics.Context} (valid : ContextValid compilation context) :
    Arms.LiteralSites (fun resolution => RequirementProves context resolution.requirement resolution.predicate) certificates :=
  Arms.literalSites certificates _ (fun _ _ _ _ _ accepted => ordinary_requirement valid accepted)

theorem Certificate.ordinary_sites
    {source scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {context : SourceSemantics.Context} (valid : ContextValid compilation context) :
    Certificate.LiteralSites (fun resolution => RequirementProves context resolution.requirement resolution.predicate) certificate :=
  Certificate.literalSites certificate _ (fun _ _ _ _ _ accepted => ordinary_requirement valid accepted)

/-- Both alternatives expose the generated matcher's exact pure execution.
No source matching judgment is supplied to the theorem. -/
theorem pattern_decides_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (_certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatiblePatternDecision.WithLiterals literals compilation source scope site span expected pattern compiled)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    (∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      CompatiblePatternLeaves.BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values) ∨
    (Dynamic.PatternDoesNotMatch context pattern sourceValue ∧ MatcherFails compiled value) := by
  obtain ⟨instructions, root, tree, supported⟩ := sites.supported
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  have payloadEq : payload = compiled.type := Except.ok.inj
    (represented.projection.symm.trans (CompatiblePatternSuccess.Tree.projected tree))
  cases payloadEq
  cases CompatiblePatternDecision.Tree.decides_with_literals literals requirements extended tree supported sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, executes⟩ := success
    subst instructions
    have sourceMatch : Dynamic.PatternMatches context pattern sourceValue bindings := .intro sourceRep matched
    exact .inl ⟨bindings, values, sourceMatch,
      bindingRep, executes⟩
  | inr failed =>
    refine .inr ⟨.intro sourceRep ?_, failed⟩
    subst instructions
    refine ⟨CompatiblePatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, executes⟩ := CompatiblePatternSuccess.Tree.success catalogValid extended tree sourceValue value bindings [] represented matched
    have impossible := (evaluation_deterministic (failed [value] [] (.var 0) (.var rfl))
      (executes [value] [] (.var 0) (.var rfl))).1
    cases impossible

theorem pattern_decides {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    (∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      CompatiblePatternLeaves.BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values) ∨
    (Dynamic.PatternDoesNotMatch context pattern sourceValue ∧ MatcherFails compiled value) := by
  exact pattern_decides_with_literals certificate _ valid.signatures (fun _ proof => proof)
    (CompatiblePatternDecision.WithLiterals.of_certificate certificate _
      (fun _ _ _ _ accepted => ordinary_requirement valid accepted)) catalogValid extended represented

/-- The first matching arm wins. The default carries its own static body
certificate, and no-branch has precisely the compiler's fallthrough code. -/
inductive Decision (compilation : Compilation) (context : SourceSemantics.Context)
    (registry : SourceCoreRawMetadata.Registry) {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    (functions : FunctionModel compilation.checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (scope : Scope) (bodyCertificate : BodyCertificate) (resultType : Ty)
    (sourceValue : Dynamic.Value) (value : Value) :
    List TypedMatchCase → List (Pattern × Expr) → Option (List StatementId) → Expr →
      Dynamic.MatchCaseSelection → Prop where
  | head {arm rest pattern body arms fallback fallbackCode bindings values}
      (matched : Dynamic.PatternMatches context arm.pattern sourceValue bindings)
      (bindingsRepresented : CompatiblePatternLeaves.BindingsRep compilation.checked registry functions mapping world
        pattern.bindings bindings values)
      (runs : MatcherRuns pattern value values)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body) :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode (.arm arm.body bindings)
  | tail {arm rest pattern body arms fallback fallbackCode selection}
      (notMatched : Dynamic.PatternDoesNotMatch context arm.pattern sourceValue)
      (fails : MatcherFails pattern value)
      (next : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
        rest arms fallback fallbackCode selection) :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode selection
  | default {statements code} (bodyCertified : bodyCertificate scope statements code) :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value [] [] (some statements)
        code (.default statements)
  | noBranch :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value [] [] none
        (LocalLoop.fallthrough resultType) .noBranch

theorem Decision.source {context : SourceSemantics.Context}
    {scope : Scope} {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection) :
    Dynamic.MatchCasesSelect context sourceValue cases fallback selection := by
  induction decision with
  | head matched => exact .head matched
  | tail notMatched _ _ ih => exact .tail notMatched ih
  | default => exact .default
  | noBranch => exact .noBranch

/-- The source arm selection and each pure matcher execution are consequences
of the actual compiler certificates, source evidence validity, and represented
input. Child statement evaluation is not assumed or concluded here. -/
theorem Arms.decides_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : Arms.LiteralSites literals certificates)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    ∃ selection, Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  revert sites
  induction certificates with
  | nil =>
    intro sites
    cases fallbackCertificate with
    | none => exact ⟨_, .noBranch⟩
    | some certified => exact ⟨_, .default certified⟩
  | cons certificate typed bodyCertified tail ih =>
    intro sites
    cases sites with
    | cons headSupported tailSupported =>
      cases pattern_decides_with_literals certificate literals signatures requirements headSupported catalogValid extended represented with
      | inl matched =>
        obtain ⟨bindings, values, matched, representedBindings, runs⟩ := matched
        exact ⟨_, .head matched representedBindings runs bodyCertified⟩
      | inr failed =>
        obtain ⟨selection, next⟩ := ih tailSupported
        exact ⟨selection, .tail failed.1 failed.2 next⟩
theorem Arms.decides {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    ∃ selection, Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  exact Arms.decides_with_literals certificates fallbackCertificate _ valid.signatures (fun _ proof => proof)
    (Arms.ordinary_sites certificates valid) catalogValid extended represented

/-- A certified whole match always has an independent ordered source arm
selection for a represented scrutinee. Execution of that arm is a separate
statement correspondence obligation. -/
theorem Certificate.source_selects_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry) {node : ExpressionNode}
    (found : source.lookupExpression? resolution.scrutinee = some node)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload) :
    ∃ selection, Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection := by
  cases sites with
  | @matchWith statementNode statementType scrutineeNode type scrutinee compiledArms fallbackCode branches code
      read allowed form ownedRequirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branchesCompiled hiddenCompiled supported =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst node
    obtain ⟨selection, decision⟩ := Arms.decides_with_literals arms fallback literals signatures requirements supported
      catalogValid extended represented
    exact ⟨selection, decision.source⟩

theorem Certificate.source_selects {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry) {node : ExpressionNode}
    (found : source.lookupExpression? resolution.scrutinee = some node)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload) :
    ∃ selection, Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection := by
  exact Certificate.source_selects_with_literals certificate _ valid.signatures (fun _ proof => proof)
    (Certificate.ordinary_sites certificate valid) catalogValid extended found represented

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchDecision
