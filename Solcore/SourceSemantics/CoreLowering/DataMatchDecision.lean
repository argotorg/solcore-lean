import Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
import Solcore.SourceSemantics.CoreLowering.DataPatternBindings

/-! Ordered arm selection from the actual match compiler's static certificate.
Every tested matcher has an independent source match/non-match and a finite,
store-preserving Core execution. The selected binder bundle is authenticated at
its retained source declaration types. Nested statement execution and binder
allocation are subsequent consumers of this decision certificate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchDecision
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternExecution DataPatternSuccess DataPatternTypedValues DataPatternDecision DataEquality
open DataMatchCertificates

/-- Both alternatives expose the generated matcher's exact pure execution.
No source matching judgment is supplied to the theorem. -/
theorem pattern_decides {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : DataPatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value) :
    (∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      DataPatternBindings.BindingsRep compilation.checked.catalog compilation.signatures compiled.bindings bindings values ∧
      MatcherRuns compiled value values) ∨
    (Dynamic.PatternDoesNotMatch context pattern sourceValue ∧ MatcherFails compiled value) := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  cases Tree.decides valid tree sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, executes⟩ := success
    subst instructions
    have sourceMatch : Dynamic.PatternMatches context pattern sourceValue bindings := .intro sourceRep matched
    exact .inl ⟨bindings, values, sourceMatch,
      DataPatternBindings.Certificate.bindings_typed certificate valid.signatures represented sourceMatch bindingRep,
      executes⟩
  | inr failed =>
    refine .inr ⟨.intro sourceRep ?_, failed⟩
    subst instructions
    refine ⟨DataPatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, executes⟩ := DataPatternSuccess.Tree.success tree sourceValue value bindings []
      (TypedValueRep.erase represented) matched
    have impossible := (evaluation_deterministic (failed [value] [] (.var 0) (.var rfl))
      (executes [value] [] (.var 0) (.var rfl))).1
    cases impossible

/-- The first matching arm wins. The default carries its own static body
certificate, and no-branch has precisely the compiler's fallthrough code. -/
inductive Decision (compilation : Compilation) (context : SourceSemantics.Context)
    (scope : Scope) (bodyCertificate : BodyCertificate) (resultType : Ty)
    (sourceValue : Dynamic.Value) (value : Value) :
    List TypedMatchCase → List (Pattern × Expr) → Option (List StatementId) → Expr →
      Dynamic.MatchCaseSelection → Prop where
  | head {arm rest pattern body arms fallback fallbackCode bindings values}
      (matched : Dynamic.PatternMatches context arm.pattern sourceValue bindings)
      (bindingsRepresented : DataPatternBindings.BindingsRep compilation.checked.catalog compilation.signatures
        pattern.bindings bindings values)
      (runs : MatcherRuns pattern value values)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body) :
      Decision compilation context scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode (.arm arm.body bindings)
  | tail {arm rest pattern body arms fallback fallbackCode selection}
      (notMatched : Dynamic.PatternDoesNotMatch context arm.pattern sourceValue)
      (fails : MatcherFails pattern value)
      (next : Decision compilation context scope bodyCertificate resultType sourceValue value
        rest arms fallback fallbackCode selection) :
      Decision compilation context scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode selection
  | default {statements code} (bodyCertified : bodyCertificate scope statements code) :
      Decision compilation context scope bodyCertificate resultType sourceValue value [] [] (some statements)
        code (.default statements)
  | noBranch :
      Decision compilation context scope bodyCertificate resultType sourceValue value [] [] none
        (LocalLoop.fallthrough resultType) .noBranch

theorem Decision.source {compilation : Compilation} {context : SourceSemantics.Context}
    {scope : Scope} {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context scope bodyCertificate resultType sourceValue value
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
theorem Arms.decides {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value) :
    ∃ selection, Decision compilation context scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  induction certificates with
  | nil =>
    cases fallbackCertificate with
    | none => exact ⟨_, .noBranch⟩
    | some certified => exact ⟨_, .default certified⟩
  | cons certificate typed bodyCertified tail ih =>
    cases pattern_decides certificate valid represented with
    | inl matched =>
      obtain ⟨bindings, values, matched, representedBindings, runs⟩ := matched
      exact ⟨_, .head matched representedBindings runs bodyCertified⟩
    | inr failed =>
      obtain ⟨selection, next⟩ := ih
      exact ⟨selection, .tail failed.1 failed.2 next⟩
/-- A certified whole match always has an independent ordered source arm
selection for a represented scrutinee. Execution of that arm is a separate
statement correspondence obligation. -/
theorem Certificate.source_selects {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (valid : ContextValid compilation context) {node : ExpressionNode}
    (found : source.lookupExpression? resolution.scrutinee = some node)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures node.type sourceValue value) :
    ∃ selection, Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType arms fallback =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst node
    obtain ⟨selection, decision⟩ := Arms.decides arms fallback valid represented
    exact ⟨selection, decision.source⟩

end Solcore.SourceSemantics.CoreLowering.DataMatchDecision
