import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts

/-! The accepted same-Code body and its actual static Tree construct the used
terminal child receipt. Only the real terminal Source form, reader policy and
selected staged scope remain static inputs. No execution law is stored here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaStaticBodySupport
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

private theorem lowered_eq {left right : SourceCoreBasic.LoweredExpr}
    (sameType : left.type = right.type) (sameExpression : left.expression = right.expression) :
    left = right := by
  cases left
  cases right
  cases sameType
  cases sameExpression
  rfl

private theorem finish_injective {type : Ty} {left right : Expr} {fellThrough escaped : Word}
    (same : CompatibleStatements.finish type left fellThrough escaped =
      CompatibleStatements.finish type right fellThrough escaped) : left = right := by
  unfold CompatibleStatements.finish LocalControl.finish LocalLoop.toControl LanguageResult.bind at same
  exact (Expr.caseE.inj (Expr.caseE.inj same).1).1

private theorem return_value_injective {type : Ty} {left right : Expr}
    (same : LocalLoop.returnValue type left = LocalLoop.returnValue type right) : left = right := by
  unfold LocalLoop.returnValue LanguageResult.bind at same
  exact (Expr.caseE.inj same).1

section StaticTrees
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}

private theorem lexical_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      certificates context scope true statements expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases terminal with
  | returning rest found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩
  | tail found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩

private theorem imperative_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative context scope
      (.statements true statements) expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases tree
  case body syntaxTree body => exact lexical_terminal_child terminal body
  all_goals cases terminal <;> simp_all
end StaticTrees

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}

/-- Accepted lowering and the actual compiler Tree supply both the receipt and
its used child certificate at this Code's real body parameter context. -/
theorem of_actual_body_exact
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId)
    (terminal : Terminal code.view expression function.body)
    (readPolicy : body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages,
      packet.certificate = certificates body.readFuel code.view body.toContext.context ∧
      packet.child = child ∧ packet.expression = expression ∧
      certificates body.readFuel code.view body.toContext.context
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        expression packet.receipt.child := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    readPolicy terminal body.accepted
  obtain ⟨lowered, sameType, flow, certified⟩ := imperative_terminal_child terminal body.actualTree
  have sameFlow : body.flow = LocalLoop.returnValue code.receipt.resultCore receipt.child.expression :=
    finish_injective (body.emitted.symm.trans receipt.emitted)
  have sameExpression : lowered.expression = receipt.child.expression :=
    return_value_injective (flow.symm.trans sameFlow)
  have sameLowered : lowered = receipt.child :=
    lowered_eq (sameType.trans receipt.sameType.symm) sameExpression
  have used : certificates body.readFuel code.view body.toContext.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression receipt.child := sameLowered ▸ certified
  exact ⟨{
    policy := body.policy
    fuel := code.fuel
    expression := expression
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    receipt := receipt
    certificate := certificates body.readFuel code.view body.toContext.context
    certifies := fun lowered generated =>
      (Except.ok.inj (receipt.generated.symm.trans generated)) ▸ used
    child := child
    selected := selected }, rfl, rfl, rfl, used⟩

/-- The original receipt-only interface is preserved. -/
theorem of_actual_body
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId)
    (terminal : Terminal code.view expression function.body)
    (readPolicy : body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) := by
  obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
    of_actual_body_exact body expression terminal readPolicy child selected
  exact ⟨packet⟩

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Supported terminal syntax is read at the actual ordinary or principal
compiler view retained by the contextual association. -/
def TerminalShapeFor
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) : Prop :=
  match association with
  | .ordinary _ _ code _ _ _ _ _ _ _ _ => Terminal code.view expression function.body
  | .principal _ _ code _ _ _ _ _ _ _ _ => Terminal code.view expression function.body

/-- The compiler's actual statement reader is retained independently of the
chosen expression grammar and its certificates. -/
def ReadPolicyFor
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) : Prop :=
  match association with
  | .ordinary _ _ _ _ support _ _ _ _ _ _ => support.body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked
  | .principal _ _ _ _ support _ _ _ _ _ _ => support.body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked

/-- The generated packet uses precisely the actual BodyWith child certificate
at its compiler view and reached parameter context. -/
def HasBodyCertificate
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Prop :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      packet.certificate = support.certificates support.body.readFuel code.view support.body.toContext.context
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      packet.certificate = support.certificates support.body.readFuel code.view support.body.toContext.context

private abbrev body_scope {closure : Dynamic.Closure}
    {localScope : SourceCoreLocalCell.Scope} {admin : Core.Context}
    (code : Code compiled.indexed closure localScope admin) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope

/-- The packet retains the actual selected expression and its original static
child certificate, in addition to the literal BodyWith certificate family. -/
def HasBodyChild
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Prop :=
  HasBodyCertificate association packet ∧
    match association, packet with
    | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
        packet.expression = expression ∧
        support.certificates support.body.readFuel code.view support.body.toContext.context
          (body_scope code)
          expression packet.receipt.child
    | .principal _ _ code _ support _ _ _ _ _ _, packet =>
        packet.expression = expression ∧
        support.certificates support.body.readFuel code.view support.body.toContext.context
          (body_scope code)
          expression packet.receipt.child

/-- The exact certificate conclusion exposes the static child used by numeric
induction, without quantifying over arbitrary terminal packets. -/
theorem terminal_for_exact
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages,
      HasBodyChild association expression packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy child selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy child selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩

/-- Each concrete contextual association constructs TerminalFor internally
from its accepted BodyWith, without a prebuilt terminal packet. -/
theorem terminal_for
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    exact of_actual_body support.body expression terminal readPolicy child selected
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact of_actual_body support.body expression terminal readPolicy child selected

/-- The genuine prepared stage registry selects the same actual closure
from its descriptor and original Source receipt; no arbitrary registry totality
is inferred. This specializes the terminal factory to that selected scope. -/
theorem at_prepared_registry
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association) :
    Nonempty (CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table)) := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    exact of_actual_body support.body expression terminal readPolicy _ selected
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    exact of_actual_body support.body expression terminal readPolicy _ selected

/-- The real prepared registry supplies a packet whose certificate is the
same actual BodyWith child. The selected scope is constructed internally. -/
theorem at_prepared_registry_exact
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table), HasBodyChild association expression packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy _ selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy _ selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
