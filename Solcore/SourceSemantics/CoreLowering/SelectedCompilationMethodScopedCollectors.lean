import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization

/-! The actual cached implementation and its accepted flow provide native child
typing. The one compiler traversal preserves every reached lexical context and
the selected method's original Source ledger and full dictionary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SelectedCompilationMethodScopedSupport
open CallablePreparedMethodRuntimeProfileFactory (policy)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {recipe : SourceCoreIndexedSession.Recipe}
  (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (member : entry ∈ compiled.indexed.entries)

include ready member in
/-- The complete physical cache bounds the actual method closure's native slots. -/
theorem body_typed :
    HasType (SourceCoreLocalCell.coreContext (parameterScope principal) ++ nativePrefix principal)
      principal.cached.compilation.body (LanguageResult.resultType principal.named.signature.resultType)
      compiled.indexed.layouts.definitions := by
  have cached := CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared member
    principal.cached.cached (CallableIndexedPreparedInventories.cached_global_at compiled principal.cached.selected)
  have supported := RecursiveNamedCatalogPreparedInitialization.supported_cached ready principal.cached.cached
  rw [principal.cached.compilation.emitted] at cached supported
  have original : HasType ((compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda principal.named.signature.parameterType (LanguageResult.resultType principal.named.signature.resultType)
        principal.cached.compilation.output)
      principal.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [List.append_assoc, List.singleton_append] using cached
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original
    (by simpa only [List.length_append, List.length_map, List.length_singleton] using supported)
  cases minimal with
  | lambda _ _ body =>
    simpa only [parameterScope, CallablePreparedMethodRuntimeProfileFactory.scope,
      nativePrefix, List.append_nil, List.append_assoc, List.cons_append] using
      CallableIndexedParameterNativeInversion.body_native principal.cached.compilation body

private def matchContext : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions
    ⟨.initial compiled.compatible.checked, principal.named.specialized.function.solvedRequirements,
      some (CallableIndexedNamedGeneration.allocator compiled.indexed principal.named), none⟩
    compiled.indexed.layouts.definitions

private theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (policy principal.cached.compilation) (matchContext principal) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

private def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  principal.cached.diagnostics.placeReason principal.named.signature.key site root none

private def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Solcore.Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else principal.cached.compilation.own.assignments.reasonAt site root (.value operator)

private def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  principal.cached.compilation.own.assignments.reasonAt site root .bitNot

private def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (type : TypeSystem.Ty) : Word :=
  principal.cached.diagnostics.placeReason principal.named.signature.key site root (some type)

private theorem assignments : CompatibleAssignmentStatements.AssignmentPolicy
    (policy principal.cached.compilation) (.initial compiled.compatible.checked)
    (invalidProjection principal) (invalidOperand principal) (missingDefault principal) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

private theorem unaryPolicy : CompatibleBitNotStatements.Policy
    (policy principal.cached.compilation) (.initial compiled.compatible.checked)
    (invalidProjection principal) (invalidUnary principal) (missingDefault principal) := rfl

variable (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)

include ready member signatures certified in
/-- Children retain the complete runtime context fields along actual binders. -/
theorem collected
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (invalidOperand principal site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (invalidUnary principal site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.Syntax principal.sourceBody.source expressionSyntax
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields packet.sourceAt.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context →
      expressionSyntax id → principal.sourceBody.source.lookupExpression? id = some node →
      ExpressionHasType principal.sourceBody.source context id node.type →
      (policy principal.cached.compilation).lowerExpression fuel principal.sourceBody.source scope id
        (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      certificates context scope id lowered) :
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (faults := faults) compiled.indexed.layouts
      principal.named.signature.key [] compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      (fun error => .sourceAllocation (reprStr error)) (.initial compiled.compatible.checked)
      principal.sourceBody.source expressionSyntax
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate principal.sourceBody.source certificates)
      compiled.indexed.layouts.definitions (nativePrefix principal)
      packet.sourceAt.context (parameterScope principal) (.statements true principal.cached.compilation.statements)
      principal.sourceBody.resultType principal.named.signature.resultType packet.flow := by
  have body := body_typed principal ready member
  rw [packet.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  obtain ⟨_, typed⟩ := SelectedCompilationMethodBodySupport.source_typing
    principal packet.sourceAt certified
  have ownership := typed.local_identity_ownership
  have current := runtime principal packet certified
  exact CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
    (expressionSyntax := expressionSyntax) (certificates := certificates) (LocalView.refl _)
    (by intro id member; cases member) packet.sourceAt.unique rfl
    (by
      intro scope binder monomorphic
      change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
      simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
      rfl)
    rfl (assignments principal) (unaryPolicy principal) operands unary (match_policy principal) rfl rfl rfl
    (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    ((CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm ▸ signatures)
    packet.sourceAt.valid.ledger
    (fun context fields scope fuel id node lowered declarations approved _reached found typed accepted nativeType native =>
      children context fields (scope := scope) (fuel := fuel) (id := id) (node := node)
        (lowered := lowered) declarations approved found typed accepted (nativeType := nativeType) native)
    syntaxTree rfl packet.shape (.refl _) current.variables_closed current.residual_variables_open
    packet.sourceAt.signatures (packet.sourceAt.declarations principal.cached.compilation)
    (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
    packet.sourceAt.projection packet.accepted flowTyped

include ready member signatures certified in
/-- The static family is issued from the original compiler callback at each
actual method stage. It contains no execution or body correspondence premise. -/
theorem of_compiler
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw semanticFaults operator
        (invalidOperand principal site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment →
      assignment.target.type = .word → semanticFaults (.invalidUnaryOperand .bitNot)
        (invalidUnary principal site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    (syntaxTree : GenericImperativeMatch.Syntax principal.sourceBody.source expressionSyntax
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType)
    (children : ∀ child, stages.Closure principal.sourceFunction child →
      ∀ context, Dynamic.RuntimeContextFields packet.sourceAt.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context →
      expressionSyntax id → principal.sourceBody.source.lookupExpression? id = some node →
      ExpressionHasType principal.sourceBody.source context id node.type →
      (policy principal.cached.compilation).lowerExpression fuel principal.sourceBody.source scope id
        (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      Certificate headers stages semanticFaults context child scope id lowered) :
    Support principal packet headers stages semanticFaults := by
  constructor
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, collected principal packet ready member signatures certified operands unary syntaxTree (children child selected)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedCollectors
