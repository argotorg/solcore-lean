import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts

/-! Actual ordered argument lowering supplies recursive builtin argument Trees and
native type vector. The original caller context and parent metadata are kept.
Only the reached full ordinary header is needed; no inventory-wide coverage or
argument/body execution law is part of this static extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallBuiltinArguments
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)


private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The builtin grammar embeds without changing any source, context, code or
metadata. Its semantic laws are already closed by the existing finite Tree. -/
theorem embed {readFuel : Nat} {context : SourceSemantics.Context}
    {id : ExpressionId} {code : Lowered}
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code) :
    Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code :=
  .fragment tree

private theorem sequence
    {readFuel : Nat} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {types : List TypeSystem.Ty} {codes : List Lowered}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM (fun id => child fuel source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → child fuel source scope id reasonAt = .ok code →
      CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code) :
    DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope ids types codes ∧ types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨.nil, rfl⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at accepted
      obtain ⟨code, first, accepted⟩ := bind_ok accepted
      obtain ⟨restCodes, rest, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have tree := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨remaining, projected⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      have sequence : DataExpressionSequence.Tree source
          (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
          scope (id :: ids) (type :: types) (code :: restCodes) := by
        cases remaining with
        | nil => exact sourceType ▸ .single found (embed tree)
        | single nextFound nextTree => exact sourceType ▸ .cons found (embed tree) (.single nextFound nextTree)
        | cons nextFound nextTree tailTree => exact sourceType ▸ .cons found (embed tree) (.cons nextFound nextTree tailTree)
      refine ⟨sequence, ?_⟩
      simp [List.mapM_cons, ← sourceType, tree.projected found, projected, bind, Except.bind]

/-- The actual contextual callback is consumed at each ordered argument. No
argument Tree or native parameter vector is supplied by the caller. -/
theorem of_contextual {readFuel : Nat} {context : SourceSemantics.Context}
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId}
    (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures locals parents
      assignments diagnostics compilation (some native) parent skipInitializer)
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (sourceSignatures : context.signatures = program.signatures)
    (nativeSignatures : context.signatures = values.checked.signatures)
    (typed : ExpressionHasType source context id node.type)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionBuiltins.Syntax source argument)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  have argumentsTyped := CallableCoercionRawNamedCallScalarArguments.argument_types receipt reached sourceTypes unique typed
  obtain ⟨children, projected⟩ := sequence (headers := headers) (compilation := compilation) unique argumentsTyped receipt.argumentsAccepted
    (fun argument member node code found typed accepted =>
      CompatibleExpressionBuiltins.tree_of_contextual_with_validity ordinary unique constructorValid declarations nativeSignatures (syntaxTrees argument member) found typed
        readPolicy lowerPolicy leafPolicy (by simpa only [childEq] using accepted))
  have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
  exact CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes unique sourceSignatures typed children nativeTypes

/-- Independent program typing supplies the source parameter/result receipt.
Native projections and the exact ordinary invocation evidence remain explicit. -/
theorem of_program {readFuel : Nat} {context : SourceSemantics.Context}
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId}
    (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures locals parents
      assignments diagnostics compilation (some native) parent skipInitializer)
    (reached : Reached receipt (headers := headers) header)
    (programTyped : ProgramWellFormed program)
    (projections : ∀ memberHeader, memberHeader ∈ headers →
      (memberHeader.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (memberHeader.bindings.map Prod.snd))
    (evidence : ∀ memberHeader, memberHeader ∈ headers → memberHeader.function.evidence = [])
    (unique : NodeOccurrencesUnique source)
    (sourceSignatures : context.signatures = program.signatures)
    (nativeSignatures : context.signatures = values.checked.signatures)
    (typed : ExpressionHasType source context id node.type)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionBuiltins.Syntax source argument)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  exact of_contextual receipt childEq reached
    (RecursiveNamedSourceSignatureFacts.source_types programTyped sourceSignatures projections evidence)
    unique sourceSignatures nativeSignatures typed constructorValid syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallBuiltinArguments
