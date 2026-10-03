import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning

/-! The reached header already retains closed declaration validity from its
independent source instantiation. Transport that exact witness into the real
caller context. Its residual-variable flag and lexical variables are unchanged;
no inference from ground types or native code is needed. Ordered argument Trees,
actual profiles and entry/capture/history receipts remain separate inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog

/-- A closed catalog context embeds in any context with the same signatures
and independently well-formed rigid binders. The target scopes are unchanged. -/
theorem catalog_supports {signatures : ProgramSignatures} {context : SourceSemantics.Context}
    (same : context.signatures = signatures) (binders : TypeParameterBindersWellFormed context) :
    Dynamic.TypeContextSupports (SourceSemantics.Context.ofSignatures signatures) context := by
  exact {
    signatures := same
    parameters := by intro parameter member; cases member
    parameterOwners := by intro parameter member; cases member
    variables := by intro metavariable member; cases member
    residualVariables := by intro impossible; cases impossible
    targetBinders := binders
  }

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


/-- Use the complete source instantiation in the actual reached header. This
contains range well-formedness, staging fields and the full predicate list. -/
theorem header_valid (header : Header prepared values ambient.definitions program)
    {context : SourceSemantics.Context}
    (signatures : context.signatures = program.signatures)
    (binders : TypeParameterBindersWellFormed context) :
    SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  have instantiated := header.frame.instantiated
  cases instantiated with
  | intro _ _ _ _ valid _ _ _ =>
    exact Dynamic.DeclarationInstantiation.Valid.transportContext (catalog_supports signatures binders) valid

/-- Original static typing supplies binder well-formedness; the reached header
supplies closed range validity even in a residually open caller context. -/
theorem source_types {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (signatures : context.signatures = program.signatures)
    (typed : ExpressionHasType source context id node.type) :
    node.rawType = header.function.resultType ∧
    ∃ calleeNode name, source.lookupExpression? callee = some calleeNode ∧
      calleeNode.form = .reference name (.declaration header.instantiation) ∧
      calleeNode.requirements = [] ∧ calleeNode.coercions = [] ∧
      SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw rawEq rawTyped _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst same
    rw [receipt.form, reached.metadata] at raw
    cases raw with
    | directCall calleeValid application _ =>
      cases application with
      | intro signatureMember _ declarationEq _ resultEq _ _ =>
        have result := resultEq.symm.trans (sourceTypes.result header reached.member _ signatureMember declarationEq)
        refine ⟨rawEq.trans result, ?_⟩
        cases calleeValid with
        | intro contains form valid _ requirements coercions =>
          exact ⟨_, _, lookupExpression?_complete unique contains, form, requirements, coercions, header_valid header signatures rawTyped.binders⟩

/-- Reuse the original certificate and exact callback code list. This factory
requires neither closed flexible scopes nor a false residual-variable flag. -/
theorem of_tree {readFuel : Nat} {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (signatures : context.signatures = program.signatures)
    (typed : ExpressionHasType source context id node.type)
    (children : DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope arguments (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  obtain ⟨rawType, calleeNode, name, found, form, requirements, coercions, valid⟩ :=
    source_types receipt reached sourceTypes unique signatures typed
  exact ⟨⟨reached, rawType, calleeNode, name, found, form, requirements, coercions, valid,
    sourceTypes.evidence header reached.member, source_dictionary receipt unique reached.predicates typed, children, nativeTypes⟩⟩


end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
