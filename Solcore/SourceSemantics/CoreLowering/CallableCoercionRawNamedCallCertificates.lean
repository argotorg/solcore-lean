import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning

/-! One actual outer direct call selects an ordinary catalog header. Coverage
is required only for this reached full record; coercion methods in the same
global inventory need not be ordinary headers. The ordered argument Tree uses
the original source and actual callback results. Execution laws are absent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallCertificates
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates RecursiveNamedCatalog

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

/-- Reached inventory coverage retains the entire specialization and signature,
not just their keys or erased native types. No all-global coverage is required. -/
structure Reached (header : Header prepared values ambient.definitions program) : Prop where
  member : header ∈ headers
  plan : compilation.plan = base.plan
  specialized : receipt.selection.specialized = header.named.specialized
  signature : receipt.native.signature = header.named.signature
  slot : receipt.native.index = header.slot
  occurrenceOrder : instantiation.parameterSubstitution.map Prod.fst =
    (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse
  headerOrder : header.instantiation.parameterSubstitution.map Prod.fst =
    (header.named.specialized.parameterSubstitution.map Prod.fst).reverse

theorem Reached.metadata (reached : Reached receipt (headers := headers) header) :
    instantiation = header.instantiation := by
  have present : (receipt.native.signature, receipt.native.index) ∈
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = receipt.selection.key)) := by
    rw [receipt.native.global]
    simp
  have key : receipt.native.signature.key = receipt.selection.key :=
    of_decide_eq_true (List.mem_filter.mp present).2
  have target : SourceCompilationPlan.exactInstantiationKey compilation.plan header.instantiation =
      .ok receipt.selection.key := by
    rw [reached.plan, ← key, reached.signature]
    exact header.target
  have matched := CallableNamedMetadata.matches_of_exact target receipt.selection.selected
  have first := receipt.selection.metadata.retained_canonical reached.occurrenceOrder
  have second := matched.retained_canonical (by simpa only [reached.specialized] using reached.headerOrder)
  exact first.trans second.symm

theorem Reached.predicates (reached : Reached receipt (headers := headers) header) :
    instantiation.predicates = [] := by
  have matched := receipt.selection.metadata.predicates
  rw [reached.specialized] at matched
  exact matched.symm.trans header.closed

theorem Reached.arity (reached : Reached receipt (headers := headers) header) :
    header.function.parameters.length = arguments.length := by
  have inputs : receipt.selection.specialized.function.typedBody.inputs = header.function.parameters := by
    rw [reached.specialized, ← header.agreement.source, header.inputs, ← header.parameters]
  simpa only [inputs] using receipt.arity.symm

/-- Independent original typing determines the raw return type and source
callee fields before the output coercion path. It does not run the source. -/
theorem source_types {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (typed : ExpressionHasType source context id node.type) :
    node.rawType = header.function.resultType ∧
    ∃ calleeNode name, source.lookupExpression? callee = some calleeNode ∧
      calleeNode.form = .reference name (.declaration header.instantiation) ∧
      calleeNode.requirements = [] ∧ calleeNode.coercions = [] ∧
      SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw rawEq _ _ _ =>
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
          exact ⟨_, _, lookupExpression?_complete unique contains, form, requirements, coercions, valid.toValid closed residual⟩

include receipt in
/-- With no signature predicates, the original ordered direct-call split
produces an empty invocation dictionary in every caller environment. -/
theorem source_dictionary {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (predicates : instantiation.predicates = [])
    (typed : ExpressionHasType source context id node.type)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates [] := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst same
    rw [receipt.form] at raw
    cases raw with
    | directCall _ application _ =>
      cases application with
      | intro _ _ _ _ _ _ predicatesEq =>
        cases requirements with
        | directCall valid =>
          rw [← predicatesEq, predicates] at valid
          rw [predicates]
          cases valid with
          | intro _ _ signatureValid steps ids =>
            cases signatureValid
            exact .intro steps ids .nil

/-- The static argument certificate refers to exactly the ordered code list
returned by the real outer compiler callback on the original source. -/
structure Certificate (readFuel : Nat) (context : SourceSemantics.Context)
    (header : Header prepared values ambient.definitions program) where
  reached : Reached receipt (headers := headers) header
  rawType : node.rawType = header.function.resultType
  calleeNode : ExpressionNode
  name : String
  calleeFound : source.lookupExpression? callee = some calleeNode
  calleeForm : calleeNode.form = .reference name (.declaration header.instantiation)
  calleeRequirements : calleeNode.requirements = []
  calleeCoercions : calleeNode.coercions = []
  valid : SourceSemantics.DeclarationInstantiation.Valid context header.instantiation
  evidence : header.function.evidence = []
  dictionary : ∀ evidence, Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates []
  children : DataExpressionSequence.Tree source
    (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
    scope arguments (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments
  nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd

theorem of_tree {readFuel : Nat} {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (typed : ExpressionHasType source context id node.type)
    (children : DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope arguments (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  obtain ⟨rawType, calleeNode, name, found, form, requirements, coercions, valid⟩ :=
    source_types receipt reached sourceTypes unique closed residual typed
  exact ⟨⟨reached, rawType, calleeNode, name, found, form, requirements, coercions, valid,
    sourceTypes.evidence header reached.member, source_dictionary receipt unique reached.predicates typed, children, nativeTypes⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallCertificates
