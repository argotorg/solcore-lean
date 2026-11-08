import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConditionals
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Encoding
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.Core.Internal.Renaming
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionPrimitives

/-!
# Compatible expressions: contextual constructors

Constructor trees and certificates, proxies, and contextual conditionals and primitives.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorSource
/-! Constructor source traces use independent metadata validity and preserve
left-to-right argument effects. Native type projection alone is not a proof
of the original constructor metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference CompatibleExpressionPrimitives

private theorem mismatch_irrefl {types : List TypeSystem.Ty} {expected actual : TypeSystem.Ty}
    (mismatch : Dynamic.TypesFirstMismatch types types expected actual) : False := by
  induction types with
  | nil => cases mismatch
  | cons head tail ih =>
    cases mismatch with
    | head different => exact different rfl
    | tail failed => exact ih failed

theorem metadata_fault_excluded {context : SourceSemantics.Context} {metadata : DataConstructorInstantiation}
    {reason : Dynamic.SemanticFault} (valid : SourceSemantics.DataConstructorInstantiation.Valid context metadata)
    (fault : Dynamic.ConstructorMetadataFaults context metadata reason) : False := by
  cases valid with
  | intro dataType signature dataMember signatureMember owner constructor exact range payloads result =>
    cases fault with
    | missing absent => exact absent dataType dataMember signature signatureMember constructor.symm
    | owner entry different =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      exact different owner
    | payloadArity entry mismatch =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      exact mismatch (by simp [payloads])
    | payloadType entry mismatch =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      rw [payloads] at mismatch
      exact mismatch_irrefl mismatch
    | resultType entry different =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      exact different result

inductive PacksOutcome (metadata : DataConstructorInstantiation) :
    DataExpressionSequence.Outcome → Dynamic.ExpressionOutcome → Prop where
  | values (values : List Dynamic.Value) : PacksOutcome metadata (.ok values) (.value (.constructed metadata values))
  | fault (reason : Dynamic.SemanticFault) : PacksOutcome metadata (.error reason) (.fault reason)

theorem PacksOutcome.functional {metadata : DataConstructorInstantiation} {sequence : DataExpressionSequence.Outcome}
    {first second : Dynamic.ExpressionOutcome} (left : PacksOutcome metadata sequence first)
    (right : PacksOutcome metadata sequence second) : first = second := by
  cases left <;> cases right <;> rfl

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId}

theorem constructor_inv (metadata : Metadata checked source id node type)
    (form : node.form = .constructor instantiation arguments) (unique : NodeOccurrencesUnique source)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ sequence, DataExpressionSequence.Trace program context evidence source environment before arguments sequence after ∧
      PacksOutcome instantiation sequence outcome := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructor _ _ children => exact ⟨_, .values children, .values _⟩
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructorArgument _ children => exact ⟨_, .fault children, .fault _⟩
    | constructorMetadata _ badMetadata => exact False.elim (metadata_fault_excluded valid badMetadata)

theorem constructor_intro (metadata : Metadata checked source id node type)
    (form : node.form = .constructor instantiation arguments)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    {sequence : DataExpressionSequence.Outcome}
    (trace : DataExpressionSequence.Trace program context evidence source environment before arguments sequence after)
    (packed : PacksOutcome instantiation sequence outcome) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases packed with
  | values values =>
    cases trace with
    | values children =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
      · rw [form, metadata.requirements, metadata.coercions]
        exact .constructor rfl valid children
      · rw [metadata.coercions]; exact .nil
  | fault reason =>
    cases trace with
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
      rw [form, metadata.requirements, metadata.coercions]
      exact .constructorArgument rfl failed

theorem constructor_source_types
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .constructor instantiation arguments) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    SourceSemantics.DataConstructorInstantiation.Admissible context instantiation ∧
      ExpressionsHaveTypes source context arguments instantiation.payloadTypes ∧ node.type = instantiation.resultType := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | constructor constructorValid children => exact ⟨constructorValid, children, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConditionals
/-! The actual contextual dispatcher supplies the ordinary conditional-tree policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core Frontend SourceInference

/-- Metadata for the ordinary fragment in this source view. Conditions apply
only to occurrences admitting the finite grammar, not arbitrary source forms. -/
structure Ordinary (source : TypedSource) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceSpecialization.SpecializationKey) : Prop where
  requirements : ∀ id node, Syntax source id → source.lookupExpression? id = some node →
    node.requirements = CompatibleExpressionLiterals.owned node.form
  coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = []
  notInitializer : ∀ id, Syntax source id → locals.bindings.find?
    (fun binding => decide (binding.caller = owner ∧ binding.initializer = id)) = none
  localBinder : ∀ id node name binder, Syntax source id → source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : Ordinary source locals owner) (syntaxTree : Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | primitive syntaxTree =>
    cases syntaxTree with
    | product syntaxTree =>
      cases syntaxTree with
      | @literal _ literalNode found atomic =>
        generalize form : literalNode.form = shape at atomic
        cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
      | read found form =>
        have localBinder := ordinary.localBinder _ _ _ _ (.primitive (.product (.read found form))) found form
        simp only [SourceCoreGeneralFunctions.contextualSource, found, form, localBinder, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
      | group found form child => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
      | pair found form first second => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
    | unary found form child | binary found form first second | group found form child | pair found form first second =>
      simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | unary found form child | binary found form first second | group found form child | pair found form first second | conditional found form _ _ _ =>
    simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | primitive syntaxTree =>
    cases syntaxTree with
    | product syntaxTree =>
      cases syntaxTree with
      | @literal _ literalNode originalFound atomic =>
        have same := Option.some.inj (originalFound.symm.trans found)
        subst node
        generalize form : literalNode.form = shape at atomic
        cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
          CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
      | read originalFound form | group originalFound form _ | pair originalFound form _ _ =>
        have same := Option.some.inj (originalFound.symm.trans found)
        subst node
        simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
          CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
    | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
  | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | primitive syntaxTree =>
    cases syntaxTree with
    | product child => cases child <;> exact ⟨_, by assumption⟩
    | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ => exact ⟨_, found⟩
  | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ => exact ⟨_, found⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Complete ordinary primitive trees are extracted from the production
contextual traversal, at root or full specialized parent context. -/
theorem tree_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context}
    (ordinary : Ordinary source locals context.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine tree_of_functions unique declarations ?_ ordinary.coercions syntaxTree found typed accepted
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ prepared.caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [bind, Except.bind, readPolicy]
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := context_bind_accepted accepted
      refine tree_of_functions unique declarations ?_ ordinary.coercions syntaxTree found typed generated
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, pure, Except.pure, childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, readPolicy]

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorCertificates
/-! Receipts for the real constructor compiler preserve its raw metadata ID,
registered native layout, and ordered child compilation results. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference CompatibleExpressionPrimitives CompatiblePayload DataPatternValues
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer
open CompatibleEncoding (bind_ok mapError_ok)

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

/-- The existing callback sequence, named only to state its static receipt. -/
def argument (values : ValuesContext) (child : Child) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (site : SourceCoreElaboration.ErrorSite) (reasonAt : ExpressionId → Word)
    (input : ExpressionId × TypeSystem.Ty) : Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr := do
  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked site input.2
  let lowered ← child fuel source scope input.1 reasonAt
  SourceCoreBasic.ensureType site expected lowered.type
  pure lowered

structure Argument (values : ValuesContext) (child : Child) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word)
    (input : ExpressionId × TypeSystem.Ty) (code : SourceCoreBasic.LoweredExpr) : Prop where
  projected : values.checked.catalog.project input.2 = .ok code.type
  generated : child fuel source scope input.1 reasonAt = .ok code

theorem argument_of_accepted {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {site : SourceCoreElaboration.ErrorSite} {reasonAt : ExpressionId → Word}
    {input : ExpressionId × TypeSystem.Ty} {code : SourceCoreBasic.LoweredExpr}
    (accepted : argument values child fuel source scope site reasonAt input = .ok code) :
    Argument values child fuel source scope reasonAt input code := by
  unfold argument at accepted
  obtain ⟨expected, projected, accepted⟩ := bind_ok accepted
  obtain ⟨actual, generated, accepted⟩ := bind_ok accepted
  obtain ⟨success, checked, accepted⟩ := bind_ok accepted
  cases success
  cases accepted
  have typeEq := ensureType_ok checked
  exact ⟨typeEq ▸ CompatibleExpressionReads.projectType_of_accepted projected, generated⟩

theorem arguments_of_mapM {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {site : SourceCoreElaboration.ErrorSite} {reasonAt : ExpressionId → Word}
    {inputs : List (ExpressionId × TypeSystem.Ty)} {codes : List SourceCoreBasic.LoweredExpr}
    (accepted : inputs.mapM (argument values child fuel source scope site reasonAt) = .ok codes) :
    ListRel (Argument values child fuel source scope reasonAt) inputs codes := by
  induction inputs generalizing codes with
  | nil => simp at accepted; subst codes; exact .nil
  | cons input tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, generated, accepted⟩ := bind_ok accepted
    obtain ⟨rest, compiled, accepted⟩ := bind_ok accepted
    cases accepted
    exact .cons (argument_of_accepted generated) (ih compiled)

theorem arguments_projected {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {reasonAt : ExpressionId → Word} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} (count : ids.length = types.length)
    (arguments : ListRel (Argument values child fuel source scope reasonAt) (ids.zip types) codes) :
    types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil => cases types with
    | nil => cases arguments; rfl
    | cons => cases count
  | cons id ids ih => cases types with
    | nil => cases count
    | cons type types =>
      cases arguments with
      | cons head tail =>
        have rest := ih (Nat.succ.inj count) tail
        simp only [List.mapM_cons, head.projected, rest, bind, Except.bind, pure, Except.pure, List.map_cons]

structure Header (values : ValuesContext) (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (instantiation : DataConstructorInstantiation) (tag : ConstructorId)
    (header : Word) (codes : List SourceCoreBasic.LoweredExpr) : Prop where
  metadata : Metadata values.checked source id node (.namedData tag.owner)
  sourceType : node.type = instantiation.resultType
  selected : values.checked.catalog.constructor? instantiation = some tag
  original : MetadataRep values.registry (.constructor instantiation) header
  registered : values.checked.catalog.definitions.lookupConstructorPayloadType? tag =
    some (.product .word (SourceCoreCompatibleCatalog.packTypes (codes.map (·.type))))

/-- No type/evaluation property of the callback is assumed here. Successful
calls are exposed as equations to be consumed by the structural induction. -/
theorem constructor_of_lower
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {ids : List ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .constructor instantiation ids)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ tag header codes, lowered = ⟨.namedData tag.owner,
        SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ ∧
      Header values source id node instantiation tag header codes ∧ ids.length = instantiation.payloadTypes.length ∧
      ListRel (Argument values child fuel source scope reasonAt) (ids.zip instantiation.payloadTypes) codes := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := CompatibleExpressionReads.metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  by_cases sourceType : node.type = instantiation.resultType
  · simp only [sourceType, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    by_cases count : ids.length = instantiation.payloadTypes.length
    · simp only [count, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
      have resolved := mapError_ok resolved
      obtain ⟨header, metadataId, accepted⟩ := bind_ok accepted
      obtain ⟨success, checked, accepted⟩ := bind_ok accepted
      cases success
      have typeEq := ensureType_ok checked
      subst type
      obtain ⟨codes, generated, accepted⟩ := bind_ok accepted
      cases accepted
      have arguments : ListRel (Argument values child fuel source scope reasonAt) (ids.zip instantiation.payloadTypes) codes :=
        arguments_of_mapM generated
      obtain ⟨selected, types, projected, registered⟩ := CompatibleEncoding.resolveConstructor_facts resolved
      have actualProjected := arguments_projected count arguments
      have typeListEq := Except.ok.inj (projected.symm.trans actualProjected)
      subst types
      have original : MetadataRep values.registry (.constructor instantiation) header := by
        change (match values.registry.id? (.constructor instantiation) with
          | some header => Except.ok header | none => Except.error _) = .ok header at metadataId
        cases selectedId : values.registry.id? (.constructor instantiation) with
        | none => simp [selectedId] at metadataId
        | some actual =>
          simp only [selectedId, Except.ok.injEq] at metadataId
          subst actual
          exact ⟨SourceCoreRawMetadata.Registry.id?_reconstruct selectedId⟩
      exact ⟨tag, header, codes, rfl, ⟨metadata, sourceType, selected, original, registered⟩, count, arguments⟩
    · simp [count, throw, bind, Except.bind] at accepted
  · simp [sourceType, throw, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorTree
/-! Recursive constructor trees retain original payload type metadata. Their
children are certified existing expressions or further constructors. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference DataPatternValues

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionConditionals.Syntax source id) : Syntax source id
  | constructor {id node instantiation ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .constructor instantiation ids)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id

def Nodes (source : TypedSource) (ids : List ExpressionId) (types : List TypeSystem.Ty)
    (codes : List SourceCoreBasic.LoweredExpr) : Prop :=
  ListRel (fun (id, type) (_ : SourceCoreBasic.LoweredExpr) =>
    ∃ node, source.lookupExpression? id = some node ∧ node.type = type) (ids.zip types) codes

theorem sequence_of_nodes {source : TypedSource} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate}
    (count : ids.length = types.length) (nodes : Nodes source ids types codes)
    (children : ∀ id code, (id, code) ∈ ids.zip codes → certificate scope id code) :
    DataExpressionSequence.Tree source certificate scope ids types codes := by
  induction ids generalizing types codes with
  | nil => cases types with
    | nil => cases nodes; exact .nil
    | cons => cases count
  | cons id ids ih => cases types with
    | nil => cases count
    | cons type types =>
      cases nodes with
      | @cons _ _ code codes head tail =>
        obtain ⟨node, found, same⟩ := head
        have child := children id code (by simp)
        have rest := ih (Nat.succ.inj count) tail (fun id code member => children id code (by simp [member]))
        subst type
        cases rest with
        | nil => exact .single found child
        | single f g => exact .cons found child (.single f g)
        | cons f g rest => exact .cons found child (.cons f g rest)

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | constructor {id node instantiation ids tag header codes}
      (receipt : Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (count : ids.length = instantiation.payloadTypes.length)
      (nodes : Nodes source ids instantiation.payloadTypes codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Tree fuel values source context solved reasonAt scope child code) :
      Tree fuel values source context solved reasonAt scope id
        ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyCertificates
/-! Successful proxy lowering authenticates the exact raw inner type and its
registry header. The native nominal identity may share an erased runtime view;
it is not used to reconstruct or replace the original proxy metadata. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
open Core Frontend SourceInference CompatibleExpressionReads CompatiblePayload
open CompatibleEncoding (bind_ok)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

structure Header (values : ValuesContext) (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (inner : TypeSystem.Ty) (owner : DataTypeId) (header : Word) : Prop where
  metadata : Metadata values.checked source id node (.namedData owner)
  form : node.form = .proxy inner
  sourceType : node.type = .proxy inner
  identity : values.checked.catalog.identity? (.proxy inner) = some owner
  original : MetadataRep values.registry (.proxy inner) header
  registered : values.checked.catalog.definitions.lookupConstructorPayloadType? ⟨owner, 0⟩ = some .word

inductive Certificate (values : ValuesContext) (source : TypedSource) (_scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | proxy {id node inner owner header} (receipt : Header values source id node inner owner header) :
      Certificate values source _scope id
        ⟨.namedData owner, LanguageResult.success (.construct ⟨owner, 0⟩ (.word header))⟩

/-- The actual leaf branch checks raw source type equality, registered payload
layout and the existing metadata ID; it never calls its child callback. -/
theorem proxy_of_lower
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ owner header, lowered = ⟨.namedData owner, LanguageResult.success (.construct ⟨owner, 0⟩ (.word header))⟩ ∧
      Header values source id node inner owner header := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  by_cases sourceType : node.type = .proxy inner
  · simp only [sourceType, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    cases identity : values.checked.catalog.identity? (.proxy inner) with
    | none => simp [identity] at accepted
    | some owner =>
      simp only [identity] at accepted
      obtain ⟨header, metadataId, accepted⟩ := bind_ok accepted
      obtain ⟨success, checked, accepted⟩ := bind_ok accepted
      cases success
      have typeEq := ensureType_ok checked
      subst type
      by_cases registered : values.checked.catalog.definitions.lookupConstructorPayloadType? ⟨owner, 0⟩ = some .word
      · simp only [registered, ↓reduceIte, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
        subst lowered
        have original : MetadataRep values.registry (.proxy inner) header := by
          change (match values.registry.id? (.proxy inner) with
            | some header => Except.ok header | none => Except.error _) = .ok header at metadataId
          cases selected : values.registry.id? (.proxy inner) with
          | none => simp [selected] at metadataId
          | some actual =>
            simp only [selected, Except.ok.injEq] at metadataId
            subst actual
            exact ⟨SourceCoreRawMetadata.Registry.id?_reconstruct selected⟩
        exact ⟨owner, header, rfl, metadata, form, sourceType, identity, original, registered⟩
      · simp [registered, throw, bind, Except.bind] at accepted
  · simp [sourceType, throw, bind, Except.bind] at accepted

/-- An ordinary Functions leaf receipt contains no child lowering, evaluation
or function-body semantics premise. Overrides are explicitly excluded. -/
theorem certificate_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Certificate values source scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals try rw [bypass] at accepted
      all_goals
        simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
        cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
        | error error => simp [read] at accepted
        | ok pair =>
          rcases pair with ⟨other, type⟩
          have metadata := metadata_of_read read
          have same := Option.some.inj (metadata.found.symm.trans found)
          subst other
          simp only [read, form, leafPolicy] at accepted
          unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
          simp only [read, bind, Except.bind, form] at accepted
          obtain ⟨identity, header, rfl, receipt⟩ := proxy_of_lower found form accepted
          exact .proxy receipt
    · simp [owner, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions
/-! One-level typed composition for data, primitive and conditional expressions.
The children are static certificates. A recursive compiler proof supplies their
universal meanings; the actual operand/branch slot gets its runtime type from
the represented result and the existing environment follows the world extension.
No source execution or native child evaluation is a static head premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals

inductive Head (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | group {id node inner innerNode lowered}
      (metadata : Metadata checked source id node lowered.type)
      (form : node.form = .group inner) (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : certificate scope inner lowered) :
      Head checked source certificate scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : certificate scope left first)
      (secondTree : certificate scope right second) :
      Head checked source certificate scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : certificate scope operand ⟨core.operandType, childCode⟩) :
      Head checked source certificate scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : certificate scope left ⟨mode.operandType operator, leftCode⟩)
      (second : certificate scope right ⟨mode.operandType operator, rightCode⟩) :
      Head checked source certificate scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩

  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : Metadata checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
      (thenTree : certificate scope thenId ⟨type, thenCode⟩)
      (elseTree : certificate scope elseId ⟨type, elseCode⟩) :
      Head checked source certificate scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId) (first second : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code =>
  current = scope ∧ ((id = left ∧ code = first) ∨ (id = right ∧ code = second))

private theorem two_tree {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {left right : ExpressionId}
    {leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (leftFound : source.lookupExpression? left = some leftNode)
    (rightFound : source.lookupExpression? right = some rightNode) :
    DataExpressionSequence.Tree source (Two scope left right first second) scope
      [left, right] [leftNode.type, rightNode.type] [first, second] :=
  .cons leftFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ (.single rightFound ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

private theorem pair_result {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {leftType rightType : TypeSystem.Ty}
    {first second : SourceCoreBasic.LoweredExpr} {faults : FunctionCalls.FaultRep}
    {sequence : DataExpressionSequence.Outcome} {value : Value}
    (result : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world [leftType, rightType] [first, second] faults sequence value) :
    ∃ outcome, CompatibleExpressionProducts.PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (.product leftType rightType) (.product first.type second.type) faults outcome value := by
  cases result with
  | values represented =>
    change DataExpressionSequence.Values _ _ _ [leftType, rightType] [first.type, second.type] _ _ at represented
    cases represented with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        cases tail
        exact ⟨_, .values (.cons (.singleton _)), .value (.product left right)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩


private theorem pair_post {expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {ids : List ExpressionId} {type : Core.Ty}
    {sequence : DataExpressionSequence.Outcome} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (joins : ExpressionFailurePostContracts.CompositionJoins expressionPost listPost program context evidence source)
    (link : ExpressionFailurePostContracts.ExpressionsLink source id ids)
    (trace : DataExpressionSequence.Trace program context evidence source environment before ids sequence after)
    (packed : CompatibleExpressionProducts.PacksOutcome sequence outcome)
    (retained : ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source
      environment before ids type sequence after value mapping world store) :
    ExpressionFailurePostContracts.OutcomePost expressionPost program context evidence source environment
      before id type outcome after value mapping world store := by
  cases packed with
  | values _ => trivial
  | fault _ =>
    cases trace with
    | fault failed =>
      obtain ⟨token, same, retained⟩ := retained
      exact ⟨token, same, joins.expressions link failed retained⟩


variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost} {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}

theorem Head.preserves_with_post
    (unique : NodeOccurrencesUnique source)
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (joins : ExpressionFailurePostContracts.CompositionJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults expressionPost) :
    ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults expressionPost := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    have childTrace := CompatibleExpressionProducts.group_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      ih innerFound environments heaps locals agrees actualTyped childTrace
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata, ExpressionFailurePostContracts.OutcomePost.expression joins (.group contains form layout) childTrace retained⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    have children : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults expressionPost := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, sourceTrace, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      TypedDataExpressionSequence.preserves_with_post (two_tree (first := first) (second := second) leftFound rightFound) sequenceJoins children environments heaps locals agrees actualTyped sourceTrace
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata, pair_post joins (.tuple contains form layout) sourceTrace packed retained⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    have sourceStep := unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, ⟨_, rfl, joins.expression (.unary contains form layout) childTrace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | invalid childTrace failed =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih childFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    have sourceStep := binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, ⟨_, rfl, joins.expression (.binaryLeft contains form layout) childTrace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | leftInvalid childTrace invalid =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH leftFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
    | rightFault firstTrace continues secondTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨_, rfl, joins.expression (.binaryRight contains form layout firstTrace continues) secondTrace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | value firstTrace continues secondTrace applied =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second
          have same := actualApplied.functional applied
          subst sourceResult
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, trivial⟩
    | invalid firstTrace continues secondTrace failed =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, _, firstMetadata, _firstPost⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
          exact False.elim (binary_fault_excluded applied failed)

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    have sourceStep := conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, ⟨_, rfl, joins.expression (.conditionalCondition contains form layout) childTrace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | @branch flag middle outcome after conditionTrace branchTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
            elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ExpressionFailurePostContracts.OutcomePost.expression joins (.conditionalFalse contains form layout conditionTrace) branchTrace retained⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
            thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ExpressionFailurePostContracts.OutcomePost.expression joins (.conditionalTrue contains form layout conditionTrace) branchTrace retained⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH conditionFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)


theorem Head.preserves
    (unique : NodeOccurrencesUnique source)
    (meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget (Head.preserves_with_post functions program evidence unique
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
    (ExpressionFailurePostContracts.TypedPreserves.of_trivial meaning))

theorem Head.reflects_with_post
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (joins : ExpressionFailurePostContracts.CompositionJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults expressionPost) :
    ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults expressionPost := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      ih innerFound environments heaps locals agrees actualTyped evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata, ExpressionFailurePostContracts.OutcomePost.expression joins (.group contains form layout) trace retained⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    have children : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults expressionPost := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      TypedDataExpressionSequence.reflects_with_post (two_tree (first := first) (second := second) leftFound rightFound) sequenceJoins children environments heaps locals agrees actualTyped evaluated
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata, pair_post joins (.tuple contains form layout) sourceTrace packed retained⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    rw [unary_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, ⟨_, rfl, joins.expression (.unary contains form layout) failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, ⟨_, rfl, joins.expression (.binaryLeft contains form layout) failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped leftEvaluation
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, trivial⟩
          · obtain ⟨rightValue, rightStore, rightEvaluation⟩ := profile.right_evaluated payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
              rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation rightEvaluation
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace continues failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨_, rfl, joins.expression (.binaryRight contains form layout firstTrace continues) failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation rightEvaluation
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              cases trace with
              | value secondTrace =>
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace continues secondTrace applied),
                  .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, trivial⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have contains := lookupExpression?_sound metadata.found
    have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
      rw [metadata.requirements, metadata.coercions]; rfl
    rw [choose_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, ⟨_, rfl, joins.expression (.conditionalCondition contains form layout) failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | value payload =>
        obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
        subst sourceEq
        subst coreEq
        cases trace with
        | value conditionTrace =>
          have selected := choose_branch_evaluated branch
          cases flag with
          | false =>
            change Evaluates _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
              elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ExpressionFailurePostContracts.OutcomePost.expression joins (.conditionalFalse contains form layout conditionTrace) branchTrace retained⟩
            simpa only [elseType] using represented
          | true =>
            change Evaluates _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
              thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ExpressionFailurePostContracts.OutcomePost.expression joins (.conditionalTrue contains form layout conditionTrace) branchTrace retained⟩
            simpa only [thenType] using represented
theorem Head.reflects
    (meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget (Head.reflects_with_post functions program evidence
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
    (ExpressionFailurePostContracts.TypedReflects.of_trivial meaning))



end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping
/-! Native typing for the existing literal/read/product/primitive/conditional
families. Visible native scope types supply the complete annotations needed by
lazy mapping defaults. Every child code is typed by the same static tree's
induction, under arbitrary administrative contexts and ambient extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev Scope := SourceCoreLocalCell.Scope

/-- Only actually visible source-cell payload types are constrained. Native
administrative types and runtime value typing do not authenticate these types. -/
def ScopeWellFormed (definitions : DataEnvironment) (scope : Scope) : Prop :=
  ∀ binder index type, SourceCoreLocalCell.lookup? scope binder = some (index, type) →
    type.WellFormed definitions

theorem ScopeWellFormed.empty (definitions : DataEnvironment) : ScopeWellFormed definitions [] := by
  intro binder index type found
  cases found

theorem ScopeWellFormed.prepend {definitions : DataEnvironment} {scope : Scope}
    (typed : ScopeWellFormed definitions scope) (binder : Resolved.LocalId) {type : Ty}
    (wellFormed : type.WellFormed definitions) : ScopeWellFormed definitions ((binder, type) :: scope) := by
  intro selected index payload found
  by_cases same : binder = selected
  · simp [SourceCoreLocalCell.lookup?, same] at found
    obtain ⟨rfl, rfl⟩ := found
    exact wellFormed
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at found
    cases tail : SourceCoreLocalCell.lookup? scope selected with
    | none => simp [tail] at found
    | some pair =>
      obtain ⟨previous, payloadType⟩ := pair
      simp only [tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact typed _ _ _ tail

def NativeTyping (definitions : DataEnvironment) (context : Core.Context)
    (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  lowered.type.WellFormed definitions ∧
    HasType context lowered.expression (LanguageResult.resultType lowered.type) definitions

theorem literal_native {solved : List SolvedRequirement} {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code)
    (definitions : DataEnvironment) (context : Core.Context) :
    NativeTyping definitions context ⟨type, code⟩ := by
  cases literal <;> exact ⟨by constructor, LanguageResult.success_hasType (by constructor)⟩

theorem read_native {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word} {scope : Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (read : CompatibleExpressionReads.LoweredRead fuel values source sourceContext reasonAt scope id lowered)
    (typed : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨certificate, same, binding⟩ := read
  have wellFormed := typed _ _ _ certificate.slot
  refine ⟨same ▸ wellFormed, ?_⟩
  rw [← same]
  exact certificate.native_hasType binding wellFormed administrative

private theorem binary_native {definitions : DataEnvironment} {context : Core.Context}
    {mode : Mode} {operator : Syntax.BinaryOp} {left right : Expr}
    (first : HasType context left (LanguageResult.resultType (mode.operandType operator)) definitions)
    (second : HasType context right (LanguageResult.resultType (mode.operandType operator)) definitions) :
    NativeTyping definitions context ⟨mode.resultType operator, mode.binary operator left right⟩ := by
  constructor
  · cases mode <;> cases operator <;> constructor
  · cases mode with
    | word => exact SourceCorePrimitive.binary_hasType first second
    | integer => exact SourceCoreInteger.binary_hasType first second

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (typed : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)
include typed in
theorem products_native
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | literal receipt =>
    obtain ⟨_, _, literal⟩ := receipt
    exact literal_native literal _ _
  | read receipt => exact read_native receipt typed administrative
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩

include typed in
theorem primitives_native
    (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | product child => exact products_native typed administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2

include typed in
theorem conditionals_native
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | primitive child => exact primitives_native typed administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩

include typed in
theorem conditionals_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := conditionals_native typed administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include typed in
/-- The production contextual traversal supplies every child certificate.
Visible cell annotations are the only additional native typing input; neither
an independently supplied tree nor a child-code typing callback is needed. -/
theorem contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionConditionals.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (syntaxTree : CompatibleExpressionConditionals.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead fuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  exact conditionals_native_at typed administrative extension
    (CompatibleExpressionConditionals.tree_of_contextual ordinary unique declarations syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)
end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualPrimitives
/-! The actual contextual dispatcher supplies the ordinary primitive-tree policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference

/-- Metadata for the ordinary fragment in this source view. Conditions apply
only to occurrences admitting the finite grammar, not arbitrary source forms. -/
structure Ordinary (source : TypedSource) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceSpecialization.SpecializationKey) : Prop where
  requirements : ∀ id node, Syntax source id → source.lookupExpression? id = some node →
    node.requirements = CompatibleExpressionLiterals.owned node.form
  coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = []
  notInitializer : ∀ id, Syntax source id → locals.bindings.find?
    (fun binding => decide (binding.caller = owner ∧ binding.initializer = id)) = none
  localBinder : ∀ id node name binder, Syntax source id → source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : Ordinary source locals owner) (syntaxTree : Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | product syntaxTree =>
    cases syntaxTree with
    | @literal _ literalNode found atomic =>
      generalize form : literalNode.form = shape at atomic
      cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
    | read found form =>
      have localBinder := ordinary.localBinder _ _ _ _ (.product (.read found form)) found form
      simp only [SourceCoreGeneralFunctions.contextualSource, found, form, localBinder, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
    | group found form child => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
    | pair found form first second => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | unary found form child | binary found form first second | group found form child | pair found form first second =>
    simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | product syntaxTree =>
    cases syntaxTree with
    | @literal _ literalNode originalFound atomic =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      generalize form : literalNode.form = shape at atomic
      cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
    | read originalFound form | group originalFound form _ | pair originalFound form _ _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
  | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | product syntaxTree => cases syntaxTree <;> exact ⟨_, by assumption⟩
  | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ => exact ⟨_, found⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Complete ordinary primitive trees are extracted from the production
contextual traversal, at root or full specialized parent context. -/
theorem tree_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context}
    (ordinary : Ordinary source locals context.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine tree_of_functions unique declarations ?_ ordinary.coercions syntaxTree found typed accepted
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ prepared.caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [bind, Except.bind, readPolicy]
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := context_bind_accepted accepted
      refine tree_of_functions unique declarations ?_ ordinary.coercions syntaxTree found typed generated
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, pure, Except.pure, childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, readPolicy]

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end
