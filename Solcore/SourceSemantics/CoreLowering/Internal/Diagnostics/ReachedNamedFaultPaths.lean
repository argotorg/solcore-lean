import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GeneralExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ScalarReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedLexicalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionIndices
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.DiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.ReachedExpressionFaults
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ExpressionHeads

/-!
# Reached fault paths of named bodies

Fault paths and outcome ports by expression fragment and by body form, in reached named bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedScalarExpressionFaultPaths
/-! A scalar path carries the same primitive packet through authentic parent
receipts. Ordinary links are reused; no Source or native trace is traversed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedScalarExpressionFaultPaths
open Core Frontend SourceInference GeneralHeap CompatiblePayload ExpressionFailurePostContracts
open ReachedExpressionFaultOrigins (PrimitiveOrigin NativeTransport)
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)

inductive IndexParentLink (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment) :
    Dynamic.Heap → ExpressionId → Dynamic.Heap → ExpressionId → Prop where
  | base {values : SourceCoreCompatibleValues.Context} {id base key : ExpressionId}
      {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
      {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
      {before : Dynamic.Heap}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type) :
      IndexParentLink program context evidence source environment before id before base
  | key {values : SourceCoreCompatibleValues.Context} {id base key : ExpressionId}
      {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
      {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
      {before middle : Dynamic.Heap} {baseSource : Dynamic.Value}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle) :
      IndexParentLink program context evidence source environment before id middle key

mutual
  inductive ExpressionPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
    | prior {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId}
        (path : ReachedExpressionExtendedFaultPaths.ExpressionPath origin program context evidence source environment before id) :
        ExpressionPath origin program context evidence source environment before id
    | indexSelected {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id childId : ExpressionId}
        (link : IndexParentLink program context evidence source environment before id middle childId)
        (failed : Dynamic.ExpressionFaults program context evidence source environment middle childId reason heap)
        (child : ExpressionPath origin program context evidence source environment middle childId) :
        ExpressionPath origin program context evidence source environment before id
    | constructorArguments {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context}
        {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
        {ids : List ExpressionId} {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
        (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
        (form : node.form = .constructor instantiation ids)
        (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
        (count : ids.length = instantiation.payloadTypes.length)
        (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
        (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason heap)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id
    | memberBase {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context}
        {id base : ExpressionId} {node baseNode : ExpressionNode} {name : String} {index : Nat}
        {identity : DataTypeId} {branches : List Expr} {result childType : Ty}
        (metadata : CompatibleExpressionReads.Metadata values.checked source id node result)
        (baseMetadata : CompatibleExpressionReads.Metadata values.checked source base baseNode childType)
        (form : node.form = .member base name index)
        (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence)
          baseNode.type node.type index identity branches result)
        (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason heap)
        (child : ExpressionPath origin program context evidence source environment before base) :
        ExpressionPath origin program context evidence source environment before id
    | expression {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id childId : ExpressionId}
        (link : ExpressionLink program context evidence source environment before id middle childId)
        (child : ExpressionPath origin program context evidence source environment middle childId) :
        ExpressionPath origin program context evidence source environment before id
    | expressions {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
        (link : ExpressionsLink source id ids)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id

  inductive ExpressionsPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → List ExpressionId → Prop where
    | prior {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {ids : List ExpressionId}
        (path : ReachedExpressionExtendedFaultPaths.ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionsPath origin program context evidence source environment before ids
    | head {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
        (child : ExpressionPath origin program context evidence source environment before id) :
        ExpressionsPath origin program context evidence source environment before (id :: ids)
    | tail {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId} {value : Dynamic.Value}
        (head : Dynamic.ExpressionEvaluates program context evidence source environment before id value middle)
        (child : ExpressionsPath origin program context evidence source environment middle ids) :
        ExpressionsPath origin program context evidence source environment before (id :: ids)
end

def model_expressionPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionFaultPost :=
  fun program context evidence source environment before id reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionPath origin program context evidence source environment before id ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

def model_expressionsPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionsFaultPost :=
  fun program context evidence source environment before ids reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionsPath origin program context evidence source environment before ids ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

theorem prior_expressionPost {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : ReachedExpressionExtendedFaultPaths.model_expressionPost checked functions registry program context
      evidence source environment before id reason after token mapping world store) :
    model_expressionPost checked functions registry program context evidence source environment before id reason
      after token mapping world store := by
  obtain ⟨origin, path, native, associated⟩ := post
  exact ⟨origin, .prior path, native, associated⟩

theorem prior_outcomePost {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {type : Ty} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : OutcomePost (ReachedExpressionExtendedFaultPaths.model_expressionPost checked functions registry)
      program context evidence source environment before id type outcome after value mapping world store) :
    OutcomePost (model_expressionPost checked functions registry) program context evidence source environment
      before id type outcome after value mapping world store := by
  cases outcome with
  | value _ => trivial
  | fault _ =>
    obtain ⟨token, same, retained⟩ := post
    exact ⟨token, same, prior_expressionPost retained⟩

theorem sequence_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SequenceJoins (model_expressionPost checked functions registry) (model_expressionsPost checked functions registry)
      program context evidence source where
  head := by
    intro environment before id ids reason after token mapping world store _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .head path, native, associated⟩
  tail := by
    intro environment before middle id ids value reason after token mapping world store firstSource _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .tail firstSource path, native, associated⟩

theorem composition_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    CompositionJoins (model_expressionPost checked functions registry) (model_expressionsPost checked functions registry)
      program context evidence source where
  expression := by
    intro environment before id middle child reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expression link path, native, associated⟩
  expressions := by
    intro environment before id ids reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expressions link path, native, associated⟩

theorem constructor_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    ScalarConstructorFaultPostContracts.Joins (model_expressionPost values.checked functions registry)
      (model_expressionsPost values.checked functions registry) values program context evidence source where
  arguments := by
    intro id node instantiation ids tag header codes environment before reason after token mapping world store
      receipt form valid count nodes failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .constructorArguments receipt form valid count nodes failed path, native, associated⟩

theorem member_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    ScalarMemberFaultPostContracts.Joins (model_expressionPost values.checked functions registry)
      values program context evidence source where
  base := by
    intro id node child childNode name index identity branches result childType
      environment before reason after token mapping world store metadata baseMetadata form layout failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .memberBase metadata baseMetadata form layout failed path, native, associated⟩

theorem index_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    IndexFaultPostContracts.IndexJoins (model_expressionPost values.checked functions registry)
      values program context evidence source where
  base := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before after reason token mapping world store failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .indexSelected (.base header keyFound form sourceType) failed path, native, associated⟩
  key := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before middle after baseSource reason token mapping world store baseTrace failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .indexSelected (.key header keyFound form sourceType baseTrace) failed path, native, associated⟩

end Solcore.SourceSemantics.CoreLowering.ReachedScalarExpressionFaultPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedBuiltinExpressionFaultPaths
/-! A builtin path carries the same primitive packet through authentic parent
receipts. Ordinary links are reused; no Source or native trace is traversed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedBuiltinExpressionFaultPaths
open Core Frontend SourceInference GeneralHeap CompatiblePayload ExpressionFailurePostContracts
open ReachedExpressionFaultOrigins (PrimitiveOrigin NativeTransport)
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)

open ReachedScalarExpressionFaultPaths (IndexParentLink)

mutual
  inductive ExpressionPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
    | prior {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId}
        (path : ReachedScalarExpressionFaultPaths.ExpressionPath origin program context evidence source environment before id) :
        ExpressionPath origin program context evidence source environment before id
    | indexSelected {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id childId : ExpressionId}
        (link : IndexParentLink program context evidence source environment before id middle childId)
        (failed : Dynamic.ExpressionFaults program context evidence source environment middle childId reason heap)
        (child : ExpressionPath origin program context evidence source environment middle childId) :
        ExpressionPath origin program context evidence source environment before id
    | constructorArguments {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context}
        {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
        {ids : List ExpressionId} {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
        (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
        (form : node.form = .constructor instantiation ids)
        (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
        (count : ids.length = instantiation.payloadTypes.length)
        (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
        (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason heap)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id
    | builtinArguments {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context}
        {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
        {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
        {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
        (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
        (form : node.form = .call callee ids (.builtinFunction function))
        (sourceType : node.type = function.returnType)
        (compiledChildren : DataExpressionSequence.Tree source certificate scope ids function.parameterTypes codes)
        (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
        (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason heap)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id
    | memberBase {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context}
        {id base : ExpressionId} {node baseNode : ExpressionNode} {name : String} {index : Nat}
        {identity : DataTypeId} {branches : List Expr} {result childType : Ty}
        (metadata : CompatibleExpressionReads.Metadata values.checked source id node result)
        (baseMetadata : CompatibleExpressionReads.Metadata values.checked source base baseNode childType)
        (form : node.form = .member base name index)
        (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence)
          baseNode.type node.type index identity branches result)
        (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason heap)
        (child : ExpressionPath origin program context evidence source environment before base) :
        ExpressionPath origin program context evidence source environment before id
    | expression {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id childId : ExpressionId}
        (link : ExpressionLink program context evidence source environment before id middle childId)
        (child : ExpressionPath origin program context evidence source environment middle childId) :
        ExpressionPath origin program context evidence source environment before id
    | expressions {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
        (link : ExpressionsLink source id ids)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id

  inductive ExpressionsPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → List ExpressionId → Prop where
    | prior {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {ids : List ExpressionId}
        (path : ReachedScalarExpressionFaultPaths.ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionsPath origin program context evidence source environment before ids
    | head {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
        (child : ExpressionPath origin program context evidence source environment before id) :
        ExpressionsPath origin program context evidence source environment before (id :: ids)
    | tail {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId} {value : Dynamic.Value}
        (head : Dynamic.ExpressionEvaluates program context evidence source environment before id value middle)
        (child : ExpressionsPath origin program context evidence source environment middle ids) :
        ExpressionsPath origin program context evidence source environment before (id :: ids)
end

def model_expressionPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionFaultPost :=
  fun program context evidence source environment before id reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionPath origin program context evidence source environment before id ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

def model_expressionsPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionsFaultPost :=
  fun program context evidence source environment before ids reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionsPath origin program context evidence source environment before ids ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

theorem prior_expressionPost {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : ReachedScalarExpressionFaultPaths.model_expressionPost checked functions registry program context
      evidence source environment before id reason after token mapping world store) :
    model_expressionPost checked functions registry program context evidence source environment before id reason
      after token mapping world store := by
  obtain ⟨origin, path, native, associated⟩ := post
  exact ⟨origin, .prior path, native, associated⟩

theorem prior_outcomePost {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {type : Ty} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : OutcomePost (ReachedScalarExpressionFaultPaths.model_expressionPost checked functions registry)
      program context evidence source environment before id type outcome after value mapping world store) :
    OutcomePost (model_expressionPost checked functions registry) program context evidence source environment
      before id type outcome after value mapping world store := by
  cases outcome with
  | value _ => trivial
  | fault _ =>
    obtain ⟨token, same, retained⟩ := post
    exact ⟨token, same, prior_expressionPost retained⟩

theorem sequence_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SequenceJoins (model_expressionPost checked functions registry) (model_expressionsPost checked functions registry)
      program context evidence source where
  head := by
    intro environment before id ids reason after token mapping world store _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .head path, native, associated⟩
  tail := by
    intro environment before middle id ids value reason after token mapping world store firstSource _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .tail firstSource path, native, associated⟩

theorem composition_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    CompositionJoins (model_expressionPost checked functions registry) (model_expressionsPost checked functions registry)
      program context evidence source where
  expression := by
    intro environment before id middle child reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expression link path, native, associated⟩
  expressions := by
    intro environment before id ids reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expressions link path, native, associated⟩

theorem constructor_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    ScalarConstructorFaultPostContracts.Joins (model_expressionPost values.checked functions registry)
      (model_expressionsPost values.checked functions registry) values program context evidence source where
  arguments := by
    intro id node instantiation ids tag header codes environment before reason after token mapping world store
      receipt form valid count nodes failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .constructorArguments receipt form valid count nodes failed path, native, associated⟩

theorem member_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    ScalarMemberFaultPostContracts.Joins (model_expressionPost values.checked functions registry)
      values program context evidence source where
  base := by
    intro id node child childNode name index identity branches result childType
      environment before reason after token mapping world store metadata baseMetadata form layout failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .memberBase metadata baseMetadata form layout failed path, native, associated⟩

theorem index_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    IndexFaultPostContracts.IndexJoins (model_expressionPost values.checked functions registry)
      values program context evidence source where
  base := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before after reason token mapping world store failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .indexSelected (.base header keyFound form sourceType) failed path, native, associated⟩
  key := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before middle after baseSource reason token mapping world store baseTrace failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .indexSelected (.key header keyFound form sourceType baseTrace) failed path, native, associated⟩


theorem builtin_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    BuiltinFaultPostContracts.Joins (model_expressionPost values.checked functions registry)
      (model_expressionsPost values.checked functions registry) values program context evidence source where
  arguments := by
    intro certificate scope id callee ids function node codes environment before reason after token mapping world store
      metadata form sourceType compiledChildren nativeTypes failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .builtinArguments metadata form sourceType compiledChildren nativeTypes failed path, native, associated⟩

end Solcore.SourceSemantics.CoreLowering.ReachedBuiltinExpressionFaultPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedNamedLexicalBodyFaultPaths
/-! The flow path is produced at the original lexical joins. A body packet
retains that same flow fault and native body completion at the body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedLexicalBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open NamedLexicalFlowFaultPostContracts NamedLexicalFunctionFaultPostContracts

abbrev BodyPath (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (reason : Dynamic.SemanticFault)
    (after : Dynamic.Heap) (token : Word) (mapping : LocationMap) (world : StoreTyping) (store : Store) :=
  FlowOrigin post program function.evidence function.source context environment before true function.body
    reason after token mapping world store

/-- Lexical finish retains the original child post, including callable
children, at the same actual body store. -/
def bodyPost (post : ExpressionFailurePostContracts.ExpressionFaultPost) :
    NamedInvocationFaultPostContracts.BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ sourceSize finalContext type,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext (.fault reason) after ∧
      BodyPath post
        program function context environment before reason after token mapping world bodyStore ∧
      Evaluates actual initialStore body (.inLeft type (.word token)) bodyStore

def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    NamedInvocationFaultPostContracts.BodyFaultPost :=
  bodyPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry)

/-- The lexical exit and original finish evaluation preserve the same child
fault origin. No second flow or finish evaluation is constructed. -/
theorem outcome_post_of_finished_for
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {expressionSyntax : ExpressionId → Prop} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {type : Ty} {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {mapping : LocationMap} {world : StoreTyping} {bodyStore initialStore : Store} {actual : Environment} {body : Expr}
    (syntaxTree : GenericLexicalStatements.Syntax function.source expressionSyntax context true function.body function.resultType)
    (unique : NodeOccurrencesUnique function.source)
    (retained : FinishedPost (FlowPost post)
      program function context environment before size type outcome after value mapping world bodyStore)
    (evaluated : Evaluates actual initialStore body value bodyStore) :
    NamedInvocationFaultPostContracts.OutcomePost (bodyPost post) program function context
      environment before actual initialStore body type outcome after value mapping world bodyStore := by
  cases outcome with
  | value sourceValue => trivial
  | fault reason =>
    obtain ⟨finalContext, control, trace, exit, origin⟩ := retained
    cases exit with
    | fault =>
      obtain ⟨token, same, path⟩ := origin
      exact ⟨token, same, size, finalContext, type, trace, path, same ▸ evaluated⟩
    | breaking next =>
      cases trace with
      | control executed => cases GenericLexicalStatements.syntax_control_shape syntaxTree unique executed.sound
    | continuing next =>
      cases trace with
      | control executed => cases GenericLexicalStatements.syntax_control_shape syntaxTree unique executed.sound

/-- The retained actual flow and exit select the same fault. Successful lexical
syntax excludes direct transfers; it supplies no primitive fault origin. -/
theorem outcome_post_of_finished {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {expressionSyntax : ExpressionId → Prop} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {type : Ty} {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {mapping : LocationMap} {world : StoreTyping} {bodyStore initialStore : Store} {actual : Environment} {body : Expr}
    (syntaxTree : GenericLexicalStatements.Syntax function.source expressionSyntax context true function.body function.resultType)
    (unique : NodeOccurrencesUnique function.source)
    (retained : FinishedPost (FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry))
      program function context environment before size type outcome after value mapping world bodyStore)
    (evaluated : Evaluates actual initialStore body value bodyStore) :
    NamedInvocationFaultPostContracts.OutcomePost (model_bodyPost checked functions registry) program function context
      environment before actual initialStore body type outcome after value mapping world bodyStore := by
  exact outcome_post_of_finished_for syntaxTree unique retained evaluated

end Solcore.SourceSemantics.CoreLowering.ReachedNamedLexicalBodyFaultPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedLiteralOutcomePorts
/-! The existing literal meanings exclude faults at their real certificates.
Finite projections retain their values and add the vacuous success post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedLiteralOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
  {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
  (evidence : Dynamic.EvidenceEnvironment) {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {post : ExpressionFaultPost}

theorem preserves_of_fault_free
    (meaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate (fun _ _ => False)) :
    Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals agrees trace
  cases represented with
  | value related =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

theorem reflects_of_fault_free
    (meaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate (fun _ _ => False)) :
    Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals agrees evaluated
  cases represented with
  | value related =>
    exact ⟨_, after, finalMap, finalWorld, trace, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

theorem preserves_with_evidence
    (receipts : ∀ scope id lowered, certificate scope id lowered →
      ∃ node, source.lookupExpression? id = some node ∧
        CompatibleExpressionLiterals.Literal solved node lowered.type lowered.expression ∧
        CompatibleExpressionLiterals.NumericEvidence context evidence node)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post :=
  preserves_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.preserves_with_evidence functions program context evidence
      receipts unique (fun _ _ => False))

theorem reflects_with_evidence
    (receipts : ∀ scope id lowered, certificate scope id lowered →
      ∃ node, source.lookupExpression? id = some node ∧
        CompatibleExpressionLiterals.Literal solved node lowered.type lowered.expression ∧
        CompatibleExpressionLiterals.NumericEvidence context evidence node) :
    Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post :=
  reflects_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.reflects_with_evidence functions program context evidence source
      receipts (fun _ _ => False))

theorem preserves (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => CompatibleExpressionLiterals.Certificate solved source id lowered)
      faults post :=
  preserves_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique (fun _ _ => False))

theorem reflects (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) :
    Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => CompatibleExpressionLiterals.Certificate solved source id lowered)
      faults post :=
  reflects_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source (fun _ _ => False))

end Solcore.SourceSemantics.CoreLowering.ReachedLiteralOutcomePorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedScalarFragmentOutcomePorts
/-! The scalar fragment derives its literal and reached read providers
internally. The existing index core receives that same richer path family. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedScalarFragmentOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

include extension in
theorem read_preserves
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedLoweredReadOutcomePorts.lowered_read_preserves_with_post functions extension program context evidence
      reasonAt policies unique generated found environments heaps locals agrees trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem read_reflects
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedLoweredReadOutcomePorts.lowered_read_reflects_with_post functions extension program context evidence
      reasonAt policies unique generated found environments heaps locals agrees evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem members_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionMembers.preserves_with_literals_and_post functions extension program evidence unique
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (read_preserves functions extension program evidence policies unique) ⟨tree, tree.literalSites⟩

include extension in
theorem members_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionMembers.reflects_with_literals_and_post functions extension program evidence
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (read_reflects functions extension program evidence policies unique) ⟨tree, tree.literalSites⟩

theorem scalar_terminal
    (policies : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt CompatibleExpressionIndices.SourceScalar faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, retained⟩ :=
    IndexFaultPostContracts.model_scalar_terminal functions registry program context evidence reasonAt policies
      header sourceType profile baseRep keyRep actualTyped heaps keyFound form baseTrace keyTrace
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem scalar_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) :=
  CompatibleExpressionIndices.preserves_with_post (functions := functions) (program := program)
    (evidence := evidence) (unique := unique)
    (ReachedLoweredReadOutcomePorts.typed_preserves_of_unrestricted
      (members_preserves functions extension program evidence valid reads unique))
    (scalar_terminal functions program evidence missing)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)

include extension in
theorem scalar_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) :=
  CompatibleExpressionIndices.reflects_with_post (functions := functions) (program := program)
    (evidence := evidence)
    (ReachedLoweredReadOutcomePorts.typed_reflects_of_unrestricted
      (members_reflects functions extension program evidence valid reads unique))
    (scalar_terminal functions program evidence missing)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)

end Solcore.SourceSemantics.CoreLowering.ReachedScalarFragmentOutcomePorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedRecursiveFragmentOutcomePorts
/-! Recursive support derives its literal, read and Members providers internally.
The same existing support induction retains the actual primitive fault path. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedRecursiveFragmentOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

include extension in
theorem recursive_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionRecursive.preserves_with_literals_and_post functions extension program evidence unique
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (ReachedScalarFragmentOutcomePorts.read_preserves functions extension program evidence policies unique)
    ⟨tree, tree.literalSites⟩

include extension in
theorem recursive_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionRecursive.reflects_with_literals_and_post functions extension program evidence
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (ReachedScalarFragmentOutcomePorts.read_reflects functions extension program evidence policies unique)
    ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.ReachedRecursiveFragmentOutcomePorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedGeneralFragmentOutcomePorts
/-! The General fragment obtains every primitive provider from the actual
read, proxy, Recursive and index certificates. The existing support fold carries
the same fault post through its ordered children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedGeneralFragmentOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

include extension in
/-- The original proxy meaning with a false fault relation excludes only the
actual impossible alternative. Its full value tuple is kept. -/
theorem proxy_preserves (unique : NodeOccurrencesUnique source) {post : ExpressionFaultPost} :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionProxies.preserves functions extension program context evidence unique
      (fun _ _ => False) generated found environments heaps locals agrees actualTyped trace
  cases represented with
  | value related =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

include extension in
/-- Proxy completion retains the original independent Source trace. No Source
uniqueness premise is added to the generic reflection core. -/
theorem proxy_reflects {post : ExpressionFaultPost} :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionProxies.reflects functions extension program context evidence
      (fun _ _ => False) generated found environments heaps locals agrees actualTyped evaluated
  cases represented with
  | value related =>
    exact ⟨_, after, finalMap, finalWorld, trace, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include faithful functionLeaves functionTypes in
theorem general_terminal
    (policies : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, retained⟩ :=
    IndexFaultPostContracts.model_general_terminal functions registry program context evidence reasonAt
      faithful functionLeaves functionTypes policies header sourceType profile baseRep keyRep
      actualTyped heaps keyFound form baseTrace keyTrace
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension faithful functionLeaves functionTypes in
theorem general_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionGeneral.preserves_with_literals_and_post functions extension program evidence unique
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (ReachedScalarFragmentOutcomePorts.read_preserves functions extension program evidence reads unique)
    (proxy_preserves functions extension program evidence unique)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes in
theorem general_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionGeneral.reflects_with_literals_and_post functions extension program evidence
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (ReachedScalarFragmentOutcomePorts.read_reflects functions extension program evidence reads unique)
    (proxy_reflects functions extension program evidence)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.ReachedGeneralFragmentOutcomePorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedBuiltinFragmentOutcomePorts
/-! Builtin fragment providers retain the same reached primitive packet through
ordered argument faults. Literal, read, proxy and terminal providers come from
their genuine existing certificates; the support core is used once. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedBuiltinFragmentOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

include extension in
theorem read_preserves
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedScalarFragmentOutcomePorts.read_preserves functions extension program evidence policies unique generated found environments heaps locals agrees trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedBuiltinExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem read_reflects
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedScalarFragmentOutcomePorts.read_reflects functions extension program evidence policies unique generated found environments heaps locals agrees evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedBuiltinExpressionFaultPaths.prior_outcomePost retained⟩

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include faithful functionLeaves functionTypes in
theorem general_terminal
    (policies : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, retained⟩ :=
    ReachedGeneralFragmentOutcomePorts.general_terminal functions program evidence faithful functionLeaves functionTypes policies
      header sourceType profile baseRep keyRep actualTyped heaps keyFound form baseTrace keyTrace
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, ReachedBuiltinExpressionFaultPaths.prior_outcomePost retained⟩

include extension faithful functionLeaves functionTypes in
theorem builtin_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionBuiltins.preserves_with_literals_and_post functions extension functionLeaves program evidence unique
    (ReachedBuiltinExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.builtin_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (read_preserves functions extension program evidence reads unique)
    (ReachedGeneralFragmentOutcomePorts.proxy_preserves functions extension program evidence unique)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes in
theorem builtin_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionBuiltins.reflects_with_literals_and_post functions extension functionLeaves program evidence
    (ReachedBuiltinExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.builtin_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (read_reflects functions extension program evidence reads unique)
    (ReachedGeneralFragmentOutcomePorts.proxy_reflects functions extension program evidence)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.ReachedBuiltinFragmentOutcomePorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedNamedArgumentFaultPaths
/-! The named parent adds one genuine direct-argument edge to the original
builtin list path. The primitive leaf, model and native transport stay exact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedArgumentFaultPaths
open Core Frontend SourceInference GeneralHeap CompatiblePayload ExpressionFailurePostContracts
open ReachedExpressionFaultOrigins (PrimitiveOrigin NativeTransport)
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)

inductive ExpressionPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
    TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
  | arguments {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
      {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
      {before : Dynamic.Heap} {id callee : ExpressionId} {ids : List ExpressionId}
      {node calleeNode : ExpressionNode} {instantiation : DeclarationInstantiation} {name : String}
      (parent : ContainsExpression source id node)
      (form : node.form = .call callee ids (.declaration instantiation))
      (calleeContains : ContainsExpression source callee calleeNode)
      (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
      (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason heap)
      (children : ReachedBuiltinExpressionFaultPaths.ExpressionsPath origin program context evidence source environment before ids) :
      ExpressionPath origin program context evidence source environment before id

def model_expressionPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionFaultPost :=
  fun program context evidence source environment before id reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionPath origin program context evidence source environment before id ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

theorem arguments_join (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    NamedArgumentFaultPostContracts.ArgumentsJoin (model_expressionPost checked functions registry)
      (ReachedBuiltinExpressionFaultPaths.model_expressionsPost checked functions registry)
      program context evidence source where
  arguments := by
    intro id callee ids node calleeNode instantiation name environment before after reason token mapping world store
      parent form calleeContains calleeForm failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .arguments parent form calleeContains calleeForm failed path, native, associated⟩

end Solcore.SourceSemantics.CoreLowering.ReachedNamedArgumentFaultPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedNamedPrimitiveBodyFaultPaths
/-! A singleton function body adds one genuine Source edge to the actual
builtin expression path. Its native child and body completions keep the same
token and body store; caller restoration remains a separate receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedPrimitiveBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ReachedExpressionFaultOrigins
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)
open NamedInvocationFaultPostContracts

/-- These are the actual static singleton Source and emitted builtin fields. -/
structure SingletonAt (values : SourceCoreCompatibleValues.Context)
    (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (statement : StatementId) (node : StatementNode)
    (expression : ExpressionId) (expressionNode : ExpressionNode)
    (fuel : Nat) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (lowered : SourceCoreBasic.LoweredExpr) (body : Expr) (fellThrough escaped : Word) : Prop where
  statements : function.body = [statement]
  found : function.source.lookupStatement? statement = some node
  form : node.form = .expression expression false ∨ node.form = .returnStmt (some expression)
  expressionFound : function.source.lookupExpression? expression = some expressionNode
  expressionTyped : ExpressionHasType function.source context expression expressionNode.type
  resultType : expressionNode.type = function.resultType
  tree : CompatibleExpressionBuiltins.Tree fuel values function.source context solved reasonAt scope expression lowered
  projection : values.checked.catalog.project function.resultType = .ok lowered.type
  emitted : body = CompatibleStatements.finish lowered.type
    (LocalLoop.returnValue lowered.type lowered.expression) fellThrough escaped

/-- The leaf remains indexed by its actual final Source heap and reason. -/
inductive BodyPath : {after : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin after reason token → Program → Dynamic.Closure → SourceSemantics.Context →
    Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
  | tail {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
      (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .expression expression false)
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
        function.source environment before expression) :
      BodyPath origin program function context environment before expression
  | returning {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
      (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .returnStmt (some expression))
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
        function.source environment before expression) :
      BodyPath origin program function context environment before expression

/-- This projection constructs the real function fault directly from its child. -/
theorem BodyPath.source_fault {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap} {expression : ExpressionId}
    (path : BodyPath origin program function context environment before expression) :
    Dynamic.FunctionStatementsFault program context function.evidence function.source
      environment before function.body context reason after := by
  cases path with
  | tail body contains form failed _ =>
    rw [body]
    exact .tailExpression contains form failed
  | returning body contains form failed _ =>
    rw [body]
    exact .singleton (.returnValue contains form failed)

/-- Static emission and both actual evaluations associate the selected Source
child with the same body completion. The original model is fixed throughout. -/
def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) : BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ origin : PrimitiveOrigin after reason token,
      ∃ scope statement node expression expressionNode fuel solved reasonAt lowered sourceBody fellThrough escaped ξ,
        SingletonAt (.initial checked) function context scope statement node expression expressionNode fuel solved reasonAt
          lowered sourceBody fellThrough escaped ∧
        body = sourceBody.rename ξ ∧
        BodyPath origin program function context environment before expression ∧
        NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin ∧
        Evaluates actual initialStore (lowered.expression.rename ξ)
          (.inLeft lowered.type (.word token)) bodyStore ∧
        Evaluates actual initialStore body (.inLeft lowered.type (.word token)) bodyStore

/-- The same actual child packet supplies the singleton path and native link. -/
theorem model_bodyPost.of_child {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode}
    {expression : ExpressionId} {expressionNode : ExpressionNode} {fuel : Nat}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {sourceBody : Expr} {fellThrough escaped : Word}
    {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
    (singleton : SingletonAt (.initial checked) function context scope statement node expression expressionNode
      fuel solved reasonAt lowered sourceBody fellThrough escaped)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment before expression reason after token mapping world bodyStore)
    (child : Evaluates actual initialStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft lowered.type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore
      (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  refine ⟨origin, scope, statement, node, expression, expressionNode, fuel, solved, reasonAt,
    lowered, sourceBody, fellThrough, escaped, ξ, singleton, rfl, ?_, transported, model, child, completed⟩
  rcases singleton.form with tail | returning
  · exact .tail singleton.statements (lookupStatement?_sound singleton.found) tail failed path
  · exact .returning singleton.statements (lookupStatement?_sound singleton.found) returning failed path

end Solcore.SourceSemantics.CoreLowering.ReachedNamedPrimitiveBodyFaultPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedNamedSequentialBodyFaultPaths
/-! A discard prefix and the literal singleton suffix retain one actual causal
leaf. Source/native prefix receipts name the same reached heap and body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedSequentialBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ReachedExpressionFaultOrigins
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)
open NamedInvocationFaultPostContracts
open ReachedNamedPrimitiveBodyFaultPaths (SingletonAt BodyPath)

def suffix (function : Dynamic.Closure) (statement : StatementId) : Dynamic.Closure :=
  {function with body := [statement]}

/-- Both actual compiler children and the exact main emission are static receipts. -/
structure SequentialAt (values : SourceCoreCompatibleValues.Context)
    (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (statement : StatementId) (node : StatementNode)
    (expression : ExpressionId) (expressionNode : ExpressionNode) (fuel : Nat)
    (last : StatementId) (lastNode : StatementNode) (lastExpression : ExpressionId)
    (lastExpressionNode : ExpressionNode) (lastFuel : Nat) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (lowered lastLowered : SourceCoreBasic.LoweredExpr)
    (body : Expr) (fellThrough escaped : Word) : Prop where
  statements : function.body = [statement, last]
  found : function.source.lookupStatement? statement = some node
  form : node.form = .expression expression true
  expressionFound : function.source.lookupExpression? expression = some expressionNode
  expressionTyped : ExpressionHasType function.source context expression expressionNode.type
  tree : CompatibleExpressionBuiltins.Tree fuel values function.source context solved reasonAt scope expression lowered
  final : SingletonAt values (suffix function last) context scope last lastNode lastExpression lastExpressionNode
    lastFuel solved reasonAt lastLowered
    (CompatibleStatements.finish lastLowered.type (LocalLoop.returnValue lastLowered.type lastLowered.expression)
      fellThrough escaped) fellThrough escaped
  emitted : body = CompatibleStatements.finish lastLowered.type
    (LocalSequence.discard (LocalLoop.controlType lastLowered.type) lowered.expression
      (LocalLoop.returnValue lastLowered.type lastLowered.expression)) fellThrough escaped

/-- The successful Source prefix and the singleton leaf share their actual middle heap. -/
inductive SequentialPath : {after : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin after reason token → Program → Dynamic.Closure → SourceSemantics.Context →
    Dynamic.Environment → Dynamic.Heap → Prop where
  | head {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement last : StatementId} {node : StatementNode} {expression : ExpressionId}
      (body : function.body = [statement, last]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .expression expression true)
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
        function.source environment before expression) :
      SequentialPath origin program function context environment before
  | tail {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before middle : Dynamic.Heap}
      {statement last : StatementId} {node : StatementNode} {expression lastExpression : ExpressionId}
      {value : Dynamic.Value}
      (body : function.body = [statement, last]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .expression expression true)
      (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression value middle)
      (child : BodyPath origin program (suffix function last) context environment middle lastExpression) :
      SequentialPath origin program function context environment before

theorem SequentialPath.source_fault {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (path : SequentialPath origin program function context environment before) :
    Dynamic.FunctionStatementsFault program context function.evidence function.source
      environment before function.body context reason after := by
  cases path with
  | head body contains form failed _ =>
    rw [body]
    exact .head (.expression contains form failed)
  | tail body contains form first child =>
    rw [body]
    exact .tail (.expression contains form first) child.source_fault

/-- The exact child evaluations retain native sequencing beside the real Source path. -/
def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) : BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ origin : PrimitiveOrigin after reason token,
      ∃ scope statement node expression expressionNode fuel last lastNode lastExpression lastExpressionNode lastFuel
        solved reasonAt lowered lastLowered sourceBody fellThrough escaped ξ,
        SequentialAt (.initial checked) function context scope statement node expression expressionNode fuel
          last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered
          sourceBody fellThrough escaped ∧
        body = sourceBody.rename ξ ∧
        NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin ∧
        ((Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after ∧
          ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
            function.source environment before expression ∧
          Evaluates actual initialStore (lowered.expression.rename ξ)
            (.inLeft lowered.type (.word token)) bodyStore) ∨
          ∃ middle sourceValue payload middleStore initialMap initialWorld middleMap middleWorld,
            Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression sourceValue middle ∧
            BodyPath origin program (suffix function last) context environment middle lastExpression ∧
            Evaluates actual initialStore (lowered.expression.rename ξ) (.inRight .word payload) middleStore ∧
            CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore ∧
            LocationMap.Extends initialMap middleMap ∧ WorldExtends initialWorld middleWorld ∧
            AdministrativePreserved initialMap initialStore middleMap middleStore ∧ Dynamic.HeapMetadataExtend before middle ∧
            LocationMap.Extends middleMap mapping ∧ WorldExtends middleWorld world ∧
            AdministrativePreserved middleMap middleStore mapping bodyStore ∧ Dynamic.HeapMetadataExtend middle after ∧
            Evaluates (payload :: actual) middleStore
              (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))
              (.inLeft lastLowered.type (.word token)) bodyStore) ∧
        Evaluates actual initialStore body (.inLeft lastLowered.type (.word token)) bodyStore

section Constructors
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {scope : SourceCoreLocalCell.Scope} {statement last : StatementId} {node lastNode : StatementNode}
  {expression lastExpression : ExpressionId} {expressionNode lastExpressionNode : ExpressionNode}
  {fuel lastFuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {lowered lastLowered : SourceCoreBasic.LoweredExpr} {sourceBody : Expr} {fellThrough escaped : Word}
  {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
  {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
  (sequential : SequentialAt (.initial checked) function context scope statement node expression expressionNode fuel
    last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered sourceBody fellThrough escaped)

include sequential in
theorem model_bodyPost.of_head
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment before expression reason after token mapping world bodyStore)
    (child : Evaluates actual initialStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore
      (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  exact ⟨origin, scope, statement, node, expression, expressionNode, fuel, last, lastNode,
    lastExpression, lastExpressionNode, lastFuel, solved, reasonAt, lowered, lastLowered, sourceBody,
    fellThrough, escaped, ξ, sequential, rfl,
    transported, model, Or.inl ⟨failed, path, child⟩, completed⟩

include sequential in
theorem model_bodyPost.of_tail {middle : Dynamic.Heap} {sourceValue : Dynamic.Value} {payload : Value}
    {middleStore : Store} {initialMap middleMap : LocationMap} {initialWorld middleWorld : StoreTyping}
    (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression sourceValue middle)
    (firstNative : Evaluates actual initialStore (lowered.expression.rename ξ) (.inRight .word payload) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore)
    (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap mapping) (worlds : WorldExtends middleWorld world)
    (frame : AdministrativePreserved middleMap middleStore mapping bodyStore)
    (metadata : Dynamic.HeapMetadataExtend middle after)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle lastExpression reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment middle lastExpression reason after token mapping world bodyStore)
    (child : Evaluates (payload :: actual) middleStore
      (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))
      (.inLeft lastLowered.type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore
      (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  have lastPath : BodyPath origin program (suffix function last) context environment middle lastExpression := by
    rcases sequential.final.form with tail | returning
    · exact .tail rfl (lookupStatement?_sound sequential.final.found) tail failed path
    · exact .returning rfl (lookupStatement?_sound sequential.final.found) returning failed path
  exact ⟨origin, scope, statement, node, expression, expressionNode, fuel, last, lastNode,
    lastExpression, lastExpressionNode, lastFuel, solved, reasonAt, lowered, lastLowered, sourceBody,
    fellThrough, escaped, ξ, sequential, rfl,
    transported, model, Or.inr ⟨middle, sourceValue, payload, middleStore, initialMap, initialWorld,
      middleMap, middleWorld, first, lastPath, firstNative, middleHeaps, firstMaps, firstWorlds, firstFrame,
      firstMetadata, maps, worlds, frame, metadata, child⟩, completed⟩
end Constructors

/-- Finite projection exposes the same coupled leaf; it performs no Source fault traversal. -/
theorem model_bodyPost.source_path {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {actual : Environment} {initialStore bodyStore : Store} {body : Expr}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
    (post : model_bodyPost checked functions registry program function context environment before actual initialStore
      body reason after token mapping world bodyStore) :
    ∃ origin : PrimitiveOrigin after reason token,
      SequentialPath origin program function context environment before ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin := by
  obtain ⟨origin, scope, statement, node, expression, expressionNode, fuel, last, lastNode,
    lastExpression, lastExpressionNode, lastFuel, solved, reasonAt, lowered, lastLowered, sourceBody,
    fellThrough, escaped, ξ, sequential, _sameBody, transported, model, route, _completed⟩ := post
  refine ⟨origin, ?_, transported, model⟩
  rcases route with ⟨failed, path, _child⟩ | tail
  · exact .head sequential.statements (lookupStatement?_sound sequential.found) sequential.form failed path
  · obtain ⟨middle, sourceValue, payload, middleStore, initialMap, initialWorld, middleMap, middleWorld,
      first, path, _firstNative, _middleHeaps, _firstMaps, _firstWorlds, _firstFrame, _firstMetadata,
      _maps, _worlds, _frame, _metadata, _child⟩ := tail
    exact .tail sequential.statements (lookupStatement?_sound sequential.found) sequential.form first path

end Solcore.SourceSemantics.CoreLowering.ReachedNamedSequentialBodyFaultPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedNamedConditionalBodyFaultPaths
/-! A literal conditional with two explicit return branches keeps the actual
condition or selected branch fault, its reached heap, and the same body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedConditionalBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ReachedExpressionFaultOrigins
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)
open NamedInvocationFaultPostContracts

/-- The exact loop compiler envelope includes its real empty suffix. -/
structure ConditionalAt (values : SourceCoreCompatibleValues.Context)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (statement : StatementId) (node : StatementNode) (condition : ExpressionId) (conditionNode : ExpressionNode)
    (conditionFuel : Nat) (branch : Bool → StatementId) (branchNode : Bool → StatementNode)
    (expression : Bool → ExpressionId) (expressionNode : Bool → ExpressionNode) (fuel : Bool → Nat)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (conditionCode : Expr) (code : Bool → Expr) (type : Ty) (body : Expr) (fellThrough escaped : Word) : Prop where
  statements : function.body = [statement]
  found : function.source.lookupStatement? statement = some node
  form : node.form = .ifThen condition [branch true] (some [branch false])
  conditionFound : function.source.lookupExpression? condition = some conditionNode
  conditionTyped : ExpressionHasType function.source context condition conditionNode.type
  conditionType : conditionNode.type = .bool
  conditionTree : CompatibleExpressionBuiltins.Tree conditionFuel values function.source context solved reasonAt scope condition ⟨.bool, conditionCode⟩
  branchFound : ∀ b, function.source.lookupStatement? (branch b) = some (branchNode b)
  branchForm : ∀ b, (branchNode b).form = .returnStmt (some (expression b))
  expressionFound : ∀ b, function.source.lookupExpression? (expression b) = some (expressionNode b)
  expressionTyped : ∀ b, ExpressionHasType function.source context (expression b) (expressionNode b).type
  resultType : ∀ b, (expressionNode b).type = function.resultType
  tree : ∀ b, CompatibleExpressionBuiltins.Tree (fuel b) values function.source context solved reasonAt scope (expression b) ⟨type, code b⟩
  projection : values.checked.catalog.project function.resultType = .ok type
  emitted : body = CompatibleStatements.finish type
    (LocalLoop.sequence type
      (LocalLoop.conditional type conditionCode (LocalLoop.returnValue type (code true)) (LocalLoop.returnValue type (code false)))
      (LocalLoop.fallthrough type)) fellThrough escaped

/-- The selected Source edge is constructed at its actual middle heap. -/
inductive ConditionalPath : {after : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin after reason token → Program → Dynamic.Closure → SourceSemantics.Context →
    Dynamic.Environment → Dynamic.Heap → Prop where
  | condition {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId} {thenStmt elseStmt : StatementId}
      (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .ifThen condition [thenStmt] (some [elseStmt]))
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before condition reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment before condition) :
      ConditionalPath origin program function context environment before
  | branch {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before middle : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId}
      {branch : Bool → StatementId} {branchNode : Bool → StatementNode} {expression : Bool → ExpressionId}
      (boolean : Bool) (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .ifThen condition [branch true] (some [branch false]))
      (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
      (branchContains : ContainsStatement function.source (branch boolean) (branchNode boolean))
      (branchForm : (branchNode boolean).form = .returnStmt (some (expression boolean)))
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle (expression boolean) reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment middle (expression boolean)) :
      ConditionalPath origin program function context environment before

theorem ConditionalPath.source_fault {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (path : ConditionalPath origin program function context environment before) :
    Dynamic.FunctionStatementsFault program context function.evidence function.source environment before function.body context reason after := by
  cases path with
  | condition body contains form failed _ =>
    rw [body]
    exact .singleton (.ifCondition contains form failed)
  | branch boolean body contains form first branchContains branchForm failed _ =>
    rw [body]
    cases boolean with
    | false => exact .singleton (.ifFalseBody contains form first (.head (.returnValue branchContains branchForm failed)))
    | true => exact .singleton (.ifTrueBody contains form first (.head (.returnValue branchContains branchForm failed)))

/-- Native route fields retain both actual evaluations and real prefix effects. -/
inductive Route {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    (origin : PrimitiveOrigin after reason token) (program : Program) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (expression : Bool → ExpressionId) (conditionCode : Expr) (code : Bool → Expr)
    (type : Ty) (actual : Environment) (initialStore bodyStore : Store) (ξ : Renaming)
    (mapping : LocationMap) (world : StoreTyping) : Prop where
  | condition
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before condition reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment before condition)
      (evaluated : Evaluates actual initialStore (conditionCode.rename ξ) (.inLeft .bool (.word token)) bodyStore) :
      Route functions registry origin program function context environment before condition expression conditionCode code type actual initialStore bodyStore ξ mapping world
  | branch {middle : Dynamic.Heap} {middleStore : Store} {initialMap middleMap : LocationMap} {initialWorld middleWorld : StoreTyping}
      (boolean : Bool)
      (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
      (firstNative : Evaluates actual initialStore (conditionCode.rename ξ) (.inRight .word (.bool boolean)) middleStore)
      (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
      (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
      (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore) (firstMetadata : Dynamic.HeapMetadataExtend before middle)
      (maps : LocationMap.Extends middleMap mapping) (worlds : WorldExtends middleWorld world)
      (frame : AdministrativePreserved middleMap middleStore mapping bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle (expression boolean) reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment middle (expression boolean))
      (evaluated : Evaluates (.bool boolean :: actual) middleStore
        ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) (.inLeft type (.word token)) bodyStore) :
      Route functions registry origin program function context environment before condition expression conditionCode code type actual initialStore bodyStore ξ mapping world

/-- Literal compiler emission, selected causal route and full body evaluation stay coupled. -/
def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) : BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ origin : PrimitiveOrigin after reason token,
      ∃ scope statement node condition conditionNode conditionFuel branch branchNode expression expressionNode fuel
        solved reasonAt conditionCode code type sourceBody fellThrough escaped ξ,
        ConditionalAt (.initial checked) function context scope statement node condition conditionNode conditionFuel
          branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type sourceBody fellThrough escaped ∧
        body = sourceBody.rename ξ ∧
        NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin ∧
        Route functions registry origin program function context environment before condition expression conditionCode code type actual initialStore bodyStore ξ mapping world ∧
        Evaluates actual initialStore body (.inLeft type (.word token)) bodyStore

section Constructors
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode}
  {condition : ExpressionId} {conditionNode : ExpressionNode} {conditionFuel : Nat}
  {branch : Bool → StatementId} {branchNode : Bool → StatementNode} {expression : Bool → ExpressionId}
  {expressionNode : Bool → ExpressionNode} {fuel : Bool → Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {conditionCode : Expr} {code : Bool → Expr} {type : Ty}
  {sourceBody : Expr} {fellThrough escaped : Word} {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
  {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
  (conditional : ConditionalAt (.initial checked) function context scope statement node condition conditionNode conditionFuel
    branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type sourceBody fellThrough escaped)

include conditional in
theorem model_bodyPost.of_route
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment before condition reason after token mapping world bodyStore)
    (child : Evaluates actual initialStore (conditionCode.rename ξ) (.inLeft .bool (.word token)) bodyStore)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before condition reason after)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  exact ⟨origin, scope, statement, node, condition, conditionNode, conditionFuel, branch, branchNode, expression,
    expressionNode, fuel, solved, reasonAt, conditionCode, code, type, sourceBody, fellThrough, escaped, ξ,
    conditional, rfl, transported, model, .condition failed path child, completed⟩

include conditional in
theorem model_bodyPost.of_branch {middle : Dynamic.Heap} {middleStore : Store}
    {initialMap middleMap : LocationMap} {initialWorld middleWorld : StoreTyping} (boolean : Bool)
    (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
    (firstNative : Evaluates actual initialStore (conditionCode.rename ξ) (.inRight .word (.bool boolean)) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore) (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap mapping) (worlds : WorldExtends middleWorld world)
    (frame : AdministrativePreserved middleMap middleStore mapping bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle (expression boolean) reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment middle (expression boolean) reason after token mapping world bodyStore)
    (child : Evaluates (.bool boolean :: actual) middleStore ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) (.inLeft type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  exact ⟨origin, scope, statement, node, condition, conditionNode, conditionFuel, branch, branchNode, expression,
    expressionNode, fuel, solved, reasonAt, conditionCode, code, type, sourceBody, fellThrough, escaped, ξ,
    conditional, rfl, transported, model,
    .branch boolean first firstNative middleHeaps firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata failed path child, completed⟩
end Constructors

theorem model_bodyPost.source_path {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {actual : Environment} {initialStore bodyStore : Store} {body : Expr}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
    (post : model_bodyPost checked functions registry program function context environment before actual initialStore body reason after token mapping world bodyStore) :
    ∃ origin : PrimitiveOrigin after reason token,
      ConditionalPath origin program function context environment before ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin := by
  obtain ⟨origin, scope, statement, node, condition, conditionNode, conditionFuel, branch, branchNode, expression,
    expressionNode, fuel, solved, reasonAt, conditionCode, code, type, sourceBody, fellThrough, escaped, ξ,
    conditional, _sameBody, transported, model, route, _completed⟩ := post
  refine ⟨origin, ?_, transported, model⟩
  cases route with
  | condition failed path _ => exact .condition conditional.statements (lookupStatement?_sound conditional.found) conditional.form failed path
  | branch boolean first _ _ _ _ _ _ _ _ _ _ failed path _ =>
    exact .branch boolean conditional.statements (lookupStatement?_sound conditional.found) conditional.form first
      (lookupStatement?_sound (conditional.branchFound boolean)) (conditional.branchForm boolean) failed path

end Solcore.SourceSemantics.CoreLowering.ReachedNamedConditionalBodyFaultPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedIndexMeaningOutcomePorts
/-! Concrete finite terminal and Source joins are derived internally. The
fragment retains its genuine independent meaning until its original fold is
connected to the same reached post family. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedIndexMeaningOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts IndexFaultPostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

theorem scalar_preserves_with_reached_diagnostics
    (unique : NodeOccurrencesUnique source)
    (fragment : TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleExpressionIndices.preserves_with_post (functions := functions) (program := program)
    (evidence := evidence) (unique := unique) fragment
    (model_scalar_terminal functions registry program context evidence reasonAt policies)
    (model_index_joins functions registry program context evidence)

theorem scalar_reflects_with_reached_diagnostics
    (fragment : TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleExpressionIndices.reflects_with_post (functions := functions) (program := program)
    (evidence := evidence) fragment
    (model_scalar_terminal functions registry program context evidence reasonAt policies)
    (model_index_joins functions registry program context evidence)

theorem general_preserves_with_reached_diagnostics
    (unique : NodeOccurrencesUnique source)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (fragment : TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleGeneralIndex.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleGeneralIndex.preserves_with_post (functions := functions) (program := program)
    (evidence := evidence) (unique := unique) fragment
    (model_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes policies)
    (model_index_joins functions registry program context evidence)

theorem general_reflects_with_reached_diagnostics
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (fragment : TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleGeneralIndex.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleGeneralIndex.reflects_with_post (functions := functions) (program := program)
    (evidence := evidence) fragment
    (model_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes policies)
    (model_index_joins functions registry program context evidence)

end Solcore.SourceSemantics.CoreLowering.ReachedIndexMeaningOutcomePorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedIndexMissingDiagnosticObservations
/-! A reached unavailable mapping supplies the receiving metadata and canonical
mapping view from its own fields. Its exact specialization and issued reason
remain static provenance receipts; observations do not infer a whole public
execution or identify a restored store with the primitive store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedIndexMissingDiagnosticObservations
open Core Frontend SourceInference CompatiblePayload GeneralHeap
open ReachedExpressionFaultOrigins
open CompatiblePublicContextualMissingDiagnosticObservations
open CallableIndexedOwnedPublicFaultReceiverTables

/-- Literal source and reason associations at one actual specialized issuer. -/
def IssuerAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked))
    (owner : SourceSpecialization.SpecializationKey) (leaf : IndexLeaf) : Prop :=
  ∃ function, SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function ∧
    leaf.source = function.function.typedBody ∧
    leaf.reason = issued.program.reasonAt owner leaf.id

/-- The real base lookup and both raw runtime views are already in the leaf. -/
theorem IndexLeaf.mapping_view (leaf : IndexLeaf) (unique : NodeOccurrencesUnique leaf.source) :
    CanonicalMappingView leaf.source leaf.base leaf.rawKey leaf.rawValue := by
  refine ⟨leaf.baseNode, lookupExpression?_complete unique leaf.baseContains, ?_⟩
  rw [leaf.sourceType, SourceCoreRawMetadata.runtimeType, leaf.keyView, leaf.valueView]

/-- Transport the original mapping metadata only along the actual registry. -/
theorem IndexLeaf.receiving_metadata (leaf : IndexLeaf)
    {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends leaf.registry registry) :
    MetadataRep registry (.mapping leaf.rawKey leaf.rawValue) leaf.tag :=
  leaf.fields.metadata.extend extension

/-- The actual first receiving row decodes this primitive's literal token. -/
theorem IndexLeaf.table_diagnostic (leaf : IndexLeaf)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : CallableIndexedOwnedContextualDiagnosticSources.FactoryAt prepared issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt prepared issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source)
    {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends leaf.registry registry)
    {issuedExtension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry registry issuedExtension = .ok table) :
    table.diagnostic? (leaf.reason.add leaf.tag) = some {
      error := .typeMismatch leaf.rawValue none,
      site := .occurrence leaf.id.occurrence, span := some leaf.node.span } := by
  obtain ⟨function, record, sourceEq, reasonEq⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.node.id leaf.node := by
    rw [← sourceEq, leaf.contains.2]
    exact leaf.contains
  have view := sourceEq ▸ IndexLeaf.mapping_view leaf unique
  obtain ⟨missing, _member, _receipt, base, decoded⟩ :=
    FactoryAt.table_expression_missing_diagnostic factory record canonicalUnique contains leaf.form view rebuilt
      (IndexLeaf.receiving_metadata leaf extension)
  simpa only [base, leaf.contains.2, ← reasonEq] using decoded

/-- Actual public rebuilding and callable append retain the same origin token. -/
theorem IndexLeaf.public_diagnostic (leaf : IndexLeaf)
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt compiled.indexed.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source)
    (extension : SourceCoreRawMetadata.Extends leaf.registry completion.result.context.registry) :
    completion.result.diagnostics.diagnostic? (leaf.reason.add leaf.tag) = some {
      error := .typeMismatch leaf.rawValue none,
      site := .occurrence leaf.id.occurrence, span := some leaf.node.span } := by
  obtain ⟨function, record, sourceEq, reasonEq⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.node.id leaf.node := by
    rw [← sourceEq, leaf.contains.2]
    exact leaf.contains
  have view := sourceEq ▸ IndexLeaf.mapping_view leaf unique
  have decoded := receiver_index_missing_diagnostic compiled receiver present record canonicalUnique contains
    leaf.form view (IndexLeaf.receiving_metadata leaf extension)
  simpa only [leaf.contains.2, ← reasonEq] using decoded

/-- Session metadata comes from the same reached leaf and real extension. -/
theorem IndexLeaf.session_diagnostic (leaf : IndexLeaf)
    {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact)
    {rootKey : SourceSpecialization.SpecializationKey} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    {registry : SourceCoreRawMetadata.Registry} (registryAt : session.RegistryAt registry)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial _)}
    (present : artifact.program.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt artifact.program.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source)
    (extension : SourceCoreRawMetadata.Extends leaf.registry registry) :
    table.diagnostic? (leaf.reason.add leaf.tag) = some {
      error := .typeMismatch leaf.rawValue none,
      site := .occurrence leaf.id.occurrence, span := some leaf.node.span } := by
  obtain ⟨function, record, sourceEq, reasonEq⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.node.id leaf.node := by
    rw [← sourceEq, leaf.contains.2]
    exact leaf.contains
  have view := sourceEq ▸ IndexLeaf.mapping_view leaf unique
  obtain ⟨actual, actualPresent, decoded⟩ :=
    CompatibleSessionContextualMissingDiagnosticObservations.session_index_missing_observation session receiver
      registry registryAt present record canonicalUnique contains leaf.form view (IndexLeaf.receiving_metadata leaf extension)
  have same := Option.some.inj (actualPresent.symm.trans present)
  cases same
  simpa only [leaf.contains.2, ← reasonEq] using decoded

end Solcore.SourceSemantics.CoreLowering.ReachedIndexMissingDiagnosticObservations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedNamedInvocationFaultReceipts
/-! Finite projections of the same actual body receipt. The fault token is
unchanged by caller restoration; the body post remains at its original store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedInvocationFaultReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {post : BodyFaultPost}

section Body
variable {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location}
  {capturePrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  {entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost}
  {reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩} {size : Nat}

theorem source_body_forget (meaning : SourceBodyAtWithPost post (faults := faults) entry reached size) :
    SourceBodyAt (faults := faults) entry reached size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps,
    maps, worlds, frame, metadata, returned, _post⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps,
    maps, worlds, frame, metadata, returned⟩

theorem native_body_forget (meaning : NativeBodyAtWithPost post (faults := faults) entry reached size) :
    NativeBodyAt (faults := faults) entry reached size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps,
    maps, worlds, frame, metadata, returned, _post⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps,
    maps, worlds, frame, metadata, returned⟩
end Body

section Continuation
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {arguments : List Dynamic.Value}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}
  {budget : Nat}

theorem source_continuation_forget
    (meaning : SourceContinuationWithPost (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) (post := post) owner caller condition budget) :
    SourceContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical owned history emitted entry agreement reached related allowed child strict
  exact source_body_forget (meaning physical owned history emitted entry agreement reached related allowed child strict)

theorem native_continuation_forget
    (meaning : NativeContinuationWithPost (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) (post := post) owner caller condition budget) :
    NativeContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict
  exact native_body_forget (meaning physical owned history emitted prefixCompleted prefixWithin restored
    entry reached related allowed child strict)
end Continuation

section Returned
variable {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
  {arguments : List Dynamic.Value} {sourceParent : Nat} {nativeBudget : Option Nat}
  {after : Dynamic.Heap} {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}

/-- The same body word passes through the original frame restoration. No
primitive origin is inferred from the ordinary result relation. -/
theorem fault_word {reason : Dynamic.SemanticFault}
    (receipt : ReturnedAt (header := header) (functions := functions) (registry := registry)
      post sourceParent nativeBudget owner caller arguments (.fault reason) after value finalMap finalWorld finalStore) :
    ∃ token, value = .inLeft header.output (.word token) := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ, entry, parameterState,
    sourceSize, bodyStore, bodyState, owned, history, emitted, parameterRelated, bodyRelated,
    trace, smaller, evaluation, bodyPost, measured, related, restored, cell, returnedRelated,
    callerRelated, records⟩ := receipt
  exact ⟨bodyPost.choose, bodyPost.choose_spec.1⟩

/-- The same retained receipt supplies a real restored pool and its unchanged
ordered records. The body post is still indexed by the pre-restoration store. -/
theorem restored_pool {outcome : Dynamic.ExpressionOutcome}
    (receipt : ReturnedAt (header := header) (functions := functions) (registry := registry)
      post sourceParent nativeBudget owner caller arguments outcome after value finalMap finalWorld finalStore) :
    ∃ (bodyScope : SourceCoreLocalCell.Scope) (bodyCanonical : Environment) (bodyStore : Store)
      (bodyState : State headers keys ⟨bodyScope, finalMap, finalWorld, after, bodyStore, bodyCanonical⟩),
      finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
        (body := ⟨bodyScope, finalMap, finalWorld, after, bodyStore, bodyCanonical⟩)).store ∧
      Relates bodyState (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      Relates caller (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      records (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) = records bodyState := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ, entry, parameterState,
    sourceSize, bodyStore, bodyState, owned, history, emitted, parameterRelated, bodyRelated,
    trace, smaller, evaluation, bodyPost, measured, related, restored, cell, returnedRelated,
    callerRelated, records⟩ := receipt
  exact ⟨_, entry.canonical, bodyStore, bodyState, restored, returnedRelated, callerRelated, records⟩
end Returned
end Solcore.SourceSemantics.CoreLowering.ReachedNamedInvocationFaultReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedNamedCallBodyFaultReceipts
/-! Finite projections retain the actual named call route. Argument failure
stays distinct from the body receipt, whose post remains at its body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedCallBodyFaultReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open NamedInvocationFaultPostContracts NamedCallBodyFaultPostContracts
open CallableIndexedOwnedExpressionHeads
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {codes : List SourceCoreBasic.LoweredExpr} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical actual : Environment} {ξ : Renaming}
  {slots : ProtectedStateTransition.Index → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol}
  {caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩}
  {post : BodyFaultPost}

section Providers
variable {callerPrefix : Nat}
  {namedBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}
  {budget : Nat}

/-- Forget only the strict child's sidecar, preserving its actual continuation. -/
theorem source_provider_forget
    (meaning : SourceInvocationsForWithPost (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) post budget) :
    SourceInvocationsFor (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) budget := by
  intro size arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    related maps worlds frame metadata capture represented heaps
  exact ReachedNamedInvocationFaultReceipts.source_continuation_forget
    (meaning evaluated argumentState related maps worlds frame metadata capture represented heaps)

/-- The reflected continuation retains its independent Source output grade. -/
theorem native_provider_forget
    (meaning : NativeInvocationsForWithPost (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) post budget) :
    NativeInvocationsFor (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) budget := by
  intro size arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    related maps worlds frame metadata capture represented heaps
  exact ReachedNamedInvocationFaultReceipts.native_continuation_forget
    (meaning evaluated argumentState related maps worlds frame metadata capture represented heaps)
end Providers

section Routes
variable {sourceParent : Nat} {nativeParent : Option Nat} {outcome : Dynamic.ExpressionOutcome}
  {after : Dynamic.Heap} {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}

/-- A finite route projection keeps the failed list or the same successful
argument pool and exact restored body receipt. It does not classify a fault
by its reason/token or manufacture a primitive origin for argument failure. -/
theorem argument_failure_or_body
    (route : CallRouteAt (functions := functions) (registry := registry) (header := header)
      (source := source) (context := context) (evidence := evidence) (environment := environment)
      (ids := ids) (codes := codes) (actual := actual) (ξ := ξ)
      post owner bridge caller sourceParent nativeParent outcome after value finalMap finalWorld finalStore) :
    (∃ child reason token,
      outcome = .fault reason ∧
      SourceExecutionSize.ExpressionsFault program child context evidence source environment before ids reason after ∧
      child < sourceParent ∧ value = .inLeft header.output (.word token) ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      CompletionBelow nativeParent actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore) ∨
    (∃ argumentsSize arguments middle middleMap middleWorld middleStore,
      ∃ argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩,
      ∃ bodySourceSize bodyNative,
      SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle ∧
      argumentsSize < sourceParent ∧ bodySourceSize < sourceParent ∧
      callerProtocol.Relates caller argumentState ∧ InvocationBelow nativeParent bodyNative ∧
      ReturnedAt (header := header) (functions := functions) (registry := registry)
        post bodySourceSize bodyNative owner (bridge.pool argumentState) arguments outcome after value finalMap finalWorld finalStore ∧
      ∃ finalState : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      Relates (bridge.pool argumentState) finalState ∧ bridge.pool returned = finalState ∧ callerProtocol.Relates caller returned) := by
  cases route with
  | argumentFailure failed smaller evaluation measured reached related =>
    exact .inl ⟨_, _, _, rfl, failed, smaller, rfl, evaluation, measured⟩
  | bodyApplied evaluated argumentsSmaller called callSmaller argumentEvaluation argumentMeasured
      argumentState argumentRelated argumentMaps argumentWorlds argumentFrame argumentMetadata capture represented heaps
      bodyTrace bodySmaller bodyEvaluation bodyNative bodyMeasured receipt finalState bodyRelated
      bodyMaps bodyWorlds bodyFrame bodyMetadata returned samePool relatedCaller =>
    exact .inr ⟨_, _, _, _, _, _, argumentState, _, bodyNative, evaluated, argumentsSmaller,
      Nat.lt_trans bodySmaller callSmaller, argumentRelated, bodyMeasured, receipt,
      finalState, returned, bodyRelated, samePool, relatedCaller⟩

/-- The actual word is retained by either real route. Body fault attribution
still belongs to its exact ReturnedAt receipt at bodyStore. -/
theorem fault_word {reason : Dynamic.SemanticFault}
    (route : CallRouteAt (functions := functions) (registry := registry) (header := header)
      (source := source) (context := context) (evidence := evidence) (environment := environment)
      (ids := ids) (codes := codes) (actual := actual) (ξ := ξ)
      post owner bridge caller sourceParent nativeParent (.fault reason) after value finalMap finalWorld finalStore) :
    ∃ token, value = .inLeft header.output (.word token) := by
  cases route with
  | argumentFailure failed smaller evaluation measured reached related => exact ⟨_, rfl⟩
  | bodyApplied evaluated argumentsSmaller called callSmaller argumentEvaluation argumentMeasured
      argumentState argumentRelated argumentMaps argumentWorlds argumentFrame argumentMetadata capture represented heaps
      bodyTrace bodySmaller bodyEvaluation bodyNative bodyMeasured receipt finalState bodyRelated
      bodyMaps bodyWorlds bodyFrame bodyMetadata returned samePool relatedCaller =>
    exact ReachedNamedInvocationFaultReceipts.fault_word receipt
end Routes
end Solcore.SourceSemantics.CoreLowering.ReachedNamedCallBodyFaultReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedReadFaultDiagnosticObservations
/-! A reached local read retains its literal binder and Source occurrence.
Actual issuer selection and table rebuilding supply the same diagnostic token.
Whole-program failure and restored heap associations remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedReadFaultDiagnosticObservations
open Core Frontend SourceInference
open ReachedExpressionFaultOrigins
open CallableIndexedOwnedPublicFaultReceiverTables

/-- The primitive uses the Source and token of the selected actual issuer.
The original prepared function row is kept as a genuine lookup receipt. -/
def IssuerAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked))
    (owner : SourceSpecialization.SpecializationKey) (leaf : ReadLeaf) : Prop :=
  ∃ function own, SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function ∧
    leaf.source = function.function.typedBody ∧
    leaf.reason = issued.program.reasonAt owner leaf.id ∧
    issued.program.base.find? owner = some own

/-- The Source occurrence follows from this actual read certificate. -/
theorem ReadLeaf.contains (leaf : ReadLeaf) :
    ContainsExpression leaf.source leaf.id leaf.certificate.node :=
  lookupExpression?_sound leaf.certificate.metadata.found

/-- The receiving public table decodes the actual primitive token. Binder and
span come from its certificate, rather than separate association assumptions. -/
theorem ReadLeaf.public_diagnostic (leaf : ReadLeaf)
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt compiled.indexed.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source) :
    completion.result.diagnostics.diagnostic? leaf.reason = some {
      error := .uninitializedLocal leaf.certificate.binder,
      site := .occurrence leaf.id.occurrence, span := some leaf.certificate.node.span } := by
  obtain ⟨function, own, record, sourceEq, reasonEq, ownFound⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.id leaf.certificate.node :=
    sourceEq ▸ ReadLeaf.contains leaf
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic
      compiled receiver present record canonicalUnique contains leaf.certificate.form ownFound
  simpa only [← token, ← reasonEq] using decoded

/-- The actual Session receiving table retains the same canonical read.
Its genuine registry and callable append are supplied by the existing receiver. -/
theorem ReadLeaf.session_diagnostic (leaf : ReadLeaf)
    {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact)
    {rootKey : SourceSpecialization.SpecializationKey} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial _)}
    (present : artifact.program.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt artifact.program.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source) :
    table.diagnostic? leaf.reason = some {
      error := .uninitializedLocal leaf.certificate.binder,
      site := .occurrence leaf.id.occurrence, span := some leaf.certificate.node.span } := by
  obtain ⟨function, own, record, sourceEq, reasonEq, ownFound⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.id leaf.certificate.node :=
    sourceEq ▸ ReadLeaf.contains leaf
  obtain ⟨registry, _registryAt, actual, read, actualPresent, _expression, _binder, _span,
      token, _member, decoded⟩ :=
    CompatibleSessionContextualDiagnosticObservations.session_read_observation session receiver
      (show CompatibleSessionContextualDiagnosticObservations.ReadInputs artifact.program owner from
        ⟨issued, own, present, ownFound⟩) record canonicalUnique contains leaf.certificate.form
  have same := Option.some.inj (actualPresent.symm.trans present)
  cases same
  simpa only [← token, ← reasonEq] using decoded

end Solcore.SourceSemantics.CoreLowering.ReachedReadFaultDiagnosticObservations
end
