import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning

/-! An interface for retaining an actual fault origin beside the
original result. Finite joins consume existing child posts and Source traces.
They do not produce evaluations or choose a primitive witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly

abbrev ExpressionFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

abbrev ExpressionsFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → List ExpressionId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

/-- Only an actual fault outcome requires a provenance post. -/
def OutcomePost (post : ExpressionFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : ExpressionId) (type : Core.Ty)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .value _ => True
  | .fault reason => ∃ token, result = .inLeft type (.word token) ∧
      post program context evidence source environment before id reason after token mapping world store

/-- This shape is independent of DataExpressionSequence and avoids an import cycle. -/
def ListOutcomePost (post : ExpressionsFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (ids : List ExpressionId) (type : Core.Ty)
    (outcome : Except Dynamic.SemanticFault (List Dynamic.Value)) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .ok _ => True
  | .error reason => ∃ token, result = .inLeft type (.word token) ∧
      post program context evidence source environment before ids reason after token mapping world store

/-- These are only the two original ordered Source fault joins. -/
structure SequenceJoins (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) : Prop where
  head : ∀ {environment before id ids reason after token mapping world store},
    Dynamic.ExpressionFaults program context evidence source environment before id reason after →
    expressionPost program context evidence source environment before id reason after token mapping world store →
    listPost program context evidence source environment before (id :: ids) reason after token mapping world store
  tail : ∀ {environment before middle id ids value reason after token mapping world store},
    Dynamic.ExpressionEvaluates program context evidence source environment before id value middle →
    Dynamic.ExpressionsFault program context evidence source environment middle ids reason after →
    listPost program context evidence source environment middle ids reason after token mapping world store →
    listPost program context evidence source environment before (id :: ids) reason after token mapping world store

/-- A genuine parent-to-selected-child Source join. The parent contains its
actual form and layout, and selected right/branch joins keep the actual prefix. -/
inductive ExpressionLink (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment) :
    Dynamic.Heap → ExpressionId → Dynamic.Heap → ExpressionId → Prop where
  | group {before : Dynamic.Heap} {id inner : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .group inner)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
      ExpressionLink program context evidence source environment before id before inner
  | unary {before : Dynamic.Heap} {id operand : ExpressionId} {node : ExpressionNode}
      {operator : Syntax.UnaryOp} {owned : List RequirementId}
      (contains : ContainsExpression source id node) (form : node.form = .unary operator operand)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned) :
      ExpressionLink program context evidence source environment before id before operand
  | binaryLeft {before : Dynamic.Heap} {id left right : ExpressionId} {node : ExpressionNode}
      {operator : Syntax.BinaryOp} {owned : List RequirementId}
      (contains : ContainsExpression source id node) (form : node.form = .binary left operator right)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned) :
      ExpressionLink program context evidence source environment before id before left
  | binaryRight {before middle : Dynamic.Heap} {id left right : ExpressionId} {node : ExpressionNode}
      {operator : Syntax.BinaryOp} {owned : List RequirementId} {value : Dynamic.Value}
      (contains : ContainsExpression source id node) (form : node.form = .binary left operator right)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned)
      (firstSource : Dynamic.ExpressionEvaluates program context evidence source environment before left value middle)
      (selected : Dynamic.EvaluatesRightOperand operator value) :
      ExpressionLink program context evidence source environment before id middle right
  | conditionalCondition {before : Dynamic.Heap} {id condition yes no : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .conditional condition yes no)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
      ExpressionLink program context evidence source environment before id before condition
  | conditionalTrue {before middle : Dynamic.Heap} {id condition yes no : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .conditional condition yes no)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
      (firstSource : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool true) middle) :
      ExpressionLink program context evidence source environment before id middle yes
  | conditionalFalse {before middle : Dynamic.Heap} {id condition yes no : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .conditional condition yes no)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
      (firstSource : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool false) middle) :
      ExpressionLink program context evidence source environment before id middle no

inductive ExpressionsLink (source : TypedSource) : ExpressionId → List ExpressionId → Prop where
  | tuple {id : ExpressionId} {ids : List ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .tuple ids)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
      ExpressionsLink source id ids

/-- Only finite post transport along those exact joins is requested. -/
structure CompositionJoins (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) : Prop where
  expression : ∀ {environment before id middle child reason after token mapping world store},
    ExpressionLink program context evidence source environment before id middle child →
    Dynamic.ExpressionFaults program context evidence source environment middle child reason after →
    expressionPost program context evidence source environment middle child reason after token mapping world store →
    expressionPost program context evidence source environment before id reason after token mapping world store
  expressions : ∀ {environment before id ids reason after token mapping world store},
    ExpressionsLink source id ids →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    expressionPost program context evidence source environment before id reason after token mapping world store

/-- The original untyped child contract with a fault-only post appended. -/
def Preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

/-- The original untyped completed-child contract, with the same appended post. -/
def Reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

/-- Inserted slots retain their original native runtime typing premise. -/
def TypedPreserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

/-- The typed completed-child contract retains the actual inserted-slot context. -/
def TypedReflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

abbrev TrivialExpressionPost : ExpressionFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True
abbrev TrivialExpressionsPost : ExpressionsFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True

theorem trivial_sequence_joins (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SequenceJoins TrivialExpressionPost TrivialExpressionsPost program context evidence source where
  head := by intros; trivial
  tail := by intros; trivial

theorem trivial_composition_joins (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    CompositionJoins TrivialExpressionPost TrivialExpressionsPost program context evidence source where
  expression := by intros; trivial
  expressions := by intros; trivial

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : FunctionCalls.FaultRep} {post : ExpressionFaultPost}

theorem OutcomePost.of_trivial {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {sourceType : TypeSystem.Ty} {type : Core.Ty} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type faults outcome value) :
    OutcomePost TrivialExpressionPost program context evidence source environment before id type
      outcome after value mapping world store := by
  cases represented with
  | value _ => trivial
  | fault _ => exact ⟨_, rfl, trivial⟩

theorem OutcomePost.fault {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {type : Core.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (retained : OutcomePost post program context evidence source environment before id type
      (.fault reason) after (.inLeft type (.word token)) mapping world store) :
    post program context evidence source environment before id reason after token mapping world store := by
  obtain ⟨actual, same, retained⟩ := retained
  have tokens : token = actual := by simpa only [Value.inLeft.injEq, Value.word.injEq, true_and] using same
  exact tokens.symm ▸ retained

/-- Finite transport of the actual selected child outcome through its owning Source form. -/
theorem OutcomePost.expression {listPost : ExpressionsFaultPost}
    (joins : CompositionJoins post listPost program context evidence source)
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id child : ExpressionId} {type : Core.Ty} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (link : ExpressionLink program context evidence source environment before id middle child)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment middle child outcome after)
    (retained : OutcomePost post program context evidence source environment middle child type
      outcome after value mapping world store) :
    OutcomePost post program context evidence source environment before id type
      outcome after value mapping world store := by
  cases trace with
  | value _ => trivial
  | fault failed =>
    obtain ⟨token, same, retained⟩ := retained
    exact ⟨token, same, joins.expression link failed retained⟩

theorem ListOutcomePost.fault {listPost : ExpressionsFaultPost}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {ids : List ExpressionId}
    {type : Core.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (retained : ListOutcomePost listPost program context evidence source environment before ids type
      (.error reason) after (.inLeft type (.word token)) mapping world store) :
    listPost program context evidence source environment before ids reason after token mapping world store := by
  obtain ⟨actual, same, retained⟩ := retained
  have tokens : token = actual := by simpa only [Value.inLeft.injEq, Value.word.injEq, true_and] using same
  exact tokens.symm ▸ retained

theorem Preserves.forget (meaning : Preserves model program context evidence source certificate faults post) :
    GenericExpressionMeaning.Preserves model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals layout trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem Reflects.forget (meaning : Reflects model program context evidence source certificate faults post) :
    GenericExpressionMeaning.Reflects model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem TypedPreserves.forget (meaning : TypedPreserves model program context evidence source certificate faults post) :
    TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals layout actualTyped trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout actualTyped trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem TypedReflects.forget (meaning : TypedReflects model program context evidence source certificate faults post) :
    TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals layout actualTyped evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem Preserves.of_trivial
    (meaning : GenericExpressionMeaning.Preserves model program context evidence source certificate faults) :
    Preserves model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals layout trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

theorem Reflects.of_trivial
    (meaning : GenericExpressionMeaning.Reflects model program context evidence source certificate faults) :
    Reflects model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

theorem TypedPreserves.of_trivial
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults) :
    TypedPreserves model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals layout actualTyped trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout actualTyped trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

theorem TypedReflects.of_trivial
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults) :
    TypedReflects model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals layout actualTyped evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

end Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
