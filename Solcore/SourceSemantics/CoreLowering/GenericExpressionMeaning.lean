import Solcore.SourceSemantics.CoreLowering.FunctionCalls

/-! Universal child-expression interfaces for arbitrary authenticated payloads.
The outcome relation is shared with ordinary function calls. These obligations
are semantic induction hypotheses, not fields of static compilation receipts.
Temporary Core slots are represented by an explicit lexical renaming. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly

abbrev Certificate := SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop
abbrev FaultRep := FunctionCalls.FaultRep
abbrev ResultRepresents := @FunctionCalls.ResultRepresents

/-- Every finite independent child execution has a matching Core execution.
The payload model may include closures, mappings and catalog-authenticated data. -/
def Preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
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
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- Every completed Core child execution constructs its independent source
outcome. No source child execution is a premise. -/
def Reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
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
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

theorem ResultRepresents.extend {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (represented : ResultRepresents model mapping world sourceType type faults outcome value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRepresents model futureMapping futureWorld sourceType type faults outcome value := by
  cases represented with
  | value payload => exact .value (model.extend payload maps worlds)
  | fault reason => exact .fault reason

/-- Inserting an administrative value changes the code's renaming, not the
canonical captured environment or any existing value. -/
theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index foundValue found
  exact agrees found

theorem rename_prefix (expression : Expr) (ξ : Renaming) :
    expression.rename (Renaming.comp (Renaming.insertion 0) ξ) =
      (expression.rename ξ).weakenAt 0 := by
  rw [← Expr.rename_comp, Expr.rename_insertion]

end Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
