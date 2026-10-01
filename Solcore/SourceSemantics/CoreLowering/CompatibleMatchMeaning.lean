import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchScrutineeReflection
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileComposition
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace

/-! Selected compatible match bodies receive the actual native frame and typed
captures. These are structural induction interfaces, separate from the static
compiler receipts. The source selection and binder context remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open TypedLexicalWhile (FlowRep Restored)

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource}
  (program : Program) (parent : SourceSemantics.Context) (control : ControlContext)
  (evidence : Dynamic.EvidenceEnvironment) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty)
  {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : FunctionCalls.FaultRep}

def ArmPreserves : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    TypedLexicalWhile.Preserves functions program evidence (values := compilation.values)
      (source := source) (context := armContext) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def ArmReflects : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    TypedLexicalWhile.Reflects functions program evidence (values := compilation.values)
      (source := source) (context := armContext) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def DefaultPreserves : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    TypedLexicalWhile.Preserves functions program evidence (values := compilation.values)
      (source := source) (context := parent) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def DefaultReflects : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    TypedLexicalWhile.Reflects functions program evidence (values := compilation.values)
      (source := source) (context := parent) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

theorem valid_binders {owner : Resolved.DeclarationId} {context finalContext : SourceSemantics.Context}
    {binders : List TypedBinder} (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extended : BindersExtend owner context binders finalContext) :
    CompatibleExpressionLiterals.ContextValid solved finalContext evidence := by
  induction extended with
  | nil => exact valid
  | cons head tail ih => exact ih (TypedLexicalControl.valid_extend valid head)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
