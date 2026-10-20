import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCall
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallPrefix

/-! One body index retains its actual compiler action and invocation origin.
Named cache calls and materialized local calls share the body interface. The
independently substituted Source is related to runtime metadata by `Pair`;
their requirement lists are not identified. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference GeneralHeap
open CallableIndexedHistory
open GeneralizedLocalAcceptedMaterialization

/-- Both constructors retain the accepted compiler receipt. The contextual
constructor also keeps the actual stored closure, read and lexical frame. -/
inductive Index (compiled : SourceCoreUnifiedCompilation.Compiled) where
  | named {named : SourceCoreGeneralFunctions.Function}
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {output : Expr}
      (receipt : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics output)
      (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
        named.signature.key = .ok named.specialized)
  | contextual {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
      (material : Materialization compiled mapping world function) (view : View material)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Index.owner : Index compiled → SourceCompilationPlan.Key
  | @Index.named _ callable _ _ _ _ => callable.signature.key
  | .contextual material _ => material.code.compilation.owner

def Index.active : Index compiled → TypeSystem.Substitution
  | .named _ _ => []
  | .contextual material _ => material.code.active

def Index.source : Index compiled → TypedSource
  | @Index.named _ callable _ _ _ _ => CallableIndexedNamedGeneration.source callable
  | @Index.contextual _ _ _ function _ _ => function.source

/-- The actual native body is compiled against this view. Runtime Source
history remains a distinct index, even when only requirement metadata differs. -/
def Index.compilerSource : Index compiled → TypedSource
  | @Index.named _ callable _ _ _ _ => CallableIndexedNamedGeneration.source callable
  | .contextual material _ => material.code.view

theorem Index.source_view (index : Index compiled) :
    LambdaMetadataViews.MetadataView index.source index.compilerSource := by
  cases index with
  | named _ _ => exact .refl _
  | contextual material _ => exact material.code.viewOfSource

def Index.compilation : Index compiled → SourceCoreFunctions.Context
  | @Index.named _ callable _ _ _ _ => CallableIndexedNamedGeneration.context compiled.indexed callable
  | .contextual material _ => material.code.compilation

def Index.policy : Index compiled → SourceCoreLoops.Policy
  | @Index.named _ callable diagnostics _ receipt _ =>
      AcceptedNamedBodyFlow.namedPolicy compiled.indexed callable diagnostics receipt.parents receipt.own
  | .contextual material _ => GeneralizedLocalAcceptedBodyCompiler.policy material

def Index.fuel : Index compiled → Nat
  | .named _ _ => compiled.indexed.fuel
  | .contextual material _ => material.code.fuel

def Index.scope : Index compiled → SourceCoreLocalCell.Scope
  | @Index.named _ callable _ _ _ _ => callable.inputs.reverse.map fun binding => (binding.1.id, binding.2)
  | .contextual material _ => material.code.receipt.loweredParameters.reverse.map
      (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope

def Index.statements : Index compiled → List StatementId
  | .named receipt _ => receipt.statements
  | @Index.contextual _ _ _ function _ _ => function.body

def Index.result : Index compiled → Ty
  | @Index.named _ callable _ _ _ _ => callable.signature.resultType
  | .contextual material _ => material.code.receipt.resultCore

def Index.reasonAt : Index compiled → ExpressionId → Word
  | @Index.named _ callable diagnostics _ _ _ => diagnostics.reasonAt callable.signature.key
  | .contextual material _ => material.code.reasonAt

def Index.fellThrough : Index compiled → Word
  | .named receipt _ => receipt.own.fellThroughReason
  | .contextual material _ => material.code.compilation.internalReason

def Index.escaped : Index compiled → Word
  | .named receipt _ => receipt.own.table.escapedReason
  | .contextual material _ => material.code.compilation.internalReason

def Index.body : Index compiled → Expr
  | .named receipt _ => receipt.body
  | .contextual material _ => material.code.receipt.body

/-- The complete actual body, with the compiler's original fuel, policy,
parameter scope, diagnostics and statement order. -/
theorem Index.body_receipt (index : Index compiled) :
    Nonempty (AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope
      index.statements index.result index.reasonAt index.fellThrough index.escaped index.body) := by
  cases index with
  | named receipt _ => exact AcceptedNamedBodyFlow.of_compilation receipt
  | contextual material _ =>
    have receipt := GeneralizedLocalAcceptedBodyCompiler.body_receipt material
    simpa only [Index.policy, Index.fuel, Index.compilerSource, Index.scope, Index.statements,
      Index.result, Index.reasonAt, Index.fellThrough, Index.escaped, Index.body] using receipt

theorem Index.compilation_owner (index : Index compiled) :
    index.compilation.owner = index.owner := by cases index <;> rfl

private theorem entry_of_id (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (selected : table.idAt? origin = some id) :
    ∃ entry, table.entryAt? id = some entry ∧ entry.origin = origin := by
  unfold SourceCoreStageCodebook.Table.idAt? at selected
  cases found : table.entries.find? (fun entry => decide (entry.origin = origin)) with
  | none => simp [found] at selected
  | some entry =>
    have origin : entry.origin = origin := by simpa using List.find?_some found
    have identifier : entry.id = id := by simpa [found] using selected
    subst id
    exact ⟨entry, CallableAncestryPairedValidation.stage_entry_self table
      (List.mem_of_find?_eq_some found), origin⟩

/-- Descriptor selection makes the native cumulative substitution agree with
the actual candidate compiler. This does not identify semantic substitutions. -/
theorem view_native_active {mapping world function}
    {material : Materialization compiled mapping world function} (view : View material) :
    (view.recipe.read.after material.origin.metadata).nativeActive = material.code.active := by
  obtain ⟨entry, found, origin⟩ := entry_of_id _ material.indexed.descriptor.found
  rw [← material.descriptorId] at found
  have same := Option.some.inj (found.symm.trans view.recipe.read.descriptorSelected)
  have equal := origin.symm.trans ((congrArg SourceCoreStageCodebook.Entry.origin same).trans
    view.recipe.read.viewOrigin)
  have active := (SourceCoreStageCodebook.Origin.lambda.inj equal).2.2
  change view.recipe.read.entry.view.cumulative = material.code.active
  exact active.symm.trans material.active.symm

theorem view_metadata_owner {mapping world function}
    {material : Materialization compiled mapping world function} (view : View material) :
    (view.recipe.read.after material.origin.metadata).metadata.owner = material.code.compilation.owner := by
  change material.origin.metadata.metadata.owner = material.code.compilation.owner
  rw [material.compilation]
  exact material.origin.owner.trans material.owner.symm

/-- The real frame history and independently substituted source at body entry. -/
structure Frame (index : Index compiled) where
  native : NativeFrame
  ghost : GhostFrame
  metadata : MetadataState
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    native ghost (some metadata)
  paired : CallableAppliedDynamicSourceMaterialization.Pair compiled.indexed.ancestry.graph.inputs
    ghost metadata index.source
  owner : metadata.metadata.owner = index.owner
  active : metadata.nativeActive = index.active

def Frame.contextual {mapping world function}
    (material : Materialization compiled mapping world function) (view : View material) :
    Frame (.contextual material view) where
  native := view.selected
  ghost := .appliedView view.id material.code.descriptor.id view.callerGhost material.origin.ghost
  metadata := view.recipe.read.after material.origin.metadata
  carried := GeneralizedLocalCallPrefix.applied_history material.origin view.carried view.recipe
  paired := view.materialized_pair
  owner := view_metadata_owner view
  active := view_native_active view

theorem Index.frame (index : Index compiled) : Nonempty (Frame index) := by
  cases index with
  | named receipt selected =>
    obtain ⟨id, chosen, carried, _⟩ := receipt.history selected
    exact ⟨⟨_, _, _, carried, .named (CallableIndexedNamedGeneration.seed _ chosen selected),
      rfl, rfl⟩⟩
  | contextual material view => exact ⟨.contextual material view⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
