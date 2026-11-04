import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.Frontend.SourceCoreCallableIndexedPrograms
import Solcore.Frontend.SourceCoreCompatibleOutputs
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped

/-!
# Named calls

Certificates and meaning of named calls and their arguments.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCallCertificates
/-! Static selection of cached named code and the actual nil-argument call
shape. Source declaration/evidence agreement and native installation are
separate obligations; no native closure type invents either of them. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapM_at {α β ε : Type} {f : α → Except ε β} {inputs : List α} {outputs : List β}
    (accepted : inputs.mapM f = .ok outputs) {index : Nat} {input : α}
    (selected : inputs[index]? = some input) :
    ∃ output, outputs[index]? = some output ∧ f input = .ok output := by
  induction inputs generalizing outputs index with
  | nil => simp at selected
  | cons head rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, generated, accepted⟩ := bind_ok accepted
    obtain ⟨remaining, generatedRest, accepted⟩ := bind_ok accepted
    cases accepted
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected; subst input; exact ⟨first, rfl, generated⟩
    | succ index =>
      obtain ⟨output, position, compiled⟩ := ih generatedRest selected
      exact ⟨output, position, compiled⟩

/-- The actual installer shifts free global/capture slots while retaining the
lambda argument at index zero. The body theorem uses this lifted renaming. -/
def installationRenaming : Nat → Renaming
  | 0 => Renaming.id
  | index + 1 => Renaming.comp (Renaming.insertion 0) (installationRenaming index)

private theorem installation_index (count index : Nat) : installationRenaming count index = count + index := by
  induction count with
  | zero => simp [installationRenaming, Renaming.id]
  | succ count ih => simp [installationRenaming, Renaming.comp, Renaming.insertion, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem installation_argument (count : Nat) : (installationRenaming count).lift 0 = 0 := rfl

theorem installation_reference (count index : Nat) :
    (installationRenaming count).lift (index + 1) = count + index + 1 := by
  simp only [Renaming.lift, installation_index]

private theorem installed_rename (count : Nat) (expression : Expr) :
    SourceCoreCompatibleOutputs.installedTemplate count expression = expression.rename (installationRenaming count) := by
  induction count with
  | zero => simp [SourceCoreCompatibleOutputs.installedTemplate, installationRenaming, Expr.rename_id]
  | succ count ih =>
    unfold SourceCoreCompatibleOutputs.installedTemplate
    rw [List.range_succ, List.foldl_append]
    change (SourceCoreCompatibleOutputs.installedTemplate count expression).weakenAt 0 = _
    rw [ih, ← Expr.rename_insertion, Expr.rename_comp]
    rfl

/-- Exact saved body syntax after installation, including its real named-hook
administrative reference. This grants no closure/source authority by itself. -/
theorem installed_lambda (count : Nat) (parameter result : Ty) (body : Expr) :
    SourceCoreCompatibleOutputs.installedTemplate count (.lambda parameter result body) =
      .lambda parameter result (body.rename (installationRenaming count).lift) := by
  rw [installed_rename]
  rfl

/-- Real second-pass success selects the compiler equation for this exact
plan function and the cached code at the same slot. -/
theorem compiled_at {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : prepared.base.functions[index]? = some named) :
    ∃ diagnostics code,
      prepared.base.diagnostics = some diagnostics ∧
      prepared.secondPass.closures[index]? = some code ∧
      SourceCoreGeneralFunctions.compileClosureWithRepresentation prepared.base.sourceProgram
        (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
        prepared.base.sourceProgram.signatures prepared.base.plan prepared.base.globals
        (match prepared.base.callableContext with
          | none => diagnostics.program
          | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
        prepared.base.locals prepared.base.callableContext prepared.fuel named = .ok code := by
  have accepted := prepared.secondPass.compiled
  unfold SourceCoreCompatibleMarkedFunctions.compileClosures at accepted
  by_cases empty : prepared.base.functions.isEmpty = true
  · have absent := List.isEmpty_iff.mp empty
    rw [absent] at selected
    simp at selected
  · simp only [empty, Bool.false_eq_true, ↓reduceIte] at accepted
    cases diagnosticResult : prepared.base.diagnostics with
    | none => simp [diagnosticResult, bind, Except.bind] at accepted
    | some diagnostics =>
      simp only [diagnosticResult, bind, Except.bind, pure, Except.pure, Except.mapError] at accepted
      split at accepted
      · cases accepted
      · rename_i codes generated
        cases accepted
        obtain ⟨code, position, compiled⟩ := mapM_at generated selected
        exact ⟨diagnostics, code, rfl, position, compiled⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem zipIdx_selected {α : Type} {inputs : List α} {input : α} {index : Nat}
    (member : (input, index) ∈ inputs.zipIdx) : inputs[index]? = some input := by
  have facts := List.mem_zipIdx member
  simpa using (List.getElem?_eq_getElem (by simpa using facts.2.1)).trans (congrArg some facts.2.2.symm)

/-- The accepted action retains the canonical instantiation target, actual
plan edge, exact specialization and unique native global slot. These facts
come from the checks that ran; matching native types alone is insufficient. -/
theorem selected_signature_facts
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature)) :
    ∃ caller target specialized,
      source.owner = compilation.owner.declaration ∧
      SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller ∧
      caller.assumptions = [] ∧
      SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok target ∧
      (if isReference then SourceCompilationPlan.exactReferenceKey compilation.plan compilation.owner node.id target
        else SourceCompilationPlan.exactCallKey compilation.plan compilation.owner node.id target) = .ok signature.key ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      specialized.assumptions = [] ∧ compilation.globals[index]? = some signature := by
  unfold SourceCoreFunctions.selectedSignature at accepted
  by_cases owner : source.owner = compilation.owner.declaration
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
    obtain ⟨caller, callerReceipt, accepted⟩ := bind_ok accepted
    have callerReceipt := mapError_ok callerReceipt
    split at accepted
    · obtain ⟨target, targetReceipt, accepted⟩ := bind_ok accepted
      obtain ⟨key, edgeReceipt, accepted⟩ := bind_ok accepted
      obtain ⟨specialized, specializationReceipt, accepted⟩ := bind_ok accepted
      split at accepted
      · split at accepted
        · cases accepted
        · split at accepted
          all_goals simp only [pure, Except.pure, bind, Except.bind] at accepted
          all_goals try contradiction
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨selection, globalReceipt, accepted⟩ := bind_ok accepted
          rcases selection with ⟨selectedIndex, selectedSignature⟩
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          cases accepted
          change ((match compilation.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
            | [] => .error (.callPreparation (.missingSpecialization key))
            | [(signature, index)] => .ok (index, signature)
            | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))) :
              Except SourceCoreBasic.Error (Nat × SourceCoreCalls.Signature)) =
              .ok (selectedIndex, selectedSignature) at globalReceipt
          split at globalReceipt
          · cases globalReceipt
          · rename_i signature index filtered
            cases globalReceipt
            have member : (selectedSignature, selectedIndex) ∈ compilation.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) := by
              rw [filtered]; exact .head _
            have facts := List.mem_filter.mp member
            have keyEq : selectedSignature.key = key := of_decide_eq_true facts.2
            refine ⟨caller, target, specialized, by simpa using owner, callerReceipt,
              List.isEmpty_iff.mp (by assumption), mapError_ok targetReceipt, ?_, ?_,
              List.isEmpty_iff.mp (by assumption), zipIdx_selected facts.1⟩
            · simpa only [keyEq] using mapError_ok edgeReceipt
            · simpa only [keyEq] using mapError_ok specializationReceipt
          · cases globalReceipt
      · cases accepted
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [owner, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

private theorem edge_target {plan : SourceSpecializationWorklist.Plan}
    {caller target selected : SourceSpecialization.SpecializationKey} {id : ExpressionId} {reference : Bool}
    (accepted : (if reference then SourceCompilationPlan.exactReferenceKey plan caller id target
      else SourceCompilationPlan.exactCallKey plan caller id target) = .ok selected) : selected = target := by
  cases reference <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
  all_goals
    first | unfold SourceCompilationPlan.exactCallKey at accepted
          | unfold SourceCompilationPlan.exactReferenceKey at accepted
    split at accepted
    · cases accepted
    · rename_i edge filtered
      cases accepted
      have member : edge ∈ [edge] := .head _
      rw [← filtered] at member
      have facts := (List.mem_filter.mp member).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at facts
      exact facts.2
    · cases accepted

/-- The exact edge check cannot silently redirect the canonical target. -/
theorem selected_signature_target
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature)) :
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[index]? = some signature := by
  obtain ⟨_, target, _, _, _, _, targeted, edge, _, _, global⟩ := selected_signature_facts accepted
  have key := edge_target edge
  exact ⟨key.symm ▸ targeted, global⟩

/-- Real ordinary direct-call lowering with no argument children emits the
global-cell helper. The selected signature is exposed without asserting source
declaration identity from its native parameter/result types. -/
theorem nil_call_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) ∧
      lowered.expression = SourceCoreCalls.call signature
        (scope.length + compilation.administrativePrefix + index)
        (SourceCoreCalls.packArguments []).expression compilation.internalReason ∧
      lowered.type = type := by
  cases hook : policy.lowerSpecial? <;>
    simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook,
      bind, Except.bind, pure, Except.pure] at accepted
    try rw [special] at accepted
    simp only [bind, Except.bind, pure, Except.pure, form, read, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted
    · cases accepted
    · obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨selection, selectionReceipt, accepted⟩ := bind_ok accepted
      rcases selection with ⟨index, signature⟩
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted
      · obtain ⟨_, _, accepted⟩ := bind_ok accepted
        simp only [List.mapM_nil, bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        cases accepted
        exact ⟨index, signature, selectionReceipt, rfl, rfl⟩

/-- An accepted declaration reference retains its real callable-decoration
request. Its descriptor origin is the selected key, not a native type guess. -/
theorem reference_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature identity,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation true = .ok (index, signature) ∧
      Word.ofNat? (index + 1) = some identity ∧
      policy.callables.decorateCallable compilation source node (.named signature.key)
        signature.parameterType signature.resultType
        (SourceCoreFunctions.namedReference signature
          (scope.length + compilation.administrativePrefix + index) identity compilation.internalReason) =
        .ok lowered.expression ∧ lowered.type = type := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook,
      bind, Except.bind, pure, Except.pure] at accepted
    try rw [special] at accepted
    simp only [bind, Except.bind, pure, Except.pure, form, read] at accepted
    obtain ⟨selection, selectionReceipt, accepted⟩ := bind_ok accepted
    rcases selection with ⟨index, signature⟩
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · rename_i identity wordReceipt
      obtain ⟨expression, decorated, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨index, signature, identity, selectionReceipt, wordReceipt, decorated, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted

/-- Nil argument packing is a concrete static typed argument certificate. -/
theorem nil_arguments_typed (environment : Core.Context) (definitions : DataEnvironment) :
    HasType environment (SourceCoreCalls.packArguments []).expression
      (LanguageResult.resultType .unit) definitions :=
  .inRight .word .unit

theorem nil_arguments_evaluates (environment : Environment) (store : Store) :
    Evaluates environment store (SourceCoreCalls.packArguments []).expression (.inRight .word .unit) store :=
  .inRight .unit

end Solcore.SourceSemantics.CoreLowering.NamedCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCallMeaning
/-! Concrete named-call bodies beneath their actual installed template
renaming. Parameter and body meaning is derived from the concrete lexical
certificate. Native references, source declaration evidence and protected snapshot
history are explicit independent facts, never inferred from a function type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private theorem rename_front (expression : Expr) (ξ : Renaming) :
    (expression.weakenAt 0).rename ξ.lift = (expression.rename ξ).weakenAt 0 := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, Renaming.lift_comp_insertion_zero]

/-- Installation weakens the entire wrapper, including its frame reference.
This is a syntax law, not equality of closure values across environments. -/
theorem withFrame_rename (reference next body : Expr) (ξ : Renaming) :
    (SourceCoreCallableIndexedFrames.withFrame reference next body).rename ξ =
      SourceCoreCallableIndexedFrames.withFrame (reference.rename ξ) (next.rename ξ) (body.rename ξ) := by
  simp only [SourceCoreCallableIndexedFrames.withFrame, SourceCoreCallableContextFrames.withFrame,
    Expr.rename, rename_front, Renaming.lift]

private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

/-- The actual general callable profile wraps this named reference with its
owned descriptor. The closure code remains the global cell's exact payload. -/
theorem reference_decoration (native : SourceCoreGeneralFunctions.CallableContext)
    (active : TypeSystem.Substitution) (compilation : SourceCoreFunctions.Context)
    (source : TypedSource) (node : ExpressionNode) (signature : SourceCoreCalls.Signature)
    (index : Nat) (identity : Word)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named signature.key))
    (accepted : SourceCoreCallableContracts.descriptor native.table (.named signature.key) = .ok descriptor) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable compilation source node
      (.named signature.key) signature.parameterType signature.resultType
      (SourceCoreFunctions.namedReference signature index identity compilation.internalReason) =
      .ok (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity compilation.internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0)))) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, accepted, Except.mapError,
    bind, Except.bind, pure, Except.pure]
  rfl

theorem native_reference {environment captured : Environment} {store : Store}
    {signature : SourceCoreCalls.Signature} {index : Nat} {location : Location}
    {identity internalReason : Word} {body : Expr}
    {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named signature.key))
    (reference : environment[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    Evaluates environment store
      (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0))))
      (.inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id))) store := by
  have selected := OptionalCell.read_success internalReason (Evaluates.var reference) read
  have tagged : Evaluates environment store (SourceCoreFunctions.namedReference signature index identity internalReason)
      (.inRight .word (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) store :=
    LanguageResult.bind_success
    (TaggedFunction.functionType signature.parameterType signature.resultType) selected
    (Evaluates.inRight (Evaluates.pair (Evaluates.inRight Evaluates.word) (Evaluates.var rfl)))
  exact LanguageResult.bind_success _ tagged (.inRight (.pair (.var rfl) .word))

/-- Completed formation recovers exactly the owned cell payload and descriptor
and leaves the shared store unchanged. It does not authenticate arbitrary
externally supplied closure bodies merely from their function type. -/
theorem native_reference_reflects {environment captured : Environment} {store finalStore : Store}
    {signature : SourceCoreCalls.Signature} {index : Nat} {location : Location}
    {identity internalReason : Word} {body : Expr} {value : Value}
    {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named signature.key))
    (reference : environment[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (executed : Evaluates environment store
      (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0)))) value finalStore) :
    value = .inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id)) ∧ finalStore = store :=
  evaluation_deterministic executed (native_reference descriptor reference read)


/-- Actual reference lowering simultaneously constructs the independent source
global value and the owned native descriptor paired with the exact installed
cell payload. Completed formation recovers that same value/store. -/
theorem accepted_named_reference
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {index : Nat} {signature : SourceCoreCalls.Signature} {identity : Word}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node instantiation true = .ok (index, signature))
    (identified : Word.ofNat? (index + 1) = some identity)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named signature.key))
    (descriptorAccepted : SourceCoreCallableContracts.descriptor native.table (.named signature.key) = .ok descriptor)
    {program : Program} {context : SourceSemantics.Context} {evidence produced : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {heap : Dynamic.Heap}
    (coercions : node.coercions = [])
    (requirements : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.RequirementsProduceEnvironment context evidence [] instantiation.predicates produced)
    {environment captured : Environment} {store : Store} {location : Location} {body : Expr}
    (globalReference : environment[scope.length + compilation.administrativePrefix + index]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (globalPayload : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[index]? = some signature ∧
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment heap id (.global ⟨instantiation, produced⟩) heap ∧
    Evaluates environment store lowered.expression
      (.inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id))) store ∧
    (∀ value finalStore, Evaluates environment store lowered.expression value finalStore →
      value = .inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id)) ∧ finalStore = store) := by
  obtain ⟨selectedIndex, selectedSignature, selectedIdentity, selected, identifiedAction, decorated, _⟩ :=
    reference_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selected.symm.trans selection)
  cases same
  have sameIdentity := Option.some.inj (identifiedAction.symm.trans identified)
  cases sameIdentity
  rw [profile, reference_decoration native active compilation source node signature _ identity descriptor descriptorAccepted] at decorated
  have emitted := Except.ok.inj decorated
  have sourceEvaluation := reference (program := program) (environment := sourceEnvironment) (heap := heap)
    found form coercions requirements valid closed
  obtain ⟨target, global⟩ := selected_signature_target selection
  rw [← emitted]
  exact ⟨target, global, sourceEvaluation, native_reference descriptor globalReference globalPayload,
    fun _ _ evaluated => native_reference_reflects descriptor globalReference globalPayload evaluated⟩


variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (certificate : TypedLexicalNamedBody.Certificate layouts owner active prepared.layout.frame allocationGlobals onError readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- A source allocation and its finite body trace execute the real full named
hook. Parameters are compared with the independently constructed allocation. -/
theorem hook_preserves {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := TypedMixedNamedParameters.entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    TypedLexicalNamedParameters.preserves functions extension definitions registered program contextValid unique uninitialized missing entry certificate trace
  rw [rename_prefix] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var actualReference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    renamed.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, by simpa only [sameEnvironment, sameHeap] using reached⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- Completed actual native execution constructs both source parameter
allocation and the independent body trace from the installed call context with its actual lexical stopping context. -/
theorem hook_reflects {value : Value} {finalStore : Store}
    (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := TypedMixedNamedParameters.entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  rw [renamed] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    TypedLexicalNamedParameters.reflects functions extension definitions registered program contextValid unique uninitialized missing entry certificate bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, entry.environment, entry.heap, outcome, after, finalMap, finalWorld, owned, history,
    entry.allocation, trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, reached⟩

/-- The installed global read is pure; after the concrete nil pack, the real
call helper enters exactly the retained closure body. Reflection uses native
evaluation inversion, with no child body evaluation supplied. -/
theorem installed_call_agreement {signature : SourceCoreCalls.Signature}
    {caller captured : Environment} {store : Store} {index : Nat} {location : Location} {body : Expr} {reason : Word}
    (reference : caller[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    ContinuationAgreement caller store
      (SourceCoreCalls.call signature index (SourceCoreCalls.packArguments []).expression reason)
      (.unit :: captured) store body := by
  have arguments := nil_arguments_evaluates caller store
  have selected := OptionalCell.read_success reason
    (show Evaluates (.unit :: caller) store (.var (index + 1))
      (.cellRef (OptionalCell.cellType signature.functionType) location) store from .var reference) read
  constructor
  · intro value finalStore executed
    exact SourceCoreCalls.call_success arguments selected executed
  · intro value finalStore executed
    obtain ⟨_, sized⟩ := evaluation_has_size executed
    obtain ⟨_, _, following⟩ := sized.bind_success arguments
    obtain ⟨_, _, applied⟩ := following.bind_success selected
    obtain ⟨_, _, bodyEvaluation⟩ := applied.apply_body (.var rfl) (.var rfl)
    exact bodyEvaluation.sound


/-- Compiler success and its accepted plan selection enter the exact installed
body. This closes call formation/inversion without any child body evaluation. -/
theorem accepted_nil_agreement
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {type : Ty} {index : Nat} {signature : SourceCoreCalls.Signature}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {environment captured : Environment} {store : Store} {location : Location} {body : Expr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature))
    (reference : environment[scope.length + compilation.administrativePrefix + index]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (payload : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[index]? = some signature ∧ lowered.type = type ∧
    ContinuationAgreement environment store lowered.expression (.unit :: captured) store body := by
  obtain ⟨selectedIndex, selectedSignature, selected, emitted, typed⟩ :=
    nil_call_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selected.symm.trans selection)
  cases same
  obtain ⟨target, global⟩ := selected_signature_target selection
  exact ⟨target, global, typed, emitted.symm ▸ installed_call_agreement reference payload⟩


variable {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
  (sourceFrame : SourceFrame program instantiation bodyInstance function)
  (agreement : CompatibleNamedBody.NamedAgreement named function)
  (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
  {signature : SourceCoreCalls.Signature} {callerEnvironment captured : Environment}
  {globalIndex slot : Nat} {globalLocation : Location}
  {compiledRepresentation : SourceCoreGeneralFunctions.Representation} {compiledFuel : Nat}
  (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base compiledRepresentation compiledFuel)
  (selected : base.functions[slot]? = some named)
  (cached : compiled.closures[slot]? = some
    (.lambda signature.parameterType (LanguageResult.resultType signature.resultType) code))
  (signatureOwned : signature = named.signature)
  (parameterUnit : signature.parameterType = .unit) (resultType : signature.resultType = output)
  (bodyEnvironment : actual = .unit :: captured)
  (globalReference : callerEnvironment[globalIndex]? = some (.cellRef (OptionalCell.cellType signature.functionType) globalLocation))
  (globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure signature.parameterType (LanguageResult.resultType signature.resultType) (code.rename ξ) captured)))

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- A finite independent named-body trace executes the actual installed
global-cell call. Its nil argument pack is derived, and the concrete body
certificate closes all body meaning beneath the real indexed frame wrapper. -/
theorem nil_call_preserves
    (nativeNil : nativeArguments = [])
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after)
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      base.functions[slot]? = some named ∧
      compiled.closures[slot]? = some (.lambda signature.parameterType
        (LanguageResult.resultType signature.resultType) code) ∧
      signature = named.signature ∧ signature.parameterType = .unit ∧ signature.resultType = output ∧
      CompatibleNamedBody.NamedAgreement named function ∧
      SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before
        (.global ⟨instantiation, function.evidence⟩) [] outcome after ∧
      Evaluates callerEnvironment store (SourceCoreCalls.call signature globalIndex
        (SourceCoreCalls.packArguments []).expression Word.zero) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    evaluated, result, finalHeap, maps, worlds, frame, extendedMetadata, restored, preservedSnapshots, _⟩ :=
    hook_preserves prepared functions extension program onError certificate parameters inputs extended contextValid unique
      uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments heaps initialLocals
      actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots allocated trace
  have nilSource : arguments = [] := List.eq_nil_of_length_eq_zero (by
    rw [← represented.length.1, represented.length.2, nativeNil]
    rfl)
  have source := sourceFrame.call (callerContext := callerContext) (caller := callerEvidence) (sourceFrame.body_of_trace extended allocated trace)
  have applied : Evaluates (.unit :: captured) store (code.rename ξ) value finalStore := bodyEnvironment ▸ evaluated
  have argumentsEvaluation := nil_arguments_evaluates callerEnvironment store
  have read := OptionalCell.read_success Word.zero
    (show Evaluates (.unit :: callerEnvironment) store (.var (globalIndex + 1))
      (.cellRef (OptionalCell.cellType signature.functionType) globalLocation) store from .var globalReference) globalRead
  have invocation := SourceCoreCalls.call_success argumentsEvaluation read applied
  exact ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    selected, cached, signatureOwned, parameterUnit, resultType, agreement, target, nilSource ▸ source, invocation, result, finalHeap, maps, worlds, frame, extendedMetadata, restored, preservedSnapshots⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- Every completed installed nil-argument call constructs an independent
source global application, including body faults and exact shared-heap writes.
The parameter prefix and lexical body are derived from their static receipts. -/
theorem nil_call_reflects (nativeNil : nativeArguments = [])
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates callerEnvironment store (SourceCoreCalls.call signature globalIndex
      (SourceCoreCalls.packArguments []).expression Word.zero) value finalStore) :
    ∃ origin index metadata outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      base.functions[slot]? = some named ∧
      compiled.closures[slot]? = some (.lambda signature.parameterType
        (LanguageResult.resultType signature.resultType) code) ∧
      signature = named.signature ∧ signature.parameterType = .unit ∧ signature.resultType = output ∧
      CompatibleNamedBody.NamedAgreement named function ∧
      SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before
        (.global ⟨instantiation, function.evidence⟩) [] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  have bodyEvaluation := (installed_call_agreement globalReference globalRead).unwrap evaluated
  rw [← bodyEnvironment] at bodyEvaluation
  obtain ⟨origin, index, metadata, environment, bound, outcome, after, finalMap, finalWorld, owned, history,
    allocated, trace, result, finalHeap, maps, worlds, frame, extendedMetadata, restored, preservedSnapshots, _⟩ :=
    hook_reflects prepared functions extension program onError certificate parameters inputs extended contextValid unique
      uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments heaps initialLocals
      actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots bodyEvaluation
  have nilSource : arguments = [] := List.eq_nil_of_length_eq_zero (by
    rw [← represented.length.1, represented.length.2, nativeNil]
    rfl)
  have source := sourceFrame.call (callerContext := callerContext) (caller := callerEvidence)
    (sourceFrame.body_of_trace extended allocated trace)
  exact ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history,
    selected, cached, signatureOwned, parameterUnit, resultType, agreement, target, nilSource ▸ source, result, finalHeap,
    maps, worlds, frame, extendedMetadata, restored, preservedSnapshots⟩


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- Preservation starts with the independent instantiated declaration body's
outcome. Its real parameter allocation and trace are extracted at the concrete
certified context, rather than supplied as a semantic body hypothesis. -/
theorem nil_body_preserves (nativeNil : nativeArguments = [])
    {after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (execution : BodyOutcome program bodyInstance function.evidence before arguments outcome after)
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      base.functions[slot]? = some named ∧
      compiled.closures[slot]? = some (.lambda signature.parameterType
        (LanguageResult.resultType signature.resultType) code) ∧
      signature = named.signature ∧ signature.parameterType = .unit ∧ signature.resultType = output ∧
      CompatibleNamedBody.NamedAgreement named function ∧
      SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before
        (.global ⟨instantiation, function.evidence⟩) [] outcome after ∧
      Evaluates callerEnvironment store (SourceCoreCalls.call signature globalIndex
        (SourceCoreCalls.packArguments []).expression Word.zero) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  have arity : function.parameters.length = arguments.length := by
    rw [parameters, List.length_map]
    exact represented.length.1
  obtain ⟨environment, bound, allocated, trace⟩ := sourceFrame.trace_of_body extended arity execution
  exact nil_call_preserves prepared functions extension program onError certificate parameters inputs extended
    contextValid unique uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments
    heaps initialLocals actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots
    sourceFrame agreement target compiled selected cached signatureOwned parameterUnit resultType bodyEnvironment globalReference globalRead
    nativeNil allocated trace callerContext callerEvidence


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- The final ordinary expression boundary consumes actual lowering success,
canonical selected-key attribution and the concrete body tree. Every completed
Core result reconstructs the independent source direct call, with the exact
callee instantiation/evidence and restored indexed administration. -/
theorem nil_expression_reflects
    (nativeNil : nativeArguments = [])
    {expressionPolicy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {name : String} {type : Ty}
    {expressionReason : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : expressionPolicy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match expressionPolicy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (min budget expressionFuel)
              compilation childSource childScope childId childReasonAt)
          (expressionFuel + 1) source scope id expressionReason) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (expressionFuel + 1)
      compilation source scope id expressionReason = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature expressionPolicy compilation source node instantiation false = .ok (slot, signature))
    (offset : globalIndex = scope.length + compilation.administrativePrefix + slot)
    (internal : compilation.internalReason = Word.zero)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence node.requirements node.coercions
      instantiation.predicates function.evidence)
    (sourceEnvironment : Dynamic.Environment)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates callerEnvironment store lowered.expression value finalStore) :
    ∃ origin index metadata outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence source sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨selectedIndex, selectedSignature, selectedAction, emitted, _⟩ :=
    nil_call_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selectedAction.symm.trans selection)
  cases same
  rw [emitted, ← offset, internal] at evaluation
  obtain ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history, _, _, _, _, _, _, _,
    called, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩ :=
    nil_call_reflects prepared functions extension program onError certificate parameters inputs extended
      contextValid unique uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments
      heaps initialLocals actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots
      sourceFrame agreement target compiled selected cached signatureOwned parameterUnit resultType bodyEnvironment globalReference globalRead
      nativeNil callerContext callerEvidence evaluation
  have sourceEvaluation := direct_nil (environment := sourceEnvironment) found form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed called
  exact ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history,
    sourceEvaluation, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- Preservation of the actual lowered expression starts with the independent
instantiated declaration body. The concrete certificate constructs body/prefix
meaning and preserves the exact source declaration and caller evidence. -/
theorem nil_expression_preserves
    (nativeNil : nativeArguments = [])
    {expressionPolicy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {name : String} {type : Ty}
    {expressionReason : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : expressionPolicy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match expressionPolicy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (min budget expressionFuel)
              compilation childSource childScope childId childReasonAt)
          (expressionFuel + 1) source scope id expressionReason) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (expressionFuel + 1)
      compilation source scope id expressionReason = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature expressionPolicy compilation source node instantiation false = .ok (slot, signature))
    (offset : globalIndex = scope.length + compilation.administrativePrefix + slot)
    (internal : compilation.internalReason = Word.zero)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence node.requirements node.coercions
      instantiation.predicates function.evidence)
    (sourceEnvironment : Dynamic.Environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (execution : BodyOutcome program bodyInstance function.evidence before arguments outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence source sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store lowered.expression value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨selectedIndex, selectedSignature, selectedAction, emitted, _⟩ :=
    nil_call_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selectedAction.symm.trans selection)
  cases same
  obtain ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history, _, _, _, _, _, _, _,
    called, evaluation, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩ :=
    nil_body_preserves prepared functions extension program onError certificate parameters inputs extended
      contextValid unique uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments
      heaps initialLocals actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots
      sourceFrame agreement target compiled selected cached signatureOwned parameterUnit resultType bodyEnvironment globalReference globalRead
      nativeNil execution callerContext callerEvidence
  have sourceEvaluation := direct_nil (environment := sourceEnvironment) found form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed called
  rw [emitted, ← offset, internal]
  exact ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    sourceEvaluation, evaluation, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩

end Solcore.SourceSemantics.CoreLowering.NamedCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCallArgumentCertificates
/-! Actual ordinary named-call lowering retains every argument compiler
result. These are static receipts; argument and body execution remain in the
independent semantic relations. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem type_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {value : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok value) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- The actual selected canonical target and ordered argument traversal.
The compiler checked the original arity and packed native parameter type. -/
theorem call_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {arguments : List ExpressionId} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature specialized codes,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      arguments.length = specialized.function.typedBody.inputs.length ∧
      arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
        compilation source scope argument reasonAt) = .ok codes ∧
      signature.parameterType = (SourceCoreCalls.packArguments codes).type ∧
      signature.resultType = type ∧
      lowered.expression = SourceCoreCalls.call signature
        (scope.length + compilation.administrativePrefix + index)
        (SourceCoreCalls.packArguments codes).expression compilation.internalReason ∧
      lowered.type = type := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook,
      bind, Except.bind, pure, Except.pure] at accepted
    try rw [special] at accepted
    simp only [bind, Except.bind, pure, Except.pure, form, read, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted
    · cases accepted
    · obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨selection, selectionReceipt, accepted⟩ := bind_ok accepted
      rcases selection with ⟨index, signature⟩
      obtain ⟨specialized, specialization, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted
      · rename_i arity
        obtain ⟨_, resultChecked, accepted⟩ := bind_ok accepted
        obtain ⟨codes, argumentCodes, accepted⟩ := bind_ok accepted
        obtain ⟨_, parameterChecked, accepted⟩ := bind_ok accepted
        cases accepted
        refine ⟨index, signature, specialized, codes, selectionReceipt, ?_, ?_, argumentCodes, ?_, ?_, rfl, rfl⟩
        · cases actual : SourceCompilationPlan.exactSpecialization compilation.plan signature.key <;>
            simp [actual, Except.mapError] at specialization ⊢
          exact specialization
        · exact Classical.not_not.mp arity
        · exact type_eq parameterChecked
        · exact type_eq resultChecked

private theorem argument_types {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (children : DataExpressionSequence.Tree source
      (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) scope ids types codes) :
    types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction children with
  | nil => rfl
  | single found child => simp [child.projected found, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  | cons found child _ ih => simp [List.mapM_cons, child.projected found, ih, Functor.map, Except.map, bind, Except.bind]

/-- Instantiate successful argument traversal with concrete General trees.
Raw source argument types and per-binder projections are independent static
typing facts. Packed type equality alone cannot recover source arity. -/
theorem arguments_of_functions
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {arguments : List ExpressionId} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {bindings : List (TypedBinder × Ty)}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (bindings.map Prod.snd))
    (children : ∀ codes, arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
        compilation source scope argument reasonAt) = .ok codes →
      DataExpressionSequence.Tree source (CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt)
        scope arguments (bindings.map (fun binding => binding.1.scheme.body)) codes)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature specialized codes,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      arguments.length = specialized.function.typedBody.inputs.length ∧
      DataExpressionSequence.Tree source (CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt)
        scope arguments (bindings.map (fun binding => binding.1.scheme.body)) codes ∧
      codes.map (·.type) = bindings.map Prod.snd ∧
      signature.parameterType = (SourceCoreCalls.packArguments codes).type ∧
      signature.resultType = type ∧
      lowered.expression = SourceCoreCalls.call signature
        (scope.length + compilation.administrativePrefix + index)
        (SourceCoreCalls.packArguments codes).expression compilation.internalReason ∧
      lowered.type = type := by
  obtain ⟨index, signature, specialized, codes, selected, specializedReceipt, arity, codesReceipt,
    parameter, result, emitted, nativeType⟩ := call_of_accepted owner found read form special accepted
  have argumentTrees := children codes codesReceipt
  have nativeTypes := Except.ok.inj ((argument_types argumentTrees).symm.trans projected)
  exact ⟨index, signature, specialized, codes, selected, specializedReceipt, arity,
    argumentTrees, nativeTypes, parameter, result, emitted, nativeType⟩

/-- An occurrence retains the actual compiler action and the exact selected
slot and child results. Every field is static syntax or compiler success. -/
structure Emission (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id callee : ExpressionId) (arguments : List ExpressionId)
    (instantiation : DeclarationInstantiation) (signature : SourceCoreCalls.Signature)
    (codes : List SourceCoreBasic.LoweredExpr) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  reasonAt : ExpressionId → Word
  node : ExpressionNode
  type : Ty
  owner : id.occurrence.owner = source.owner
  found : source.lookupExpression? id = some node
  read : policy.readExpression source id = .ok (node, type)
  form : node.form = .call callee arguments (.declaration instantiation)
  special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
            compilation childSource childScope childId childReasonAt)
        (fuel + 1) source scope id reasonAt) = .ok none
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
    compilation source scope id reasonAt = .ok lowered
  index : Nat
  selection : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature)
  argumentsAccepted : arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
    compilation source scope argument reasonAt) = .ok codes

/-- The saved compiler actions determine the emitted helper and canonical
target. Equality is propositional; no executable Plan equality is assumed. -/
theorem Emission.equation {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {signature : SourceCoreCalls.Signature}
    {codes : List SourceCoreBasic.LoweredExpr} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation source scope id callee arguments instantiation signature codes lowered) :
    lowered.expression = SourceCoreCalls.call signature
      (scope.length + compilation.administrativePrefix + receipt.index)
      (SourceCoreCalls.packArguments codes).expression compilation.internalReason ∧
    signature.parameterType = (SourceCoreCalls.packArguments codes).type ∧
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[receipt.index]? = some signature := by
  obtain ⟨index, selectedSignature, specialized, actualCodes, selected, _, _, compiled, parameter, _, emitted, _⟩ :=
    call_of_accepted receipt.owner receipt.found receipt.read receipt.form receipt.special receipt.accepted
  have same := Except.ok.inj (selected.symm.trans receipt.selection)
  cases same
  have sameCodes := Except.ok.inj (compiled.symm.trans receipt.argumentsAccepted)
  cases sameCodes
  have target := NamedCalls.selected_signature_target receipt.selection
  exact ⟨emitted, parameter, target⟩

end Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCallArgumentMeaning
/-! Ordinary named calls compose concrete recursive argument trees with a
concrete lexical named-body certificate. Installed globals and caller frames
are transported along the actual argument heap effects before body entry. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
open CallableIndexedHistory CallableIndexedParameterCertificates
open SourceCoreCallableIndexedFrames

abbrev ValuesContext := SourceCoreCompatibleValues.Context

/-- Static body compilation and independent declaration attribution. There
is no source execution, native execution or body meaning field. -/
structure Body {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) where
  function : Dynamic.Closure
  instantiation : DeclarationInstantiation
  sourceBody : Dynamic.BodyInstance
  frame : NamedCalls.SourceFrame program instantiation sourceBody function
  named : SourceCoreGeneralFunctions.Function
  agreement : CompatibleNamedBody.NamedAgreement named function
  closed : named.specialized.assumptions = []
  ordinaryReturn : named.specialized.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  bindings : List Binding
  parameters : function.parameters = bindings.map Prod.fst
  inputs : function.source.inputs = bindings.map Prod.fst
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  readFuel : Nat
  output : Ty
  policy : SourceCoreLoops.Policy
  fuel : Nat
  fellThrough : Word
  escaped : Word
  body : Expr
  parameterCode : Expr
  code : Expr
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  certificate : TypedLexicalNamedBody.Certificate layouts owner active prepared.layout.frame globals onError readFuel values
    function.source context solved reasonAt (bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    function.body function.resultType output policy fuel fellThrough escaped body
  acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code
  definitions_eq : layouts.definitions = definitions
  registered : prepared.layout.frame.Registered definitions
  valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence
  unique : NodeOccurrencesUnique function.source
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  resultType : named.signature.resultType = output
  representation : SourceCoreGeneralFunctions.Representation
  compiledFuel : Nat
  compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel
  slot : Nat
  selected : base.functions[slot]? = some named
  cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)

private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)

private theorem arguments_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {bindings : List Binding}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads) :
    RuntimeValueHasType world (DataPatternValues.packValues payloads)
      (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) definitions := by
  induction represented with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => simpa [DataPatternValues.packValues, SourceCoreCompatibleCatalog.packTypes] using model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

/-- Rename the complete helper, preserving the inserted argument/function
binders and moving only its real caller environment slot. -/
theorem call_rename (signature : SourceCoreCalls.Signature) (index : Nat)
    (arguments : Expr) (reason : Word) (ξ : Renaming) :
    (SourceCoreCalls.call signature index arguments reason).rename ξ =
      SourceCoreCalls.call signature (ξ index) (arguments.rename ξ) reason := by
  simp [SourceCoreCalls.call, LanguageResult.bind, OptionalCell.read, LanguageResult.success,
    LanguageResult.failure, Expr.rename, Renaming.lift]

/-- A finite whole call necessarily completes its first argument bundle. -/
theorem arguments_complete {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment : Environment} {store finalStore : Store} {value : Value}
    (completed : Evaluates environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    ∃ argumentValue argumentStore, Evaluates environment store arguments argumentValue argumentStore := by
  cases completed with
  | caseLeft argument _ => exact ⟨_, _, argument⟩
  | caseRight argument _ => exact ⟨_, _, argument⟩

/-- With the observed argument result and authenticated installed global,
actual call completion enters the exact saved body; no body trace is supplied. -/
theorem body_complete {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment captured : Environment} {store middle finalStore : Store} {value argument : Value}
    {location : Location} {body : Expr}
    (argumentsEvaluated : Evaluates environment store arguments (.inRight .word argument) middle)
    (reference : environment[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : middle.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (completed : Evaluates environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    Evaluates (argument :: captured) middle body value finalStore := by
  have selected := OptionalCell.read_success reason
    (show Evaluates (argument :: environment) middle (.var (index + 1))
      (.cellRef (OptionalCell.cellType signature.functionType) location) middle from .var reference) read
  obtain ⟨_, sized⟩ := evaluation_has_size completed
  obtain ⟨_, _, following⟩ := sized.bind_success argumentsEvaluated
  obtain ⟨_, _, applied⟩ := following.bind_success selected
  obtain ⟨_, _, bodyEvaluation⟩ := applied.apply_body (.var rfl) (.var rfl)
  exact bodyEvaluation.sound

/-- Real installed environments, code and frame state. These observational
facts grant no source declaration or body semantics; those are in `Body`. -/
structure Installed {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {program : Program} (body : Body prepared values ambient.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (world : StoreTyping)
    (before : Dynamic.Heap) (store : Store) (callerEnvironment : Environment) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees before body.function.context.locals []
  captureLayout : EnvironmentsAgree embedding canonical captured
  captureTyped : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  frameLocation : Location
  canonicalReference : canonical[body.globals]? = some (.cellRef prepared.layout.frame.type frameLocation)
  capturedReference : captured[embedding base.globals.length]? = some (.cellRef prepared.layout.frame.type frameLocation)
  unmapped : frameLocation ∉ mapping
  frameTyped : world[frameLocation]? = some prepared.layout.frame.type
  current : NativeFrame
  currentGhost : GhostFrame
  caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current currentGhost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records
  globalIndex : Nat
  globalLocation : Location
  globalUnmapped : globalLocation ∉ mapping
  globalReference : callerEnvironment[globalIndex]? = some
    (.cellRef (OptionalCell.cellType body.named.signature.functionType) globalLocation)
  globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure body.named.signature.parameterType (LanguageResult.resultType body.named.signature.resultType)
      (body.code.rename embedding.lift) captured))

/-- Argument effects preserve the exact installed closure and both protected
administrative histories. Captured environment typing is weakened along the
actual world extension, including all non-source slots. -/
def Installed.extend {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {program : Program}
    {body : Body prepared values ambient.definitions program} {registry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {before after : Dynamic.Heap} {store futureStore : Store} {callerEnvironment : Environment}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMapping futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Installed functions body registry futureMapping futureWorld after futureStore callerEnvironment := by
  have frameBound := (List.getElem?_eq_some_iff.mp installed.caller.read).1
  have globalBound := (List.getElem?_eq_some_iff.mp installed.globalRead).1
  have frame := preserved installed.frameLocation installed.unmapped frameBound
  have global := preserved installed.globalLocation installed.globalUnmapped globalBound
  exact { installed with
    environments := installed.environments.extend maps worlds
    locals := installed.locals.mono metadata
    captureTyped := installed.captureTyped.weaken worlds
    unmapped := frame.1
    frameTyped := worlds.lookup installed.frameTyped
    caller := ⟨frame.2.trans installed.caller.read, installed.caller.history⟩
    snapshots := installed.snapshots.transport preserved
    globalUnmapped := global.1
    globalRead := global.2.trans installed.globalRead }

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program} (body : Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include extension uninitialized missing in
/-- The concrete parameter/body certificates close this body invocation after
the real argument effects. The only source execution premise is the particular
independent invocation being preserved. -/
theorem body_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (body.code.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have arity : body.function.parameters.length = arguments.length := by
    rw [body.parameters, List.length_map]; exact represented.length.1
  obtain ⟨environment, bound, allocated, trace⟩ := body.frame.trace_of_body body.extended arity executed
  obtain ⟨_, _, _, value, finalStore, finalMap, finalWorld, _, _, evaluation, result, finalHeaps,
    maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    NamedCalls.hook_preserves prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots allocated trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds,
    preserved, metadata, current, snapshots⟩

include extension uninitialized missing in
/-- Completed actual body execution constructs parameter allocation and the
independent invocation from the concrete lexical tree, with frame restoration. -/
theorem body_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
      (body.code.rename installed.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨_, _, _, environment, bound, outcome, after, finalMap, finalWorld, _, _, allocated, trace, result,
    finalHeaps, maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    NamedCalls.hook_reflects prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots executed
  exact ⟨outcome, after, finalMap, finalWorld, body.frame.body_of_trace body.extended allocated trace,
    result, finalHeaps, maps, worlds, preserved, metadata, current, snapshots⟩

variable {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (callerValid : CompatibleExpressionLiterals.ContextValid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionGeneral.Tree readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope ids (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd)
  (packedType : body.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Concrete General argument trees close all child meaning. Arguments are
evaluated before the global read; their first fault skips the body. The body
uses its actual static parameter/lexical certificates at the intervening heap. -/
theorem preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have argumentMeaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionGeneral.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionGeneral.preserves functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid unique callerUninitialized callerMissing
  cases execution with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      TypedDataExpressionSequence.preserves_fault children argumentMeaning environments heaps locals layout actualTyped failed
    have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
      (internalReason := reason) (packedType.symm ▸ argumentsEvaluation)
    have frameRead := (frame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
    refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata,
      ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport frame⟩
    simpa only [body.resultType] using
      (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (sourceType := body.function.resultType) (type := body.output) matched)
  | apply argumentsEvaluated bodyExecuted =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEvaluation, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
      TypedDataExpressionSequence.preserves_values children argumentMeaning environments heaps locals layout actualTyped argumentsEvaluated
    rw [nativeTypes] at represented
    let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    have related := values_arguments body.bindings represented
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, current, snapshots⟩ := body_preserves functions extension body uninitialized missing next related middleHeaps bodyExecuted
    have read := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: callerEnvironment) middleStore
        (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType body.named.signature.functionType) installed.globalLocation)
        middleStore from .var installed.globalReference) next.globalRead
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Every finite native call completion reconstructs its ordered source
argument trace and concrete independent named-body invocation. Neither child
evaluations nor a universal body preservation hypothesis are supplied. -/
theorem reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
        before ids body.sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨argumentValue, middleStore, argumentEvaluation⟩ := arguments_complete completed
  have argumentMeaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionGeneral.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionGeneral.reflects functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid callerUninitialized callerMissing
  obtain ⟨argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    TypedDataExpressionSequence.reflects children argumentMeaning environments heaps locals layout actualTyped argumentEvaluation
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
        (internalReason := reason) (packedType.symm ▸ argumentEvaluation)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
      have frameRead := (argumentFrame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
      refine ⟨.fault _, middle, middleMap, middleWorld, .argumentFault failed, ?_, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
        ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport argumentFrame⟩
      simpa only [body.resultType] using
        (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
          (sourceType := body.function.resultType) (type := body.output) matched)
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have related := values_arguments body.bindings represented
      have bodyEvaluation := body_complete argumentEvaluation installed.globalReference next.globalRead completed
      obtain ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, bodyMaps, bodyWorlds,
        bodyFrame, bodyMetadata, current, snapshots⟩ := body_reflects functions extension body uninitialized missing next related middleHeaps bodyEvaluation
      exact ⟨outcome, after, finalMap, finalWorld, .apply evaluatedArguments bodyTrace, result,
        finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Actual compiler success, independent source attribution and concrete
argument/body certificates close reflection at the emitted expression itself. -/
theorem accepted_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  rw [emitted, call_rename, ← located] at completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    reflects functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped completed
  exact ⟨outcome, after, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed trace,
    result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Preservation starts with this exact independently instantiated source body
and ordered argument trace. The actual accepted emitted expression is evaluated,
including argument faults and lexical body faults with their preceding writes. -/
theorem accepted_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    preserves functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped unique execution
  have completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore := by
    rw [emitted, call_rename, ← located]; exact evaluation
  exact ⟨value, finalStore, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed execution,
    completed, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

end Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
end
