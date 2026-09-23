import Solcore.Frontend.Computation
import Solcore.Core.ExactFuelProperties

/-! An explicitly artificial nondeterministic child tests generic proof premises.
It is not source-language elaboration, a checker graph or a runtime safety claim. -/
set_option autoImplicit false
namespace Tests.FrontendComputationArgumentBoundaries
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],.bool)]
private def parameters (s : Syntax.SourceSpan) : List Syntax.FunctionParameter :=
  [⟨s,.typed none ⟨s,"x"⟩ (named s "A")⟩,⟨s,.typed none ⟨s,"y"⟩ (named s "B")⟩]
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"y"⟩⟩
private def entry (s : Syntax.SourceSpan) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"artificialChoices"⟩,none,⟨s,parameters s⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s "B"]⟩⟩,none⟩,⟨s,[⟨s,.returnStmt (some (ref s))⟩]⟩⟩⟩
private def Choice (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop := (∃ b,core=.bool b) ∧ type=.bool
private def staticInputs (o : Resolved.DeclarationId) (a : Core.Ty) :=
  (LocalTypeInputs.empty.bindFresh o "x" a).bindFresh o "y" .bool
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool,.bool b,.bool⟩
private def actualInputs (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :=
  (LocalInputs.empty.bindFresh o "x" arg.type arg.value arg.valueTyped).bindFresh o "y" .bool (.bool y) .bool
private def compiled (o : Resolved.DeclarationId) (a : Core.Ty) (selected : Bool) : CompiledRuntimeFunction :=
  ⟨staticInputs o a,.bool selected,.bool⟩
private def prepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y selected : Bool) : PreparedRuntimeFunction :=
  ⟨actualInputs o arg y,.bool selected,.bool⟩
private theorem header (s : Syntax.SourceSpan) (a : Core.Ty) :
    RuntimeFunctionHeader (types a) (entry s).value.signature .bool :=
  ⟨rfl,rfl,rfl,rfl,.single (.named (.tail (by change (["A"] : List String)≠["B"]; decide) .head))⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RuntimeParametersDeclare (types a) o (parameters s) (staticInputs o a) :=
  .cons (.named .head) (by simp)
    (.cons (.named (.tail (by change (["A"] : List String)≠["B"]; decide) .head))
      (by simp [LocalTypeInputs.names,LocalTypeInputs.bindFresh,LocalTypeInputs.empty]) .nil)
private theorem bound (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :
    RuntimeParametersBind (types arg.type) o (parameters s) [arg,boolArg y] (actualInputs o arg y) :=
  .cons (.named .head) (by simp)
    (.cons (.named (.tail (by change (["A"] : List String)≠["B"]; decide) .head))
      (by simp [LocalInputs.names,LocalInputs.bindFresh,LocalInputs.empty]) .nil)
private theorem compilation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) (selected : Bool) :
    ComputationFunctionCompiles Choice (types a) o (entry s) (compiled o a selected) :=
  ⟨header s a,declared s o a,.expression ⟨⟨selected,rfl⟩,rfl⟩⟩
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (arg : TypedRuntimeArgument) (y selected : Bool) :
    ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] (prepared o arg y selected) :=
  ⟨header s arg.type,bound s o arg y,.expression ⟨⟨selected,rfl⟩,rfl⟩⟩

theorem static_compilation_in_this_artificial_model_requires_no_argument_inhabitant
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) (selected : Bool) :
    ComputationFunctionCompiles Choice (types a) o (entry s) (compiled o a selected) :=
  compilation s o a selected
theorem supplied_values_reconstruct_the_exact_independently_bound_record
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y selected : Bool) :
    ∃ p, ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] p ∧
      p=prepared o arg y selected ∧ p.toCompiled=compiled o arg.type selected ∧
      p.inputs.environment.values=[.bool y,arg.value] := by
  obtain ⟨p,evidence,erased⟩ := (compilation s o arg.type selected).prepare_arguments [arg,boolArg y] rfl
  have same : p=prepared o arg y selected :=
    evidence.unique_of_toCompiled_eq (preparation s o arg y selected) erased
  exact ⟨p,evidence,same,erased,evidence.argument_values⟩
theorem erasure_and_reconstruction_keep_the_same_fixed_compiled_projection
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty)
    (args : List TypedRuntimeArgument) (selected : Bool) :
    (∃ p, ComputationFunctionPrepares Choice (types a) o (entry s) args p ∧
      p.toCompiled=compiled o a selected) ↔ args.map (·.type)=[a,.bool] := by
  constructor
  · intro evidence
    exact (computationFunctionPrepares_toCompiled_iff.mp evidence).2
  · intro matching
    exact computationFunctionPrepares_toCompiled_iff.mpr ⟨compilation s o a selected,matching⟩
theorem same_typed_value_permutation_changes_the_prepared_record_not_its_projection
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (selected : Bool) :
    let left := prepared o (boolArg true) false selected
    let right := prepared o (boolArg false) true selected
    ComputationFunctionPrepares Choice (types .bool) o (entry s) [boolArg true,boolArg false] left ∧
    ComputationFunctionPrepares Choice (types .bool) o (entry s) [boolArg false,boolArg true] right ∧
    left.toCompiled=right.toCompiled ∧ left≠right := by
  refine ⟨preparation s o (boolArg true) false selected,preparation s o (boolArg false) true selected,rfl,?_⟩
  intro same
  have values := congrArg (fun p : PreparedRuntimeFunction => p.inputs.environment.values) same
  change [Core.Value.bool false,.bool true]=[.bool true,.bool false] at values
  cases values
theorem arbitrary_child_elaboration_does_not_make_compilation_or_preparation_unique
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :
    let left := prepared o arg y false
    let right := prepared o arg y true
    ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] left ∧
    ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] right ∧
    ComputationFunctionCompiles Choice (types arg.type) o (entry s) left.toCompiled ∧
    ComputationFunctionCompiles Choice (types arg.type) o (entry s) right.toCompiled ∧
    left.inputs=right.inputs ∧ left.toCompiled≠right.toCompiled ∧
    ∀ store k, Core.Steps 1 ⟨.eval left.core left.inputs.environment.values,k,store⟩ ⟨.ret (.bool false),k,store⟩ ∧
      Core.Steps 1 ⟨.eval right.core right.inputs.environment.values,k,store⟩ ⟨.ret (.bool true),k,store⟩ := by
  have left := preparation s o arg y false
  have right := preparation s o arg y true
  refine ⟨left,right,left.compiles,right.compiles,rfl,?_,?_⟩
  · intro same
    have cores := congrArg CompiledRuntimeFunction.core same
    change Core.Expr.bool false=.bool true at cores
    cases cores
  · intro store k; exact ⟨.cons .bool .refl,.cons .bool .refl⟩
theorem this_nondeterministic_interface_cannot_be_an_exact_optional_checker_graph :
    ¬ ∃ checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty),
      ∀ table context source core type, checkChild table context source=some (core,type) ↔ Choice table context source core type := by
  rintro ⟨checkChild,correct⟩
  let source := ref ⟨⟨.main,"artificial-choice.sol"⟩,0,0⟩
  have left := (correct [] [] source (.bool false) .bool).mpr ⟨⟨false,rfl⟩,rfl⟩
  have right := (correct [] [] source (.bool true) .bool).mpr ⟨⟨true,rfl⟩,rfl⟩
  have impossible := Option.some.inj (left.symm.trans right)
  cases impossible
private def wordArg : TypedRuntimeArgument := ⟨.word,.word (Core.Word.ofNatModulo 14),.word⟩
theorem wrong_arity_and_reversed_distinct_types_have_no_fixed_prepared_projection
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (selected : Bool) :
    (¬ ∃ p, ComputationFunctionPrepares Choice (types .word) o (entry s) [] p ∧
      p.toCompiled=compiled o .word selected) ∧
    (¬ ∃ p, ComputationFunctionPrepares Choice (types .word) o (entry s) [boolArg true,wordArg] p ∧
      p.toCompiled=compiled o .word selected) := by
  constructor
  · intro evidence
    have impossible := (erasure_and_reconstruction_keep_the_same_fixed_compiled_projection s o .word [] selected).mp evidence
    cases impossible
  · intro evidence
    have impossible := (erasure_and_reconstruction_keep_the_same_fixed_compiled_projection s o .word [boolArg true,wordArg] selected).mp evidence
    cases impossible
theorem a_matching_type_list_does_not_validate_a_hand_built_compiled_record
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :
    let fake : CompiledRuntimeFunction := {(compiled o arg.type false) with returnType := .unit}
    [arg,boolArg y].map (·.type)=fake.inputs.context.values.reverse ∧
    ¬ ∃ p, ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] p ∧ p.toCompiled=fake := by
  refine ⟨rfl,?_⟩
  intro evidence
  have bad := (computationFunctionPrepares_toCompiled_iff.mp evidence).1
  have impossible := bad.header.type_unique (header s arg.type)
  change Core.Ty.unit=.bool at impossible
  cases impossible
end Tests.FrontendComputationArgumentBoundaries
