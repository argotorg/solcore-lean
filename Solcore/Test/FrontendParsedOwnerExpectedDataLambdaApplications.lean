import Solcore.Frontend.Expected
import Solcore.Frontend.ClosedSource
import Solcore.Syntax.Parser.Term

/- The parser must produce a literal call(lambda,args), not a grouped callee.
Old and mapped checkers/runners and Core execution precede bridge use. -/
set_option autoImplicit false
namespace Tests.ADR0315ParsedOwnerExpectedDataLambdaApplications
open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedOwnerDataApplication", by decide⟩], by decide⟩⟩, 175⟩
private def sid (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def foreignOwner : Resolved.DeclarationId := { owner with declarationIndex := 901 }
private def foreign (index : Nat) : Resolved.LocalId := ⟨foreignOwner, index⟩
private def shift (declaration : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { declaration with declarationIndex := declaration.declarationIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before, same⟩ := onto { owner with declarationIndex := 0 }
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change before.declarationIndex + 5 = 0 at impossible
  omega

private def inputs : LocalTypeInputs :=
  ⟨[⟨"arg", sid 9, .unit⟩, ⟨"noise", foreign 700, .word⟩,
    ⟨"arg", foreign 701, .bool⟩], by decide⟩
private def environment (payload : Core.Value) : Resolved.Environment :=
  [(sid 9, payload), (foreign 700, .word (Core.Word.ofNatModulo 99)),
    (foreign 701, .bool false)]
private def up (environment : Resolved.Environment) :
    List (Resolved.LocalId × RuntimeValue) :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))

private def parse (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile :=
    ⟨⟨.main, "parsed-owner-expected-data-application.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
        source.span == Syntax.SourceSpan.fullFile file) "complete parse and source span"
      return source
  | _ => throw (IO.userError "expression parser")

private def text := "lam(x){return x;}(arg)"

private def exercise (payload : Core.Value) (store : Core.Store) : IO Unit := do
  let parsed ← parse text
  let environment := environment payload
  let mappedInputs := inputs.mapIds (ownerLocalIdMap shift)
    (ownerLocalIdMap_injective shift shift_injective)
  let mappedEnvironment := Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment
  have sameIds : environment.ids = inputs.context.ids := rfl
  have mappedSameIds : mappedEnvironment.ids = mappedInputs.context.ids := rfl
  match original : parsed with
  | ⟨callSpan, .call function ⟨argumentsSpan, [argument]⟩⟩ =>
    match functionShape : function, argumentShape : argument with
    | ⟨functionSpan, .lambda keywordSpan
        ⟨parametersSpan, [⟨parameterSpan, .inferred name⟩]⟩ none
        ⟨bodySpan, [⟨returnSpan,
          .returnStmt (some ⟨referenceSpan, .identifier returnedName⟩)⟩]⟩⟩,
      ⟨argumentSpan, .identifier argumentName⟩ =>
      let returned : Syntax.Expr := ⟨referenceSpan, .identifier returnedName⟩
      let body : Syntax.Block :=
        ⟨bodySpan, [⟨returnSpan, .returnStmt (some returned)⟩]⟩
      have sourceShape : SourceUnaryLambdaShape function name body := by
        rw [functionShape]
        exact .inferred
      have bodyGate : ClosedSourceDataBody body := .expression .reference
      have argumentGate : ClosedSourceDataExpression argument := by
        rw [argumentShape]
        exact .reference
      check (functionSpan.startByte == 0 && functionSpan.endByte == argumentsSpan.startByte &&
        callSpan.startByte == 0 && argumentSpan == argumentName.span &&
        keywordSpan.startByte == 0 && parametersSpan.contains parameterSpan &&
        bodySpan.contains returnSpan && name.value == "x" && returnedName.value == "x" &&
        argumentName.value == "arg")
        "ungrouped call(lambda,args), spellings, and retained spans"
      match checked : elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner
          inputs function (.function .unit .unit) with
      | some (.lambda .unit .unit bodyCore) =>
        have mappedChecked : elaborateExpectedComputationLambda? elaborateLocalExpression?
            [] (shift owner) mappedInputs function (.function .unit .unit) =
            some (.lambda .unit .unit bodyCore) := by
          simpa only [mappedInputs] using
            (elaborateExpectedComputationLambda?_mapOwner shift shift_injective
              elaborateLocalExpression?
              (elaborateLocalExpression?_mapIds (ownerLocalIdMap shift)
                (ownerLocalIdMap_injective shift shift_injective)) [] owner inputs function
              (.function .unit .unit)).trans checked
        check (elaborateExpectedComputationLambda? elaborateLocalExpression? []
          (shift owner) mappedInputs function (.function .unit .unit) ==
            some (.lambda .unit .unit bodyCore) &&
          elaborateComputationReturnTree? elaborateLocalExpression? [] (shift owner)
            (mappedInputs.bindFresh (shift owner) name.value .unit) body ==
              some (bodyCore, .unit)) "actual mapped expected/body checkers"
        proof checked; proof mappedChecked; proof sameIds; proof mappedSameIds
        match resolved : resolveLocalExpression? inputs.names argument with
        | some resolvedArgument =>
          let argumentResolution := resolveLocalExpression?_sound resolved
          match lowered : resolvedArgument.lower? environment.ids with
          | some argumentCore =>
            let argumentLowering := Resolved.Expr.lower?_sound lowered
            check (resolveLocalExpression?
              (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names) argument ==
                some (resolvedArgument.renameIds (ownerLocalIdMap shift)) &&
              (resolvedArgument.renameIds (ownerLocalIdMap shift)).lower?
                mappedEnvironment.ids == some argumentCore)
              "actual mapped argument resolution and lowering"
            match oldRun : evaluateClosedSourceExpression? 16 owner inputs.names
                (up environment) (store.map RuntimeValue.ofCore) parsed with
            | none => throw (IO.userError "old raw evaluator")
            | some (oldValue, oldFinal) =>
              let oldActual := evaluateClosedSourceExpression?_sound oldRun
              match mappedRun : evaluateClosedSourceExpression? 16 (shift owner)
                  (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
                  (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
                  (store.map RuntimeValue.ofCore) parsed with
              | none => throw (IO.userError "mapped raw evaluator")
              | some (mappedValue, mappedFinal) =>
                let mappedActual := evaluateClosedSourceExpression?_sound mappedRun
                let core := Core.Expr.apply (.lambda .unit .unit bodyCore) argumentCore
                match coreRun : Core.runStateful 64 (.initial core environment.values store) with
                | .done coreValue coreFinal =>
                  let actualCore := Core.runStateful_evaluation_sound coreRun
                  have oldImage {value finalStore} :=
                    closedSourceExpectedDataLambda_application_core_iff sourceShape bodyGate checked
                      sameIds argumentGate argumentResolution argumentLowering
                      (callSpan := callSpan) (argumentsSpan := argumentsSpan)
                      (initialStore := store) (actualValue := value) (actualFinal := finalStore)
                  have oldForward := (oldImage (value := oldValue) (finalStore := oldFinal)).mp
                    (by simpa only [original, up] using oldActual)
                  have mappedStages {value finalStore} :=
                    closedSourceExpectedDataLambda_application_mapOwners_core_iff
                      shift shift_injective sourceShape bodyGate checked sameIds argumentGate
                      argumentResolution argumentLowering (callSpan := callSpan)
                      (argumentsSpan := argumentsSpan) (initialStore := store)
                      (actualValue := value) (actualFinal := finalStore)
                  let mappedImage :=
                    (mappedStages (value := mappedValue) (finalStore := mappedFinal)).2.2.2.2
                  have mappedForward := mappedImage.mp
                    (by simpa only [original] using mappedActual)
                  have endpoint : mappedValue = RuntimeValue.ofCore coreValue ∧
                      mappedFinal = coreFinal.map RuntimeValue.ofCore := by
                    obtain ⟨imageValue, imageStore, valueEq, storeEq, imageCore⟩ := mappedForward
                    obtain ⟨sameValue, sameStore⟩ :=
                      Core.evaluation_deterministic imageCore actualCore
                    exact ⟨valueEq.trans (congrArg RuntimeValue.ofCore sameValue),
                      storeEq.trans (congrArg (List.map RuntimeValue.ofCore) sameStore)⟩
                  proof oldForward; proof endpoint
                  proof (mappedImage.mpr
                    ⟨coreValue, coreFinal, endpoint.1, endpoint.2, actualCore⟩)
                  proof ((mappedStages (value := RuntimeValue.ofCore coreValue)
                    (finalStore := coreFinal.map RuntimeValue.ofCore)).2.2.2.2.mpr
                      ⟨coreValue, coreFinal, rfl, rfl, actualCore⟩)
                  check (mappedValue.toCore? == some coreValue &&
                    mappedFinal.mapM RuntimeValue.toCore? == some coreFinal &&
                    oldValue.toCore? == some coreValue &&
                    oldFinal.mapM RuntimeValue.toCore? == some coreFinal)
                    "old/mapped projections after both mapped iff directions"
                | _ => throw (IO.userError "Core runner")
          | none => throw (IO.userError "old argument lowering")
        | none => throw (IO.userError "old argument resolution")
      | _ => throw (IO.userError "old expected checker")
    | _, _ => throw (IO.userError "inferred lambda and reference argument")
  | _ => throw (IO.userError "actual ungrouped call(lambda,args) AST")

end Tests.ADR0315ParsedOwnerExpectedDataLambdaApplications

open Solcore Tests.ADR0315ParsedOwnerExpectedDataLambdaApplications in
def Tests.adr0315ParsedOwnerExpectedDataLambdaApplicationTests : IO Unit := do
  proof shift_not_surjective
  let payload := Core.Value.closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef .unit 700,
      .closure .bool .unit (.var 5) [.hostFunction .callerAddress]]
  let store : Core.Store :=
    [.cellRef (.function .unit .word) 900, .hostFunction .storageRead, payload, .unit]
  check (!store.isEmpty && inputs.names[0]?.map Prod.fst == some "arg" &&
    inputs.names[2]?.map Prod.fst == some "arg") "nonempty store and duplicate/foreign rows"
  exercise payload store
  IO.println "ADR0315 parsed ungrouped owner-mapped data-lambda application GREEN"
