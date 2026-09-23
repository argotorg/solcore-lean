import Solcore.Frontend.Expected
import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Syntax.Parser.Term

/- Parsed old/mapped creation, caller prefixes, complete raw calls and the Core
runner all execute before the owner-transported saved-lambda bridge is consumed. -/
set_option autoImplicit false
namespace Tests.ADR0315ParsedOwnerExpectedDataLambdaInvocations
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"ParsedOwnerSavedLambda",by decide⟩],by decide⟩⟩,index⟩
private def savedOwner := declaration 15
private def callerOwner := declaration 25
private def foreignOwner := declaration 915
private def lid (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner,index⟩
private def sid (index : Nat) := lid savedOwner index
private def cid (index : Nat) := lid callerOwner index
private def fid (index : Nat) := lid foreignOwner index
private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {owner with declarationIndex:=owner.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at modules indices ⊢
  exact ⟨modules,by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before,same⟩ := onto (declaration 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  simp [shift,declaration] at impossible

private def span (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id,start,stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨span file start stop,.identifier ⟨span file start stop,name⟩⟩
private def expectedLambda (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span file 0 17,.lambda (span file 0 3)
    ⟨span file 3 6,[⟨span file 4 5,.inferred ⟨span file 4 5,"p"⟩⟩]⟩ none
    ⟨span file 6 17,[⟨span file 7 16,.returnStmt
      (some (reference file 14 15 "p"))⟩]⟩⟩
private def expectedCall (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span file 0 4,.call (reference file 0 1 "f")
    ⟨span file 1 4,[reference file 2 3 "x"]⟩⟩
private def parseExact (filename text : String) (expected : Syntax.SourceFile → Syntax.Expr) :
    IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,filename⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      next.file==file && source.span==Syntax.SourceSpan.fullFile file &&
      source==expected file) "complete parsed AST/spans/EOF/diagnostics"
    return source
  | _ => throw (IO.userError "expression parser")

private def inputs : LocalTypeInputs := ⟨[
  ⟨"payload",sid 7,.unit⟩,⟨"noise",fid 31,.word⟩,⟨"payload",sid 2,.bool⟩],by decide⟩
private def payload : Core.Value :=
  .closure .bool .word (.var 1)
    [.cellRef .word 8,.hostFunction .callerAddress,
      .closure .unit .unit (.var 4) [.hostFunction .storageRead]]
private def environment : Resolved.Environment :=
  [(sid 7,payload),(fid 31,.word (Core.Word.ofNatModulo 99)),(sid 2,.bool false)]
private def store : Core.Store :=
  [.word (Core.Word.ofNatModulo 77),.cellRef .word 3,
    .hostFunction .storageWrite,payload]
private def captures := environment.map fun row => (row.1,RuntimeValue.ofCore row.2)
private def heap := store.map RuntimeValue.ofCore
private def mapId := ownerLocalIdMap shift
private def mappedInputs : LocalTypeInputs :=
  inputs.mapIds mapId (ownerLocalIdMap_injective shift shift_injective)
private def mappedEnvironment : Resolved.Environment := Resolved.LocalScope.mapIds mapId environment
private def callerNames : LocalNameTable :=
  [("f",cid 40),("x",cid 41),("f",fid 40)]
private def callerRows (saved : RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  [(cid 41,RuntimeValue.ofCore payload),(cid 40,saved),
    (cid 40,.sourceClosure (reference ⟨⟨.main,"noise.sol"⟩,"z"⟩ 0 1 "z") foreignOwner [] []),
    (fid 40,saved)]

private def exercise (source call : Syntax.Expr) : IO Unit := do
  match sourceShape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ none body⟩ =>
    have shape : SourceUnaryLambdaShape source parameter body := by
      rw [sourceShape]; exact .inferred
    match bodyShape : body, callShape : call with
    | ⟨_,[⟨_,.returnStmt (some result@⟨_,.identifier bodyName⟩)⟩]⟩,
        ⟨callSpan,.call ⟨calleeSpan,.identifier calleeName⟩
          ⟨argumentsSpan,[⟨argumentSpan,.identifier argumentName⟩]⟩⟩ =>
      if namesEqual : bodyName.value=parameter.value ∧ calleeName.value="f" ∧
          argumentName.value="x" then
        have gate : ClosedSourceDataBody body := by rw [bodyShape]; exact .expression .reference
        have sameIds : environment.ids=inputs.context.ids := rfl
        let inner := inputs.bindFresh savedOwner parameter.value .unit
        let mappedInner := mappedInputs.bindFresh (shift savedOwner) parameter.value .unit
        let expectedCore : Core.Expr := .lambda .unit .unit (.var 0)
        match oldCheckedRun : elaborateExpectedComputationLambda? elaborateLocalExpression? []
            savedOwner inputs source (.function .unit .unit),
          mappedCheckedRun : elaborateExpectedComputationLambda? elaborateLocalExpression? []
            (shift savedOwner) mappedInputs source (.function .unit .unit) with
        | some oldCore,some mappedCore =>
          if coresEqual : oldCore=expectedCore ∧ mappedCore=expectedCore then
            have checked : elaborateExpectedComputationLambda? elaborateLocalExpression? []
                savedOwner inputs source (.function .unit .unit)=some expectedCore :=
              coresEqual.1 ▸ oldCheckedRun
            check (elaborateComputationReturnTree? elaborateLocalExpression? [] savedOwner inner
                body==some (.var 0,.unit) &&
              elaborateComputationReturnTree? elaborateLocalExpression? [] (shift savedOwner)
                mappedInner body==some (.var 0,.unit) &&
              Resolved.freshLocalId savedOwner inputs.ids==sid 8 &&
              Resolved.freshLocalId (shift savedOwner) mappedInputs.ids==lid (shift savedOwner) 8)
              "actual old/mapped body checkers and owner-only fresh ID"
            let callee : Syntax.Expr := ⟨calleeSpan,.identifier calleeName⟩
            let argument : Syntax.Expr := ⟨argumentSpan,.identifier argumentName⟩
            let saved := RuntimeValue.sourceClosure source savedOwner inputs.names captures
            let mappedSaved := RuntimeValue.sourceClosure source (shift savedOwner)
              (LocalNameTable.mapIds mapId inputs.names)
              (mappedEnvironment.map fun row => (row.1,RuntimeValue.ofCore row.2))
            let oldRows := callerRows saved
            let mappedNames := LocalNameTable.mapIds mapId callerNames
            let mappedRows := mapRuntimeCapturedOwners shift oldRows
            let mappedHeap := heap.map (RuntimeValue.mapOwners shift)
            have mappedHeapEq : mappedHeap=heap := by
              simp only [mappedHeap,heap,mapRuntimeStoreOwners_ofCore]
            have bodyRaw : ClosedSourceBodyEvaluates savedOwner
                ((parameter.value,Resolved.freshLocalId savedOwner inputs.ids)::inputs.names)
                ((Resolved.freshLocalId savedOwner inputs.ids,RuntimeValue.ofCore payload)::captures)
                heap body (RuntimeValue.ofCore payload) heap := by
              rw [bodyShape]; exact .expression (.reference (namesEqual.1 ▸ .head) .head)
            have creationRaw : ClosedSourceExpressionEvaluates savedOwner inputs.names captures
                heap source saved heap := .creation shape
            have mappedCreationRaw : ClosedSourceExpressionEvaluates (shift savedOwner)
                (LocalNameTable.mapIds mapId inputs.names)
                (mappedEnvironment.map fun row => (row.1,RuntimeValue.ofCore row.2)) mappedHeap
                source mappedSaved mappedHeap := .creation shape
            have calleeRaw : ClosedSourceExpressionEvaluates callerOwner callerNames oldRows heap
                callee saved heap := .reference (namesEqual.2.1 ▸ .head) (.tail (by decide) .head)
            have argumentRaw : ClosedSourceExpressionEvaluates callerOwner callerNames oldRows heap
                argument (RuntimeValue.ofCore payload) heap :=
              .reference (namesEqual.2.2 ▸ .tail (by decide) .head) .head
            have callRaw : ClosedSourceExpressionEvaluates callerOwner callerNames oldRows heap call
                (RuntimeValue.ofCore payload) heap := by
              rw [callShape]; exact .call shape calleeRaw argumentRaw bodyRaw
            have mappedCalleeRaw : ClosedSourceExpressionEvaluates (shift callerOwner) mappedNames
                mappedRows mappedHeap callee mappedSaved mappedHeap := by
              simpa only [mappedNames,mappedRows,mappedHeap,saved,mappedSaved,captures,mapId,
                mappedEnvironment,RuntimeValue.mapOwners_sourceClosure,
                mapRuntimeCapturedOwners_ofCore] using calleeRaw.mapOwners shift shift_injective
            have mappedArgumentRaw : ClosedSourceExpressionEvaluates (shift callerOwner)
                mappedNames mappedRows mappedHeap argument (RuntimeValue.ofCore payload)
                mappedHeap := by
              simpa only [mappedNames,mappedRows,mappedHeap,mapId,RuntimeValue.mapOwners_ofCore] using
                argumentRaw.mapOwners shift shift_injective
            have mappedCallRaw : ClosedSourceExpressionEvaluates (shift callerOwner) mappedNames
                mappedRows mappedHeap call (RuntimeValue.ofCore payload) mappedHeap := by
              simpa only [mappedNames,mappedRows,mappedHeap,mapId,RuntimeValue.mapOwners_ofCore] using
                callRaw.mapOwners shift shift_injective
            match oldCreationRun : evaluateClosedSourceExpression? 1 savedOwner inputs.names
                captures heap source with
            | some (oldCreated,oldCreationFinal) =>
              have oldCreationEq :=
                (evaluateClosedSourceExpression?_sound oldCreationRun).deterministic creationRaw
              proof oldCreationEq
              match mappedCreationRun : evaluateClosedSourceExpression? 1 (shift savedOwner)
                  (LocalNameTable.mapIds mapId inputs.names)
                  (mappedEnvironment.map fun row => (row.1,RuntimeValue.ofCore row.2))
                  mappedHeap source with
              | some (mappedCreated,mappedCreationFinal) =>
                have mappedCreationEq :=
                  (evaluateClosedSourceExpression?_sound mappedCreationRun).deterministic
                    mappedCreationRaw
                proof mappedCreationEq
                match oldCalleeRun : evaluateClosedSourceExpression? 1 callerOwner callerNames
                    oldRows heap callee,
                  oldArgumentRun : evaluateClosedSourceExpression? 1 callerOwner callerNames
                    oldRows heap argument,
                  mappedCalleeRun : evaluateClosedSourceExpression? 1 (shift callerOwner)
                    mappedNames mappedRows mappedHeap callee,
                  mappedArgumentRun : evaluateClosedSourceExpression? 1 (shift callerOwner)
                    mappedNames mappedRows mappedHeap argument with
                | some (oldFn,oldCalleeStore),some (oldArg,oldBodyStore),
                    some (mappedFn,mappedCalleeStore),some (mappedArg,mappedBodyStore) =>
                  have oldFnEq :=
                    (evaluateClosedSourceExpression?_sound oldCalleeRun).deterministic calleeRaw
                  have oldArgEq :=
                    (evaluateClosedSourceExpression?_sound oldArgumentRun).deterministic argumentRaw
                  have mappedFnEq :=
                    (evaluateClosedSourceExpression?_sound mappedCalleeRun).deterministic
                      mappedCalleeRaw
                  have mappedArgEq :=
                    (evaluateClosedSourceExpression?_sound mappedArgumentRun).deterministic
                      mappedArgumentRaw
                  proof oldFnEq; proof oldArgEq; proof mappedFnEq; proof mappedArgEq
                  have mappedFnEval := evaluateClosedSourceExpression?_sound mappedCalleeRun
                  have mappedArgEval := evaluateClosedSourceExpression?_sound mappedArgumentRun
                  match oldRun : evaluateClosedSourceExpression? 3 callerOwner callerNames oldRows
                      heap call with
                  | some (oldValue,oldFinal) =>
                    have oldActual := evaluateClosedSourceExpression?_sound oldRun
                    proof (oldActual.deterministic callRaw)
                    match mappedRun : evaluateClosedSourceExpression? 3 (shift callerOwner)
                        mappedNames mappedRows mappedHeap call with
                    | some (mappedValue,mappedFinal) =>
                      have mappedActual := evaluateClosedSourceExpression?_sound mappedRun
                      proof (mappedActual.deterministic mappedCallRaw)
                      let core : Core.Expr := .apply (.var 0) (.var 1)
                      let coreEnvironment : List Core.Value :=
                        [.closure .unit .unit (.var 0) environment.values,payload]
                      match tooSmall : Core.runStateful 5 (.initial core coreEnvironment store) with
                      | .outOfFuel _ =>
                        match coreRun : Core.runStateful 6 (.initial core coreEnvironment store) with
                        | .done coreValue coreFinal =>
                          have coreEval := Core.runStateful_evaluation_sound coreRun
                          have functionEval : Core.Evaluates coreEnvironment store (.var 0)
                              (.closure .unit .unit (.var 0) environment.values) store := .var rfl
                          have argumentEval : Core.Evaluates coreEnvironment store (.var 1)
                              payload store := .var rfl
                          have beta : Core.Evaluates (payload::environment.values) store (.var 0)
                              coreValue coreFinal := by
                            change Core.Evaluates coreEnvironment store (.apply (.var 0) (.var 1))
                              coreValue coreFinal at coreEval
                            cases coreEval with
                            | apply f a b =>
                              obtain ⟨hf,hs⟩ := Core.evaluation_deterministic f functionEval
                              cases hf; cases hs
                              obtain ⟨ha,hs⟩ := Core.evaluation_deterministic a argumentEval
                              cases ha; cases hs; exact b
                          check (coreValue==payload && coreFinal==store)
                            "actual Core endpoint at exact 5/6 transition boundary"
                          have bridge {value final} :=
                            closedSourceExpectedDataLambda_invocation_mapOwners_core_iff
                              shift shift_injective (callerOwner:=callerOwner)
                              (callerNames:=callerNames) (callerCaptured:=oldRows)
                              (callee:=callee) (argument:=argument) (argumentValue:=payload)
                              shape gate checked sameIds
                              (by simpa only [mappedNames,mappedRows,mappedFnEq.1,mappedFnEq.2,
                                  mapId,callee,mappedSaved,saved,oldRows,mappedHeap,
                                  mappedEnvironment]
                                using mappedFnEval)
                              (by simpa only [mappedNames,mappedRows,mappedArgEq.1,mappedArgEq.2,
                                  mappedHeapEq,mapId,argument,saved,oldRows,mappedHeap,heap,
                                  mapRuntimeStoreOwners_ofCore]
                                using mappedArgEval)
                              (initialStore:=heap) (calleeStore:=heap) (bodyStore:=store)
                              (callSpan:=callSpan) (argumentsSpan:=argumentsSpan)
                              (actualValue:=value) (actualFinal:=final)
                          have mappedForBridge : ClosedSourceExpressionEvaluates
                              (shift callerOwner) mappedNames mappedRows mappedHeap call
                              mappedValue mappedFinal := mappedActual
                          have forward := (bridge (value:=mappedValue) (final:=mappedFinal)).2.2.mp
                            (by simpa only [mappedNames,mappedRows,mappedHeap,callShape,mapId,
                                oldRows,saved]
                              using mappedForBridge)
                          have endpoint : mappedValue=RuntimeValue.ofCore coreValue ∧
                              mappedFinal=coreFinal.map RuntimeValue.ofCore := by
                            obtain ⟨iv,ist,valueEq,storeEq,imageCore⟩ := forward
                            obtain ⟨valueCoreEq,storeCoreEq⟩ :=
                              Core.evaluation_deterministic imageCore beta
                            exact ⟨valueEq.trans (congrArg RuntimeValue.ofCore valueCoreEq),
                              storeEq.trans (congrArg (List.map RuntimeValue.ofCore) storeCoreEq)⟩
                          proof endpoint
                          proof ((bridge (value:=mappedValue) (final:=mappedFinal)).2.2.mpr
                            ⟨coreValue,coreFinal,endpoint.1,endpoint.2,beta⟩)
                          proof ((bridge (value:=RuntimeValue.ofCore coreValue)
                            (final:=coreFinal.map RuntimeValue.ofCore)).2.2.mpr
                              ⟨coreValue,coreFinal,rfl,rfl,beta⟩)
                          check (mappedValue.toCore?==some coreValue &&
                            mappedFinal.mapM RuntimeValue.toCore?==some coreFinal)
                            "project only after both mapped bridge directions"
                          proof shift_not_surjective
                        | _ => throw (IO.userError "Core six-transition completion")
                      | _ => throw (IO.userError "Core five-transition exhaustion")
                    | none => throw (IO.userError "mapped complete call depth three")
                  | none => throw (IO.userError "old complete call depth three")
                | _,_,_,_ => throw (IO.userError "actual old/mapped caller prefixes")
              | none => throw (IO.userError "actual mapped source-closure creation")
            | none => throw (IO.userError "actual old source-closure creation")
          else throw (IO.userError "old/mapped checked Core mismatch")
        | _,_ => throw (IO.userError "actual old/mapped expected-lambda checkers")
      else throw (IO.userError "parsed identifier spellings")
    | _,_ => throw (IO.userError "parsed body and saved call shapes")
  | _ => throw (IO.userError "parsed inferred unary source")

end Tests.ADR0315ParsedOwnerExpectedDataLambdaInvocations

open Tests.ADR0315ParsedOwnerExpectedDataLambdaInvocations in
def Tests.adr0315ParsedOwnerExpectedDataLambdaInvocationTests : IO Unit := do
  let source ← parseExact "adr0315-saved-lambda.sol" "lam(p){return p;}" expectedLambda
  let call ← parseExact "adr0315-saved-call.sol" "f(x)" expectedCall
  exercise source call
  IO.println "ADR0315 parsed owner-mapped saved data-lambda/Core image GREEN"
