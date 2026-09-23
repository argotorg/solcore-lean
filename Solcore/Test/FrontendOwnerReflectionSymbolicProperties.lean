import Solcore.Frontend.ClosedSource

/- Independent originals and exact runner recursion precede reflection. Arbitrary
mixed payloads, duplicate rows, annotations and stores require no runtime typing. -/
set_option autoImplicit false
namespace Tests.OwnerReflectionSymbolic
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (p : Syntax.Identifier) : Syntax.Expr := ⟨p.span,.identifier p⟩
private def groups (s : Syntax.SourceSpan) : Nat → Syntax.Expr → Syntax.Expr
  | 0,e => e
  | n+1,e => ⟨s,.group (groups s n e)⟩
private def block (p : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) : Syntax.Block :=
  ⟨p.span,[⟨p.span,.letDecl p annotation (some (ref p))⟩,
    ⟨p.span,.returnStmt (some (groups p.span n (ref p)))⟩]⟩
private def call (f x : Syntax.Identifier) : Syntax.Expr := ⟨f.span,.call (ref f) ⟨x.span,[ref x]⟩⟩
private theorem group_original {o ns cs st e v fin} (s : Syntax.SourceSpan) (n : Nat)
    (original : E o ns cs st e v fin) : E o ns cs st (groups s n e) v fin := by
  induction n with
  | zero => exact original
  | succ n ih => exact .group ih
private theorem group_run (n budget : Nat) (o ns cs st p id v)
    (named : LocalNameTable.Lookup ns p.value id) (found : Resolved.LocalScope.Lookup cs id v) :
    evaluateClosedSourceExpression? budget o ns cs st (groups p.span n (ref p)) =
      if n+1 ≤ budget then some (v,st) else none := by
  induction n generalizing budget with
  | zero => cases budget <;> simp [groups,ref,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget => simpa only [groups,evaluateClosedSourceExpression?,Nat.add_le_add_iff_right] using ih budget
private theorem body_original (o ns cs st p id v annotation n) :
    B o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n) v st := by
  have initial : E o ((p.value,id)::ns) ((id,v)::cs) st (ref p) v st := .reference .head .head
  have tail : B o ((p.value,Resolved.freshLocalId o (((p.value,id)::ns).map Prod.snd))::(p.value,id)::ns)
      ((Resolved.freshLocalId o (((p.value,id)::ns).map Prod.snd),v)::(id,v)::cs) st
      ⟨p.span,[⟨p.span,.returnStmt (some (groups p.span n (ref p)))⟩]⟩ v st :=
    .expression (group_original _ _ (.reference .head .head))
  cases annotation with
  | none => exact .inferred initial tail
  | some _ => exact .binding initial tail
private theorem body_run (n budget : Nat) (o ns cs st p id v annotation) :
    evaluateClosedSourceBody? budget o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n) =
      if n+3 ≤ budget then some (v,st) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceBody?]
  | succ budget =>
    cases budget with
    | zero => simp [block,ref,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
    | succ budget =>
      simp only [block,ref,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
        LocalNameTable.lookup?,Resolved.LocalScope.lookup?,↓reduceIte,bind,Option.bind_some,pure]
      have bound : n+3 ≤ budget+1+1 ↔ n+1≤budget := by omega
      simpa only [ref,bound] using
        group_run n budget o _ _ st p _ v LocalNameTable.Lookup.head Resolved.LocalScope.Lookup.head
private def Certificate (original : V → List V → Prop) (before after : Nat → Option (V × List V))
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (v : V) (st : List V) (depth : Nat) : Prop :=
  ∃ recovered final, original recovered final ∧ recovered=v ∧ final=st ∧
    ∃ required, required=depth ∧ 0<required ∧ ∀ budget,
      before budget=(if required≤budget then some (recovered,final) else none) ∧
      after budget=(if required≤budget then some (recovered.mapOwners mapping,final.map (RuntimeValue.mapOwners mapping)) else none)
private theorem body_certificate (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    {o ns cs st source v h} (positive : 0<h) (old : B o ns cs st source v st)
    (mapped : B (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns) (mapRuntimeCapturedOwners m cs)
      (st.map (RuntimeValue.mapOwners m)) source (v.mapOwners m) (st.map (RuntimeValue.mapOwners m)))
    (run : ∀ k, evaluateClosedSourceBody? k o ns cs st source=if h≤k then some (v,st) else none)
    (actual : evaluateClosedSourceBody? h (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=some (v.mapOwners m,st.map (RuntimeValue.mapOwners m))) :
    Certificate (B o ns cs st source) (fun k => evaluateClosedSourceBody? k o ns cs st source)
      (fun k => evaluateClosedSourceBody? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
        (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source) m v st h := by
  obtain ⟨pre,out,original,_,_⟩ := (ClosedSourceBodyEvaluates.mapOwners_iff_exists m inj).mp mapped
  have explicitOriginal := (ClosedSourceBodyEvaluates.mapOwners_iff m inj).mp mapped
  have endpoints := original.deterministic old
  obtain ⟨finite,finiteStore,ran,_,_⟩ := (evaluateClosedSourceBody?_mapOwners_some_iff_exists m inj).mp actual
  have finiteOriginal := evaluateClosedSourceBody?_sound ran
  have finiteEndpoints := finiteOriginal.deterministic explicitOriginal
  obtain ⟨required,pos,cutoff⟩ := finiteOriginal.mapOwners_exact_depth_threshold m inj
  have low : evaluateClosedSourceBody? (h-1) (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=none :=
    (evaluateClosedSourceBody?_mapOwners_none_iff m inj _ _ _ _ _ _).mpr (by rw [run,if_neg (by omega)])
  have upper : required≤h := by
    by_cases yes : required≤h
    · exact yes
    · have eqn := (cutoff h).1
      rw [run,if_pos (Nat.le_refl _),if_neg yes] at eqn
      cases eqn
  have lower : h≤required := by
    by_cases yes : h≤required
    · exact yes
    · have eqn := (cutoff (h-1)).2
      rw [low,if_pos (by omega)] at eqn
      cases eqn
  refine ⟨pre,out,original,endpoints.1,endpoints.2,required,by omega,pos,?_⟩
  intro k
  simpa only [endpoints.1,endpoints.2,finiteEndpoints.1,finiteEndpoints.2] using cutoff k
private theorem expression_certificate (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    {o ns cs st source v h} (positive : 0<h) (old : E o ns cs st source v st)
    (mapped : E (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns) (mapRuntimeCapturedOwners m cs)
      (st.map (RuntimeValue.mapOwners m)) source (v.mapOwners m) (st.map (RuntimeValue.mapOwners m)))
    (run : ∀ k, evaluateClosedSourceExpression? k o ns cs st source=if h≤k then some (v,st) else none)
    (actual : evaluateClosedSourceExpression? h (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=some (v.mapOwners m,st.map (RuntimeValue.mapOwners m))) :
    Certificate (E o ns cs st source) (fun k => evaluateClosedSourceExpression? k o ns cs st source)
      (fun k => evaluateClosedSourceExpression? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
        (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source) m v st h := by
  obtain ⟨pre,out,original,_,_⟩ := (ClosedSourceExpressionEvaluates.mapOwners_iff_exists m inj).mp mapped
  have explicitOriginal := (ClosedSourceExpressionEvaluates.mapOwners_iff m inj).mp mapped
  have endpoints := original.deterministic old
  obtain ⟨finite,finiteStore,ran,_,_⟩ := (evaluateClosedSourceExpression?_mapOwners_some_iff_exists m inj).mp actual
  have finiteOriginal := evaluateClosedSourceExpression?_sound ran
  have finiteEndpoints := finiteOriginal.deterministic explicitOriginal
  obtain ⟨required,pos,cutoff⟩ := finiteOriginal.mapOwners_exact_depth_threshold m inj
  have low : evaluateClosedSourceExpression? (h-1) (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=none :=
    (evaluateClosedSourceExpression?_mapOwners_none_iff m inj _ _ _ _ _ _).mpr (by rw [run,if_neg (by omega)])
  have upper : required≤h := by
    by_cases yes : required≤h
    · exact yes
    · have eqn := (cutoff h).1
      rw [run,if_pos (Nat.le_refl _),if_neg yes] at eqn
      cases eqn
  have lower : h≤required := by
    by_cases yes : h≤required
    · exact yes
    · have eqn := (cutoff (h-1)).2
      rw [low,if_pos (by omega)] at eqn
      cases eqn
  refine ⟨pre,out,original,endpoints.1,endpoints.2,required,by omega,pos,?_⟩
  intro k
  simpa only [endpoints.1,endpoints.2,finiteEndpoints.1,finiteEndpoints.2] using cutoff k

theorem fresh_body_recovers_complete_preimage
    (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    (o ns cs st p id v annotation n) :
    Certificate (B o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n))
      (fun k => evaluateClosedSourceBody? k o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n))
      (fun k => evaluateClosedSourceBody? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ((p.value,id)::ns))
        (mapRuntimeCapturedOwners m ((id,v)::cs)) (st.map (RuntimeValue.mapOwners m)) (block p annotation n)) m v st (n+3) := by
  have old := body_original o ns cs st p id v annotation n
  have mapped := body_original (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
    (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) p (ownerLocalIdMap m id) (v.mapOwners m) annotation n
  have actual := body_run n (n+3) (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
    (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) p (ownerLocalIdMap m id) (v.mapOwners m) annotation
  apply body_certificate m inj (by omega) old
    (by simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons] using mapped)
    (fun k => body_run n k o ns cs st p id v annotation)
  simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons,if_pos (Nat.le_refl _)] using actual

private theorem call_original {o ns cs st source savedOwner savedNames savedCaptured p annotation n f x fi xi v}
    (shape : SourceUnaryLambdaShape source p (block p annotation n))
    (nf : LocalNameTable.Lookup ns f.value fi)
    (ff : Resolved.LocalScope.Lookup cs fi (.sourceClosure source savedOwner savedNames savedCaptured))
    (nx : LocalNameTable.Lookup ns x.value xi) (fx : Resolved.LocalScope.Lookup cs xi v) :
    E o ns cs st (call f x) v st :=
  .call shape (.reference nf ff) (.reference nx fx)
    (body_original savedOwner savedNames savedCaptured st p _ v annotation n)
private theorem call_run {o ns cs st source savedOwner savedNames savedCaptured p annotation n f x fi xi v}
    (shape : SourceUnaryLambdaShape source p (block p annotation n))
    (nf : LocalNameTable.Lookup ns f.value fi)
    (ff : Resolved.LocalScope.Lookup cs fi (.sourceClosure source savedOwner savedNames savedCaptured))
    (nx : LocalNameTable.Lookup ns x.value xi) (fx : Resolved.LocalScope.Lookup cs xi v) (budget : Nat) :
    evaluateClosedSourceExpression? budget o ns cs st (call f x)=if n+4≤budget then some (v,st) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
    cases budget with
    | zero => simp [call,ref,evaluateClosedSourceExpression?]
    | succ budget =>
      simp only [call,ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr nf,
        LocalNameTable.lookup?_iff.mpr nx,Resolved.LocalScope.lookup?_iff.mpr ff,
        Resolved.LocalScope.lookup?_iff.mpr fx,bind,Option.bind_some,pure,sourceUnaryLambdaShape?_iff.mpr shape]
      have bound : n+4≤budget+1+1 ↔ n+3≤budget+1 := by omega
      simpa only [bound] using body_run n (budget+1) savedOwner savedNames savedCaptured st p _ v annotation

theorem saved_call_recovers_complete_preimage
    (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    {o ns cs st source savedOwner savedNames savedCaptured p annotation n f x fi xi v}
    (creationStore : List V) (shape : SourceUnaryLambdaShape source p (block p annotation n))
    (nf : LocalNameTable.Lookup ns f.value fi)
    (ff : Resolved.LocalScope.Lookup cs fi (.sourceClosure source savedOwner savedNames savedCaptured))
    (nx : LocalNameTable.Lookup ns x.value xi) (fx : Resolved.LocalScope.Lookup cs xi v) :
    E savedOwner savedNames savedCaptured creationStore source
      (.sourceClosure source savedOwner savedNames savedCaptured) creationStore ∧
    E (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames) (mapRuntimeCapturedOwners m savedCaptured)
      (creationStore.map (RuntimeValue.mapOwners m)) source
      (.sourceClosure source (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames)
        (mapRuntimeCapturedOwners m savedCaptured)) (creationStore.map (RuntimeValue.mapOwners m)) ∧
    Certificate (E o ns cs st (call f x)) (fun k => evaluateClosedSourceExpression? k o ns cs st (call f x))
      (fun k => evaluateClosedSourceExpression? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
        (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) (call f x)) m v st (n+4) := by
  have creation : E savedOwner savedNames savedCaptured creationStore source
      (.sourceClosure source savedOwner savedNames savedCaptured) creationStore := .creation shape
  have mappedCreation : E (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames)
      (mapRuntimeCapturedOwners m savedCaptured) (creationStore.map (RuntimeValue.mapOwners m)) source
      (.sourceClosure source (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames)
        (mapRuntimeCapturedOwners m savedCaptured)) (creationStore.map (RuntimeValue.mapOwners m)) := .creation shape
  have old : E o ns cs st (call f x) v st := call_original shape nf ff nx fx
  have nfm := (LocalNameTable.lookup_mapIds_iff (ownerLocalIdMap m) (ownerLocalIdMap_injective m inj)).mpr nf
  have nxm := (LocalNameTable.lookup_mapIds_iff (ownerLocalIdMap m) (ownerLocalIdMap_injective m inj)).mpr nx
  have ffm := mapRuntimeCapturedOwners_lookup m inj ff
  simp only [RuntimeValue.mapOwners_sourceClosure] at ffm
  have fxm := mapRuntimeCapturedOwners_lookup m inj fx
  have mapped : E (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns) (mapRuntimeCapturedOwners m cs)
      (st.map (RuntimeValue.mapOwners m)) (call f x) (v.mapOwners m) (st.map (RuntimeValue.mapOwners m)) :=
    call_original shape nfm ffm nxm fxm
  have actual := call_run (o:=m o) (st:=st.map (RuntimeValue.mapOwners m)) shape nfm ffm nxm fxm (n+4)
  refine ⟨creation,mappedCreation,expression_certificate m inj (by omega) old mapped (call_run shape nf ff nx fx) ?_⟩
  simpa only [if_pos (Nat.le_refl _)] using actual

private def owner (i : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"Reflection",by decide⟩],by decide⟩⟩,i⟩
private def fixtureSavedNames : LocalNameTable := [("p",⟨owner 1,40⟩),("p",⟨owner 3,40⟩),("p",⟨owner 1,40⟩)]
private theorem mixed_saved_fixture (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    (s : Syntax.SourceSpan) (parameterAnnotation bindingAnnotation : Option Syntax.TypeExpr) (opaqueCore : Core.Value) (n : Nat) :
    ∃ required : Nat, required=n+4 ∧ 0<required ∧
      Resolved.freshLocalId (owner 1) (fixtureSavedNames.map Prod.snd)=⟨owner 1,41⟩ ∧
      Resolved.freshLocalId (owner 1) (⟨owner 1,41⟩::fixtureSavedNames.map Prod.snd)=⟨owner 1,42⟩ := by
  let p : Syntax.Identifier := ⟨s,"p"⟩
  let parameter : Syntax.LambdaParameter := ⟨s,match parameterAnnotation with
    | none => .inferred p | some ty => .typed none p ty⟩
  let source : Syntax.Expr := ⟨s,.lambda s ⟨s,[parameter]⟩ none (block p bindingAnnotation n)⟩
  have shape : SourceUnaryLambdaShape source p (block p bindingAnnotation n) := by
    cases parameterAnnotation <;> first | exact .inferred | exact .typed
  let savedNames := fixtureSavedNames
  let nested : V := .coreClosure .unit .word (.var 17)
    [.sourceClosure source (owner 3) [("p",⟨owner 2,9⟩)]
      [(⟨owner 2,9⟩,.cellRef .word 77),(⟨owner 2,9⟩,.ofCore opaqueCore)],.ofCore opaqueCore]
  let savedCaptured : Resolved.LocalScope V :=
    [(⟨owner 3,40⟩,nested),(⟨owner 1,41⟩,.cellRef .word 800),(⟨owner 1,42⟩,.bool false),
      (⟨owner 1,40⟩,nested),(⟨owner 1,40⟩,.unit)]
  let saved : V := .sourceClosure source (owner 1) savedNames savedCaptured
  let arg : V := .pair nested (.pair (.ofCore opaqueCore) (.cellRef .word 78))
  let names : LocalNameTable := [("f",⟨owner 2,1⟩),("x",⟨owner 2,2⟩),("f",⟨owner 3,1⟩),("x",⟨owner 2,2⟩)]
  let captured : Resolved.LocalScope V := [(⟨owner 3,1⟩,.unit),(⟨owner 2,1⟩,saved),(⟨owner 2,2⟩,arg),
    (⟨owner 2,1⟩,.bool false),(⟨owner 2,2⟩,.unit)]
  have fresh : Resolved.freshLocalId (owner 1) (savedNames.map Prod.snd)=⟨owner 1,41⟩ := by decide
  have next : Resolved.freshLocalId (owner 1) (⟨owner 1,41⟩::savedNames.map Prod.snd)=⟨owner 1,42⟩ := by decide
  have result := saved_call_recovers_complete_preimage m inj (o:=owner 2) (ns:=names) (cs:=captured)
    (st:=[arg,.ofCore opaqueCore,.cellRef .word 900]) (f:=⟨s,"f"⟩) (x:=⟨s,"x"⟩) [nested] shape
    LocalNameTable.Lookup.head (Resolved.LocalScope.Lookup.tail (by decide) .head)
    (LocalNameTable.Lookup.tail (by change "f" ≠ "x"; decide) .head)
    (Resolved.LocalScope.Lookup.tail (by decide) (.tail (by decide) .head))
  obtain ⟨_,_,_,_,_,_,_,required,same,positive,_⟩ := result
  exact ⟨required,same,positive,fresh,next⟩

end Tests.OwnerReflectionSymbolic
