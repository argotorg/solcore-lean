import Solcore.Frontend.SourceCoreCompatibleValues
import Solcore.Core.Safety

/-! Structural native output shapes for the owned public codec. Metadata is
looked up in the actual boundary registry. Function leaves retain native
world typing. A mapping default is the pure default of its original raw
value type; the shape contains no decoding or export-success hypothesis. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCorePublicOutputShapes
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Registry := SourceCoreRawMetadata.Registry
abbrev DataValue := SourceCoreDataValues.Value
abbrev runtimeType := SourceCoreRawMetadata.runtimeType

def pack : List Core.Value → Core.Value
  | [] => .unit
  | [value] => value
  | value :: values => .pair value (pack values)

mutual
  /-- Data carriers produced by the pure default operation. In particular,
  mapping defaults contain no entries and cannot hide function leaves. -/
  inductive DefaultData (checked : Checked) (registry : Registry) : Ty → DataValue → Core.Value → Prop where
    | unit : DefaultData checked registry .unit .unit .unit
    | bool (value : Bool) : DefaultData checked registry .bool (.bool value) (.bool value)
    | word (value : Core.Word) : DefaultData checked registry .word (.word value) (.word value)
    | integer (value : Int) : DefaultData checked registry .integer (.integer value) (.integer value)
    | product {leftType rightType : Ty} {left right : DataValue} {a b : Core.Value}
        (first : DefaultData checked registry leftType left a)
        (second : DefaultData checked registry rightType right b) :
        DefaultData checked registry (.product leftType rightType) (.product left right) (.pair a b)
    | proxy {inner : Ty} {owner : Core.DataTypeId} {id : Core.Word}
        (metadata : registry.lookup id = some (.proxy inner))
        (identity : checked.catalog.identity? (.proxy inner) = some owner) :
        DefaultData checked registry (.proxy inner) (.proxy inner) (.constructed ⟨owner, 0⟩ (.word id))
    | mapping {key value : Ty} {id : Core.Word} {layout : Core.OrderedMapping.Layout} {fallback : Core.Value}
        (metadata : registry.lookup id = some (.mapping key value))
        (layoutAt : checked.catalog.mappingLayout key value = .ok layout)
        (defaultValue : Default checked registry value layout.valueType fallback) :
        DefaultData checked registry (.mapping key value) (.mapping key value [])
          (.pair (.word id) (.pair fallback (Core.OrderedMapping.encode layout [])))
    | compatible {expected actual : Ty} {data : DataValue} {native : Core.Value}
        (same : runtimeType expected = runtimeType actual)
        (shape : DefaultData checked registry actual data native) :
        DefaultData checked registry expected data native
  inductive Default (checked : Checked) (registry : Registry) : Ty → Core.Ty → Core.Value → Prop where
    | absent {raw : Ty} {type : Core.Ty}
        (missing : SourceCoreCompatibleValues.defaultValue? (raw.size + 1) raw = none) :
        Default checked registry raw type (.inLeft type .unit)
    | present {raw : Ty} {type : Core.Ty} {data : DataValue} {native : Core.Value}
        (computed : SourceCoreCompatibleValues.defaultValue? (raw.size + 1) raw = some data)
        (shape : DefaultData checked registry raw data native) :
        Default checked registry raw type (.inRight .unit native)
end

mutual
  inductive Output (checked : Checked) (registry : Registry) (world : Core.StoreTyping)
      (definitions : Core.DataEnvironment) : Ty → Core.Value → Prop where
    | unit : Output checked registry world definitions .unit .unit
    | bool (value : Bool) : Output checked registry world definitions .bool (.bool value)
    | word (value : Core.Word) : Output checked registry world definitions .word (.word value)
    | integer (value : Int) : Output checked registry world definitions .integer (.integer value)
    | product {leftType rightType : Ty} {left right : Core.Value}
        (first : Output checked registry world definitions leftType left)
        (second : Output checked registry world definitions rightType right) :
        Output checked registry world definitions (.product leftType rightType) (.pair left right)
    | function {parameter result : Ty} {native : Core.Value} {type : Core.Ty}
        (generated : checked.catalog.project (.function parameter result) = .ok type)
        (typed : Core.RuntimeValueHasType world native type definitions) :
        Output checked registry world definitions (.function parameter result) native
    | proxy {inner : Ty} {owner : Core.DataTypeId} {id : Core.Word}
        (metadata : registry.lookup id = some (.proxy inner))
        (identity : checked.catalog.identity? (.proxy inner) = some owner) :
        Output checked registry world definitions (.proxy inner) (.constructed ⟨owner, 0⟩ (.word id))
    | constructed {metadata : DataConstructorInstantiation} {id : Core.Word} {tag : Core.ConstructorId}
        {values : List Core.Value}
        (metadataAt : registry.lookup id = some (.constructor metadata))
        (resolved : checked.resolveConstructor metadata = .ok tag)
        (nominal : ∃ declaration arguments, metadata.resultType = Ty.nominal declaration arguments)
        (payloads : Payloads checked registry world definitions metadata.payloadTypes values) :
        Output checked registry world definitions metadata.resultType
          (.constructed tag (.pair (.word id) (pack values)))
    | mapping {key value : Ty} {id : Core.Word} {layout : Core.OrderedMapping.Layout}
        {entries : Core.OrderedMapping.Entries} {fallback : Core.Value}
        (metadata : registry.lookup id = some (.mapping key value))
        (layoutAt : checked.catalog.mappingLayout key value = .ok layout)
        (stored : Entries checked registry world definitions key value entries)
        (defaultValue : Default checked registry value layout.valueType fallback) :
        Output checked registry world definitions (.mapping key value)
          (.pair (.word id) (.pair fallback (Core.OrderedMapping.encode layout entries)))
    | compatible {expected actual : Ty} {native : Core.Value}
        (same : runtimeType expected = runtimeType actual)
        (shape : Output checked registry world definitions actual native) :
        Output checked registry world definitions expected native
  inductive Payloads (checked : Checked) (registry : Registry) (world : Core.StoreTyping)
      (definitions : Core.DataEnvironment) : List Ty → List Core.Value → Prop where
    | nil : Payloads checked registry world definitions [] []
    | cons {type : Ty} {value : Core.Value} {types : List Ty} {values : List Core.Value}
        (head : Output checked registry world definitions type value)
        (tail : Payloads checked registry world definitions types values) :
        Payloads checked registry world definitions (type :: types) (value :: values)
  inductive Entries (checked : Checked) (registry : Registry) (world : Core.StoreTyping)
      (definitions : Core.DataEnvironment) : Ty → Ty → Core.OrderedMapping.Entries → Prop where
    | empty (key value : Ty) : Entries checked registry world definitions key value []
    | entry {key value : Ty} {a b : Core.Value} {rest : Core.OrderedMapping.Entries}
        (first : Output checked registry world definitions key a)
        (second : Output checked registry world definitions value b)
        (tail : Entries checked registry world definitions key value rest) :
        Entries checked registry world definitions key value ((a, b) :: rest)
end
end Solcore.Frontend.SourceCorePublicOutputShapes
