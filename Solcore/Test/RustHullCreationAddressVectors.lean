import Solcore.Frontend.RustHull.CreationPreimage

/-! The independent CREATE and CREATE2 address specification derives the 11
reference vectors in `Tests/Fixtures/EvmAccounts/address-vectors.json`, which
were computed with `cast` and Python RLP. They cover every RLP nonce encoding,
including EIP-2681's largest nonce, and CREATE2 init code of one and four
bytes. Each digest is evaluated in the kernel. -/
set_option autoImplicit false
namespace Tests.RustHullCreationAddressVectors
open Solcore Solcore.Frontend.RustHull

private abbrev w := Core.Word.ofNatModulo

/-- The specification derives the reference CREATE address of a short preimage. -/
theorem create_vector {creator nonce expected : Core.Word}
    (short : (CreationAddressSemantics.createPreimage creator nonce).length < 136)
    (computed : CreationAddressSemantics.address
      (CreationPreimage.shortDigest (CreationAddressSemantics.createPreimage creator nonce)) = expected) :
    CreationAddressSemantics.Derived creator nonce [] Core.Word.zero .create expected := by
  rw [← computed]
  exact .create (CreationPreimage.shortDigest_keccak short)

/-- The specification derives the reference CREATE2 address of short init code. -/
theorem create2_vector {creator salt expected : Core.Word} {init : CreationAddressSemantics.Bytes}
    (short : init.length < 136)
    (computed : CreationAddressSemantics.address (CreationPreimage.shortDigest
      (CreationAddressSemantics.create2Preimage creator salt (CreationPreimage.shortDigest init))) = expected) :
    CreationAddressSemantics.Derived creator Core.Word.zero (CreationAddressSemantics.stored init) (w init.length)
      (.create2 salt) expected := by
  rw [← computed]
  exact .create2 (CreationPreimage.shortDigest_keccak short)
    (CreationPreimage.shortDigest_keccak (by rw [CreationPreimage.create2Preimage_length]; decide))

private def deadbeef : Core.Word := w 0xdeadbeef00000000000000000000000000000000

theorem create_nonce_0 : CreationAddressSemantics.Derived deadbeef (w 0) [] Core.Word.zero .create
    (w 0xf2048c36a5536fea3bc71d49ed59f2c65c546eea) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_1 : CreationAddressSemantics.Derived deadbeef (w 1) [] Core.Word.zero .create
    (w 0x054dd934335ea61232ae4c051f8bf20e540f8291) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_127 : CreationAddressSemantics.Derived deadbeef (w 127) [] Core.Word.zero .create
    (w 0x7feb088e1893d4a1087288d386c07252abb3c02e) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_128 : CreationAddressSemantics.Derived deadbeef (w 128) [] Core.Word.zero .create
    (w 0x2297787b25b800d655071345a1d3a7951404b50c) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_255 : CreationAddressSemantics.Derived deadbeef (w 255) [] Core.Word.zero .create
    (w 0xc8d17a8bdb6001525f8594e3ca4413d4bd644605) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_256 : CreationAddressSemantics.Derived deadbeef (w 256) [] Core.Word.zero .create
    (w 0xa0ddf5980551b5ec83721bcf168785ac3cedb183) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_largest : CreationAddressSemantics.Derived deadbeef (w 18446744073709551615) [] Core.Word.zero
    .create (w 0x66e93872e94cc56d1da3bb63f81dabd9c1d6c125) := create_vector (by decide +kernel) (by decide +kernel)
theorem create2_zero_creator : CreationAddressSemantics.Derived (w 0) Core.Word.zero (CreationAddressSemantics.stored [0])
    (w 1) (.create2 (w 0)) (w 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38) :=
  create2_vector (by decide) (by decide +kernel)
theorem create2_zero_salt : CreationAddressSemantics.Derived deadbeef Core.Word.zero (CreationAddressSemantics.stored [0])
    (w 1) (.create2 (w 0)) (w 0xb928f69bb1d91cd65274e3c79d8986362984fda3) :=
  create2_vector (by decide) (by decide +kernel)
theorem create2_salt : CreationAddressSemantics.Derived deadbeef Core.Word.zero (CreationAddressSemantics.stored [0])
    (w 1) (.create2 (w 22207167547627365064083290255604625247830016)) (w 0xf2a2934e8506d97a2cee99962533f9729676ae24) :=
  create2_vector (by decide) (by decide +kernel)
theorem create2_init : CreationAddressSemantics.Derived (w 0xdeadbeef) Core.Word.zero
    (CreationAddressSemantics.stored [0xde, 0xad, 0xbe, 0xef]) (w 4) (.create2 (w 3405691582))
    (w 0x60f3f640a8508fc6a86d45df051962668e1e8ac7) :=
  create2_vector (by decide) (by decide +kernel)

end Tests.RustHullCreationAddressVectors
