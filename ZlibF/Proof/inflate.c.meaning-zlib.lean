import ZlibF.Proof.«inflate.c.meaning-call-entry»
import ZlibF.Proof.«inflate.c.meaning-call-exit»
import ZlibF.Proof.«inflate.c.meaning-trip-modes»
import ZlibF.Proof.«inflate.c.meaning-trip-trailer»
import ZlibF.Proof.«inflate.c.meaning-trip-body»
import ZlibF.Proof.«inflate.c.meaning-trip-codes»
import ZlibF.Proof.«inflate.c.meaning-head-zlib»
import ZlibF.Proof.«inflate.c.meaning-dict-trip»
import ZlibF.Proof.«inflate.c.meaning-type-final»

/-!
# inflate.c: the format meaning after every zlib protocol history

Every row of the zlib wrapper is proved: the trip rows (`ZlibTripRows`, `inflate.c.meaning-trip`)
and the call rows (`CallRows`, `inflate.c.meaning-call`). `meaning_zlib` is `ParseMeaning` after
every protocol history of a zlib configuration, every window included.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The trip rows of the zlib wrapper. -/
theorem zlib_trip_rows : ZlibTripRows :=
  ⟨loop_mode_cases, gzip_fields_absent, trip_head_zlib, trip_dictid, trip_dict, trip_type_open,
    trip_type_final, trip_stored, trip_dynamic, trip_codes, trip_check_wrapped,
    trip_trailer⟩

/-- The call rows of a single-dictionary history. -/
theorem call_rows : CallRows := ⟨call_refused, call_entry, call_exit⟩

/-- `ParseMeaning` after every zlib protocol history. -/
theorem meaning_zlib {wb : Int32} {bits : Nat} (zlib : Api.inflWbits wb.toInt = some (.zlib, bits))
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace wb r h log pending) :
    ParseMeaning wb r h log pending ∧ log.singleDictionary = true :=
  meaning_of_protocol_zlib zlib_trip_rows call_rows zlib trace

#print axioms meaning_zlib

end Zlib.Inflate.Proofs
