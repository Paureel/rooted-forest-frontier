import FingerprintSupport
namespace FingerprintToy
structure Packet where
  value : Nat
private def hidden : Nat := 7
def projected (r : Packet) : Nat := r.value + hidden + 1
theorem harmless : True := True.intro
end FingerprintToy

run_cmd ProducerFingerprint.emit ["FingerprintToyBad"]
