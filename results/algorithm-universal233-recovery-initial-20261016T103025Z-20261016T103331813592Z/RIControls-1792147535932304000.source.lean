import RINormBound
namespace OrdinaryDispatch.RecoveryInitialBits.Controls
open Universal233 CoreProgram
open OrdinaryDispatch.RecoveryBits

def z : List Bool:=[]
def o : List Bool:=[true]
def tw : List Bool:=[false,true]
def th : List Bool:=[true,true]
def sev : List Bool:=[true,true,true]
def eig : List Bool:=[false,false,false,true]
def big : List Bool:=[false,false,false,true,false,true,true,true,true,true]
def tri : InputTree:=.node (.leaf z) (.node (.leaf o) (.leaf tw))
def dup : InputTree:=.node (.leaf o) (.leaf o)
def paddedDup : InputTree:=.node (.leaf o) (.leaf [true,false])
def four : InputTree:=.node (.node (.leaf z) (.leaf o)) (.node (.leaf tw) (.leaf th))
def forest : List (List (List Bool)) := [[z],[o,tw]]
def expected : BitTree:=.node [] (.leaf ⟨[false],[z],z⟩)
 (.node [true] (.leaf ⟨[true,false],[o],o⟩) (.leaf ⟨[true,true],[tw],o⟩))
def expectedNorm : BitTree:=.node [] (.leaf ⟨[false],[z],z⟩) (.leaf ⟨[true],[o,tw],o⟩)
def same : BitTree:=.node [] (.leaf ⟨[false],[sev],sev⟩) (.leaf ⟨[true],[eig],sev⟩)
def sameNorm : BitTree:=.leaf ⟨[],[sev,eig],sev⟩
def summary (r : InitValue) : Option (Nat×BitTree):=r.map (fun a=>(decode a.1,a.2))

def checks : List (String×Bool) := [
 ("singleton",summary (initializeBits 10 (.leaf sev) [[sev]] big).value==some (0,.leaf ⟨[],[sev],sev⟩)),
 ("tri_large_budget",summary (initializeBits 10 tri forest big).value==some (2,expected)),
 ("tri_small_budget",summary (initializeBits 10 tri forest o).value==some (1,expected)),
 ("duplicate_refusal",(initializeBits 10 dup [[o]] big).value==none),
 ("padding_duplicate",(initializeBits 10 paddedDup [[o]] big).value==none),
 ("source_refinement",viewInit (initializeBits 10 tri forest big).value==
   (OrdinaryDispatch.RecoveryLocalWork.meterInitial (OrdinaryDispatch.RecoveryLocalWork.meterColor [[0],[1,2]]) 1000 (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).value),
 ("missing_color",(ownedColor forest sev).value==[]),
 ("head_color",(ownedColor forest tw).value==o),
 ("empty_block",(ownedColor ([]::forest) tw).value==o),
 ("address_append",(appendAddress [true,false] true).value==[true,false,true]),
 ("input_copy",(copyInput tri).value==tri),
 ("leaves_copy",(leafArrays tri).value==[z,o,tw]),
 ("lifetime_word",(closeBits sev).work==13),
 ("owned_equal",(ownedEqual sev sev).value && (ownedEqual sev sev).work==88),
 ("input_copy_fee",(copyInput (.leaf sev)).work==17),
 ("input_close_fee",(closeInput (.leaf sev)).work==17),
 ("count_width_required",(summary (initializeBits 2 four [[z],[o],[tw],[th]] th).value).map Prod.fst==some 0),
 ("homogeneous_merge",(normalizeBits same).value==sameNorm),
 ("normalized_tri",(normalizeBits expected).value==expectedNorm),
 ("normalizer_source",viewTree (normalizeBits expected).value==normalize (viewTree expected))]
#eval checks
example : checks.all Prod.snd=true := by decide +kernel
#eval ("PASS_REPRESENTED_INITIAL_CONTROLS",checks.length,checks.all Prod.snd)
end OrdinaryDispatch.RecoveryInitialBits.Controls
