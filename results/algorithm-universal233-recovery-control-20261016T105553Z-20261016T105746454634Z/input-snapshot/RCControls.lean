import RCInterface
namespace OrdinaryDispatch.RecoveryControlBits.Controls
open Universal233 CoreProgram
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

def z : List Bool:=[]
def o : List Bool:=[true]
def tw : List Bool:=[false,true]
def th : List Bool:=[true,true]
def g0 : BitGroup:=⟨[false,false],[z],z⟩
def g1 : BitGroup:=⟨[false,true],[o],o⟩
def g2 : BitGroup:=⟨[true,false],[tw],z⟩
def g3 : BitGroup:=⟨[true,true],[th],o⟩
def quartet : BitTree:=.node [] (.node [false] (.leaf g0) (.leaf g1)) (.node [true] (.leaf g2) (.leaf g3))
def two : BitTree:=.node [] (.leaf g0) (.leaf g1)
def hom1 : BitGroup:={g1 with color:=z}
def hom2 : BitGroup:={g2 with color:=o}
def homogeneousFirst : BitTree:=.node [] (.node [false] (.leaf g0) (.leaf hom1)) (.node [true] (.leaf hom2) (.leaf g3))
def late : List BitGroup:=[g0,hom1,g3]
def lateTree : BitTree:=.node [] (.node [false] (.leaf g0) (.leaf hom1)) (.leaf g3)
def rightOnly : BitTree:=.node [] (.leaf g0) (.node [true] (.leaf g2) (.leaf g3))
def merged0 : BitGroup:=⟨[false],[z,o],z⟩
def merged1 : BitGroup:=⟨[true],[tw,th],o⟩
def expectedNorm : BitTree:=.node [] (.leaf merged0) (.leaf merged1)
def erasedLeaf : BitTree:=.node [] (.leaf g1) (.node [true] (.leaf g2) (.leaf g3))
def padded : BitTree:=.node [] (.leaf g0) (.leaf {g1 with color:=[false]})

def checks : List (String×Bool) := [
 ("uniform_priority",(chooseBits 8 (.leaf g0)).value==.finish),
 ("unique_before_cherry",(chooseBits 8 two).value==.one g0),
 ("mixed_fallback",(chooseBits 8 quartet).value==.two g0 g1),
 ("homogeneous_refusal",(chooseBits 8 homogeneousFirst).value==.refuse .homogeneousCherry),
 ("failed_candidates",!(uniqueTest 8 late g0).value && !(uniqueTest 8 late hom1).value && (uniqueTest 8 late g3).value),
 ("late_first_unique",(findUnique 8 late late).value==some g3),
 ("late_priority",(chooseBits 8 lateTree).value==.one g3),
 ("all_failed_unique",(findUnique 8 (rawGroups quartet) (rawGroups quartet)).value==none),
 ("groups_order",(groupsBits quartet).value==[g0,g1,g2,g3]),
 ("filter_order",(filterColor z (rawGroups quartet)).value==[g0,g2]),
 ("mixed_left_priority",(mixedBits quartet).value==some (g0,g1)),
 ("mixed_right_fallback",(mixedBits rightOnly).value==some (g2,g3)),
 ("no_cherry_tag",(chooseCore 8 (rawGroups quartet) (.leaf g0)).value==.refuse .noCherry),
 ("empty_tag",(chooseCore 8 [] quartet).value==.refuse .empty),
 ("padding_colors",(chooseBits 8 padded).value==.finish),
 ("count_fit_needed",(uniqueTest 2 (List.replicate 5 g0) g0).value),
 ("group_copy_cost",(copyGroup g0).work==29),
 ("group_close_cost",(closeGroups [g0]).work==35),
 ("discard_right_paid",(pickPair (some (g2,g3)) (some (g0,g1))).work==86),
 ("prepare_exact",(prepare 8 homogeneousFirst).value==(expectedNorm,.one merged0)),
 ("path_empty_distinct",!(ownedAddressEqual [] [false]).value),
 ("path_padding_distinct",!(ownedAddressEqual [true] [true,false]).value),
 ("address_contains",(addressContains [false] [[true],[false]]).value),
 ("address_prefix_absent",!(addressContains [false] [[false,false]]).value),
 ("erase_root",(eraseBits [] quartet).value==none),
 ("erase_leaf",(eraseBits [false,false] quartet).value==some erasedLeaf),
 ("erase_subtree",(eraseBits [false] quartet).value==some (.node [true] (.leaf g2) (.leaf g3))),
 ("erase_absent",(eraseBits [true,true,true] quartet).value==some quartet),
 ("erase_entire_leaf",(eraseBits g0.origin (.leaf g0)).value==none),
 ("erased_original_origin",(eraseBits [false,false] two).value==some (.leaf g1))]
#eval checks
example : checks.all Prod.snd=true := by decide +kernel
#eval ("PASS_PERSISTENT_CONTROL_CONTROLS",checks.length,checks.all Prod.snd)
end OrdinaryDispatch.RecoveryControlBits.Controls
