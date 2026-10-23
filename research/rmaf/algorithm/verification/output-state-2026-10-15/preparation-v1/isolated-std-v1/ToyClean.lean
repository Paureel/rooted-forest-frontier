import Std
namespace OutputStateToy
inductive Bit where | zero | one
private theorem hiddenClean : True := True.intro
theorem publicClean : True := True.intro
end OutputStateToy
