import Std
namespace CallerDetector
theorem shared : True := (fun h : True => h) True.intro
theorem ownB : True := True.intro
end CallerDetector
