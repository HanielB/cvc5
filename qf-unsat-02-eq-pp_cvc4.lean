import sigs.mysmt
open mysmt
open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def letSort1 := atom "U"
@[simp] def let9 := const "f" (mkArrowN [letSort1, letSort1])
@[simp] def let2 := const "b" letSort1
@[simp] def let1 := const "a" letSort1
@[simp] def let3 := mkEq let1 let2
@[simp] def let4 := mkNot let3
@[simp] def let5 := mkAppN let9 [let1]
@[simp] def let6 := mkAppN let9 [let2]
@[simp] def let7 := mkEq let5 let6
@[simp] def let8 := mkNot let7

noncomputable theorem main :
  th_holds ([let3]) -> th_holds ([let8]) -> th_holds ([mytop]) -> th_holds([]) :=
assume s0 : th_holds ([let3]),
assume s1 : th_holds ([let8]),
assume s2 : th_holds ([mytop]),
have s3 : th_holds ([let4, let7]), from @smtcongn let9 [let1] [let2],
have s4 : th_holds ([let4]), from fo_R s3 s1 let7,
show th_holds ([]), from fo_R s0 s4 let3
