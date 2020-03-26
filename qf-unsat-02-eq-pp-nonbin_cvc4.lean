import sigs.mysmt
open mysmt
open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def letSort1 := atom "U"
@[simp] def let13 := const "f" (mkArrowN [letSort1, letSort1, letSort1, letSort1])
@[simp] def let6 := const "b" letSort1
@[simp] def let5 := const "a" letSort1
@[simp] def let2 := const "d" letSort1
@[simp] def let1 := const "c" letSort1
@[simp] def let3 := mkEq let1 let2
@[simp] def let4 := mkNot let3
@[simp] def let7 := mkEq let5 let6
@[simp] def let8 := mkNot let7
@[simp] def let9 := mkAppN let13 [let5, let5, let1]
@[simp] def let10 := mkAppN let13 [let5, let6, let2]
@[simp] def let11 := mkEq let9 let10
@[simp] def let12 := mkNot let11
@[simp] def let14 := mkEq let5 let5
@[simp] def let15 := mkNot let14

noncomputable theorem main :
  th_holds ([let7]) -> th_holds ([let3]) -> th_holds ([let12]) -> th_holds ([mytop]) -> th_holds([]) :=
assume s0 : th_holds ([let7]),
assume s1 : th_holds ([let3]),
assume s2 : th_holds ([let12]),
assume s3 : th_holds ([mytop]),
have s4 : th_holds ([let15, let8, let4, let11]), from @smtcongn let13 [let5, let5, let1] [let5, let6, let2],
have s5 : th_holds ([let14]), from smtrefl,
have s6 : th_holds ([let8, let4, let11]), from fo_R s5 s4 let14,
have s7 : th_holds ([let8, let4]), from fo_R s6 s2 let11,
have s8 : th_holds ([let8]), from fo_R s1 s7 let3,
show th_holds ([]), from fo_R s0 s8 let7
