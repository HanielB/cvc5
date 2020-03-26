import sigs.mysmt
open mysmt
open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def letSort1 := atom "U"
@[simp] def let16 := const "f" (mkArrowN [letSort1, letSort1, letSort1])
@[simp] def let13 := const "b" letSort1
@[simp] def let9 := const "g" (mkArrowN [letSort1, letSort1])
@[simp] def let6 := const "a" letSort1
@[simp] def let2 := const "c" letSort1
@[simp] def let1 := const "d" letSort1
@[simp] def let3 := mkAppN let9 [let2]
@[simp] def let4 := mkEq let1 let3
@[simp] def let5 := mkNot let4
@[simp] def let7 := mkEq let6 let1
@[simp] def let8 := mkNot let7
@[simp] def let10 := mkEq let6 let3
@[simp] def let11 := mkNot let10
@[simp] def let12 := mkEq let3 let1
@[simp] def let14 := mkEq let13 let13
@[simp] def let15 := mkNot let14
@[simp] def let17 := mkAppN let16 [let6, let13]
@[simp] def let18 := mkAppN let16 [let3, let13]
@[simp] def let19 := mkEq let17 let18
@[simp] def let20 := mkNot let19

noncomputable theorem main :
  th_holds ([let12]) -> th_holds ([let7]) -> th_holds ([let20]) -> th_holds ([mytop]) -> th_holds([]) :=
assume s0 : th_holds ([let12]),
assume s1 : th_holds ([let7]),
assume s2 : th_holds ([let20]),
assume s3 : th_holds ([mytop]),
have s4 : th_holds ([let4]), from trust s0,
have s5 : th_holds ([let11, let15, let19]), from @smtcongn let16 [let6, let13] [let3, let13],
have s6 : th_holds ([let8, let5, let10]), from smttrans,
have s7 : th_holds ([let8, let5, let15, let19]), from fo_R s6 s5 let10,
have s8 : th_holds ([let14]), from smtrefl,
have s9 : th_holds ([let8, let5, let19]), from fo_R s8 s7 let14,
have s10 : th_holds ([let8, let5]), from fo_R s9 s2 let19,
have s11 : th_holds ([let5]), from fo_R s1 s10 let7,
show th_holds ([]), from fo_R s4 s11 let4
