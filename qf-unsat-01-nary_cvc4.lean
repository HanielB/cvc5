import sigs.mysmt
open mysmt
open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def letSort1 := atom "U"
@[simp] def let23 := const "p" (mkArrowN [letSort1, boolsort])
@[simp] def let7 := const "f4" letSort1
@[simp] def let6 := const "f3" letSort1
@[simp] def let4 := const "f2" letSort1
@[simp] def let1 := const "f1" letSort1

@[simp] def let2 := mkPapp let23 let1
@[simp] def let3 := mkNot let2
@[simp] def let5 := mkEq let1 let4
@[simp] def let8 := mkEq let6 let7
@[simp] def let9 := mkNot let8
@[simp] def let10 := mkEq let4 let6
@[simp] def let11 := mkNot let10
@[simp] def let12 := mkEq let4 let7
@[simp] def let13 := mkNot let12
@[simp] def let14 := mkAndN [let9, let11, let13]
@[simp] def let15 := mkOrN [let5, let14]
@[simp] def let16 := mkNot let15
@[simp] def let17 := mkPappN let23 [let6]
@[simp] def let18 := mkImplies let15 let17
@[simp] def let19 := mkNot let18
@[simp] def let20 := mkNot let5
@[simp] def let21 := mkNot let14
@[simp] def let22 := mkImplies let2 let18
@[simp] def let24 := mkDistinct [let6, let7, let4]
@[simp] def let25 := mkOrN [let5, let24]
@[simp] def let26 := mkImplies let25 let17
@[simp] def let27 := mkImplies let2 let26
@[simp] def let28 := mkNot let17

noncomputable theorem main :
  th_holds ([let5]) -> th_holds ([let27]) -> th_holds ([let2]) -> th_holds ([let28]) -> th_holds ([mytop]) -> th_holds([]) :=
assume s0 : th_holds ([let5]),
assume s1 : th_holds ([let27]),
assume s2 : th_holds ([let2]),
assume s3 : th_holds ([let28]),
assume s4 : th_holds ([mytop]),
have s5 : th_holds ([let22]), from trust s1,
have s6 : th_holds ([let21, let9]), from @cnf_and_pos [let9, let11, let13] 0,
have s7 : th_holds ([let21, let11]), from @cnf_and_pos [let9, let11, let13] 1,
have s8 : th_holds ([let21, let13]), from @cnf_and_pos [let9, let11, let13] 2,
have s9 : th_holds ([let14, let8, let10, let12]), from @cnf_and_neg_n [let9, let11, let13],
have s10 : th_holds ([let15, let20]), from @cnf_or_neg [let5, let14] 0,
have s11 : th_holds ([let19, let16, let17]), from cnf_implies_pos,
have s12 : th_holds ([let18, let28]), from cnf_implies_neg_1,
have s13 : th_holds ([let3, let18]), from cnf_implies s5,
have s14 : th_holds ([let18]), from fo_R s2 s13 let2,
have s15 : th_holds ([let15]), from fo_R s0 s10 let5,
have s16 : th_holds ([let16, let17]), from fo_R s14 s11 let18,
have s17 : th_holds ([let17]), from fo_R s15 s16 let15,
show th_holds ([]), from fo_R s17 s3 let17
