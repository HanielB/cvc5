import sigs.hb_smt
open smt
open smt.sort smt.term

@[simp] def letSort0 := atom "U"
@[simp] def let14 := const "p" (mkArrowN [letSort0, boolsort])
@[simp] def let8 := top
@[simp] def let3 := const "b" letSort0
@[simp] def let1 := const "a" letSort0
@[simp] def let2 := mkAppN let14 [let1]
@[simp] def let4 := mkAppN let14 [let3]
@[simp] def let5 := mkIff let2 let4
@[simp] def let6 := mkEq let1 let3
@[simp] def let7 := mkNot let6
@[simp] def let9 := mkIff let4 let8
@[simp] def let10 := mkIff let2 let8
@[simp] def let11 := mkIff let4 let2
@[simp] def let12 := mkNot let4
@[simp] def let13 := mkNot let11
@[simp] def let15 := mkNot let10

#eval [let7, let15, let9]
#eval [let7, mkNot let2, let4]
#eval [let12]
noncomputable theorem main :
  th_holds ([let2]) -> th_holds ([let6]) -> th_holds ([let12]) -> th_holds ([let8]) -> th_holds([]) :=
assume s0 : th_holds ([let2]),
assume s1 : th_holds ([let6]),
assume s2 : th_holds ([let12]),
assume s3 : th_holds ([let8]),
have s4 : th_holds ([let13, let15, let9]), from smttrans_p,
have s5 : th_holds ([let7, let5]), from @smtcongn_p let14 [let1] [let3],
have s51 : th_holds ([mkNot let5, let11]), from smtsymm_p,
have s52 : th_holds ([let7, let11]), from R0 s5 s51 let5,
have s6 : th_holds ([let7, let15, let9]), from R0 s52 s4 let11,
have s7 : th_holds ([let7, mkNot let2, let4]), from simp_iff s6,
show th_holds ([]), from R1 (R1 (R0 s7 s2 let4) s1 let6) s0 let2
