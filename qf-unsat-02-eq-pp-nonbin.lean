import sigs.mysmt

open mysmt

open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def A := atom "A"
@[simp] def fA := mkArrowN [A, A, A, A]

@[simp] def a := const "a" A
@[simp] def b := const "b" A
@[simp] def c := const "c" A
@[simp] def d := const "d" A
@[simp] def f := const "f" fA

@[simp] def fa := mkApp f a
@[simp] def faa := mkAppN f [a, a]
@[simp] def faac := mkAppN f [a, a, c]
@[simp] def fab := mkAppN f [a, b]
@[simp] def fabd := mkAppN f [a, b, d]

@[simp] def eqab := mkEq a b
@[simp] def neqab := mkNot eqab
@[simp] def eqaa := mkEq a a
@[simp] def neqaa := mkNot eqaa
@[simp] def eqbb := mkEq b b
@[simp] def neqbb := mkNot eqbb
@[simp] def eqff := mkEq f f
@[simp] def neqff := mkNot eqff
@[simp] def eqfafa := mkEq fa fa
@[simp] def neqfafa := mkNot eqfafa
@[simp] def eqfaafab := mkEq faa fab
@[simp] def neqfaafab := mkNot eqfaafab
@[simp] def eqfaacfabc := mkEq faac fabd
@[simp] def eqcd := mkEq c d
@[simp] def neqcd := mkNot eqcd

@[simp] def eqfaacfabd := mkEq faac fabd
@[simp] def neqfaacfabd := mkNot eqfaacfabd

noncomputable theorem teo :
    th_holds ([eqab]) -> th_holds ([eqcd]) -> th_holds ([neqfaacfabd]) ->
    th_holds ([]) :=
assume s0 : th_holds ([eqab]),
assume s1 : th_holds ([eqcd]),
assume s2 : th_holds ([neqfaacfabd]),
have s3   : th_holds ([eqff]), from smtrefl f,
have s4   : th_holds ([eqaa]), from smtrefl a,
have s5   : th_holds ([neqff, neqaa, eqfafa]) := smtcong,
have s6   : th_holds ([neqfafa, neqab, eqfaafab]) := smtcong,
have s7   : th_holds ([neqfaafab, neqcd, eqfaacfabd]) := smtcong,
have s8   : th_holds ([neqaa, eqfafa]), from fo_R s3 s5 eqff,
have s9   : th_holds ([eqfafa]), from fo_R s4 s8 eqaa,
have s10  : th_holds ([neqab, eqfaafab]), from fo_R s9 s6 eqfafa,
have s11  : th_holds ([eqfaafab]), from fo_R s0 s10 eqab,
have s12  : th_holds ([neqcd, eqfaacfabd]), from fo_R s11 s7 eqfaafab,
have s13  : th_holds ([eqfaacfabd]), from fo_R s1 s12 eqcd,
show th_holds [], from fo_R s13 s2 eqfaacfabd

noncomputable lemma congstep : th_holds ([eqab]) -> th_holds ([eqcd]) -> th_holds ([eqfaacfabd]) :=
assume s0 : th_holds ([eqab]),
assume s1 : th_holds ([eqcd]),
have s2   : th_holds ([eqff]), from smtrefl f,
have s3   : th_holds ([eqaa]), from smtrefl a,
have s4   : th_holds ([neqff, neqaa, eqfafa]) := smtcong,
have s5   : th_holds ([neqfafa, neqab, eqfaafab]) := smtcong,
have s6   : th_holds ([neqfaafab, neqcd, eqfaacfabd]) := smtcong,
have s7   : th_holds ([neqaa, eqfafa]), from fo_R s2 s4 eqff,
have s8   : th_holds ([eqfafa]), from fo_R s3 s7 eqaa,
have s9   : th_holds ([neqab, eqfaafab]), from fo_R s8 s5 eqfafa,
have s10  : th_holds ([eqfaafab]), from fo_R s0 s9 eqab,
have s11  : th_holds ([neqcd, eqfaacfabd]), from fo_R s10 s6 eqfaafab,
show th_holds ([eqfaacfabd]), from fo_R s1 s11 eqcd

noncomputable theorem teo2 :
    th_holds ([eqab]) -> th_holds ([eqcd]) -> th_holds ([neqfaacfabd]) ->
    th_holds ([]) :=
assume s0 : th_holds ([eqab]),
assume s1 : th_holds ([eqcd]),
assume s2 : th_holds ([neqfaacfabd]),
have s3   : th_holds ([eqfaacfabd]) := congstep s0 s1,
show th_holds [], from fo_R s3 s2 eqfaacfabd

noncomputable theorem teo3 :
    th_holds ([eqab]) -> th_holds ([eqcd]) -> th_holds ([neqfaacfabd]) ->
    th_holds ([]) :=
assume s0 : th_holds ([eqab]),
assume s1 : th_holds ([eqcd]),
assume s2 : th_holds ([neqfaacfabd]),
have s3   : th_holds ([eqaa]), from smtrefl,
have s4   : th_holds ([neqaa, neqab, neqcd, eqfaacfabd]) := @smtcongn f [a,a,c] [a,b,d],
have s5   : th_holds ([neqab, neqcd, eqfaacfabd]), from fo_R s3 s4 eqaa,
have s6   : th_holds ([neqcd, eqfaacfabd]), from fo_R s0 s5 eqab,
have s7   : th_holds ([eqfaacfabd]), from fo_R s1 s6 eqcd,
show th_holds [], from fo_R s7 s2 eqfaacfabd
