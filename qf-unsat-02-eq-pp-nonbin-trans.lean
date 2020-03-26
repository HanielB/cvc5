import sigs.mysmt

-- import smt

-- open smt

-- variable x : int
-- variable y : int

-- variable arr : array int int

-- #reduce select (store arr 0 1) 0

-- #check select_store

-- universes u v
-- variables {α : Type u} {β : Type v}

-- variable [decidable_eq α]

-- lemma my_select_store (a : array α β) (i : α) (v : β) : select (store a i v) i = v  :=
-- begin
-- unfold smt.store smt.select,
-- rewrite if_pos,
-- reflexivity
-- end

-- #check if_pos

open mysmt

open mysmt.sort mysmt.myterm mysmt.myformula
@[simp] def A := atom "A"

@[simp] def a := const "a" A
@[simp] def b := const "b" A
@[simp] def c := const "c" A
@[simp] def d := const "d" A
@[simp] def f := const "f" (arrow A (arrow A A))
@[simp] def g := const "g" (arrow A A)

@[simp] def fa := mkApp f a
@[simp] def fab := mkApp (mkApp f a) b
@[simp] def gc := mkApp g c
@[simp] def fgc := mkApp f gc
@[simp] def fgcb := mkApp fgc b

@[simp] def eqab := mkEq a b
@[simp] def neqab := mkNot eqab
@[simp] def eqgcd := mkEq gc d
@[simp] def neqgcd := mkNot eqgcd
@[simp] def eqdgc := mkEq d gc
@[simp] def neqdgc := mkNot eqdgc
@[simp] def eqad := mkEq a d
@[simp] def neqad := mkNot eqad

@[simp] def eqff := mkEq f f
@[simp] def neqff := mkNot eqff
@[simp] def eqgg := mkEq g g
@[simp] def neqgg := mkNot eqgg
@[simp] def eqbb := mkEq b b
@[simp] def neqbb := mkNot eqbb
@[simp] def eqagc := mkEq a gc
@[simp] def neqagc := mkNot eqagc

@[simp] def eqfafgc := mkEq fa fgc
@[simp] def neqfafgc := mkNot eqfafgc
@[simp] def eqfabfgcb := mkEq fab fgcb
@[simp] def neqfabfgcb := mkNot eqfabfgcb

noncomputable theorem teo :
    th_holds ([eqab]) -> th_holds ([eqgcd]) -> th_holds ([eqad]) -> th_holds ([neqfabfgcb]) ->
    th_holds ([]) :=
assume s0 : th_holds ([eqab]),
assume s1 : th_holds ([eqgcd]),
assume s2 : th_holds ([eqad]),
assume s3 : th_holds ([neqfabfgcb]),
have s4   : th_holds ([eqff]), from smtrefl,
have s5   : th_holds ([eqbb]), from smtrefl,
have s6   : th_holds ([neqgcd, eqdgc]), from smtsymm,
have s7   : th_holds ([eqdgc]), from fo_R s1 s6 eqgcd,
have s8   : th_holds ([neqad, neqdgc, eqagc]), from smttrans,
have s9   : th_holds ([neqdgc, eqagc]), from fo_R s2 s8 eqad,
have s10  : th_holds ([eqagc]), from fo_R s7 s9 eqdgc,
have s11  : th_holds ([neqff, neqagc, eqfafgc]) := smtcong,
have s12  : th_holds ([neqfafgc, neqbb, eqfabfgcb]) := smtcong,
have s13  : th_holds ([neqagc, eqfafgc]), from fo_R s4 s11 eqff,
have s14  : th_holds ([eqfafgc]), from fo_R s10 s13 eqagc,
have s15  : th_holds ([neqbb, eqfabfgcb]), from fo_R s14 s12 eqfafgc,
have s16  : th_holds ([eqfabfgcb]), from fo_R s5 s15 eqbb,
show th_holds [], from fo_R s16 s3 eqfabfgcb
