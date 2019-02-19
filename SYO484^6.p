%------------------------------------------------------------------------------
% File     : SYO484^6 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Syntactic
% Problem  : Ted Sider's S5 quantified modal logic wff 10
% Version  : Especial.
% English  :

% Refs     : [Sid09] Sider (2009), Logic for Philosophy
% Source   : [Sid09]
% Names    :

% Status   : CounterSatisfiable
% Rating   : 0.50 v7.2.0, 0.33 v6.2.0, 0.00 v5.4.0, 0.67 v5.0.0, 0.33 v4.1.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :   72 (   0 unit;  35 type;  33 defn)
%            Number of atoms       :  248 (  38 equality; 137 variable)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :  140 (   5   ~;   5   |;   8   &; 114   @)
%                                         (   0 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :  178 ( 178   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   39 (  35   :;   0   =)
%            Number of variables   :   90 (   3 sgn;  30   !;   6   ?;  54   ^)
%                                         (  90   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_CSA_EQU_NAR

% Comments :
%------------------------------------------------------------------------------
%----Include axioms for modal logic S5
%% include('Axioms/LCL013^0.ax').
include('Axioms/LCL013^6.ax').
%------------------------------------------------------------------------------
thf(mvalid_type,type,(
    mvalid: ( $i > $o ) > $o )).

thf(mvalid,definition,
    ( mvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ( Phi @ W ) ) )).


thf(meq_ind_type,type,(
    meq_ind: mu > mu > $i > $o )).

thf(meq_ind,definition,
    ( meq_ind
    = ( ^ [X: mu,Y: mu,W: $i] : ( X = Y ) ) )).

thf(mforall_ind_type,type,(
    mforall_ind: ( mu > $i > $o ) > $i > $o )).

thf(mforall_ind,definition,
    ( mforall_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] :
          ( Phi @ X @ W ) ) )).


thf(prove,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mbox_s5
          @ ( mforall_ind
            @ ^ [Y: mu] :
                ( meq_ind @ X @ Y ) ) ) ) )).

%------------------------------------------------------------------------------
