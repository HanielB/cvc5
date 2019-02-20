%------------------------------------------------------------------------------
% File     : SYO048^1 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Quantified multimodal logic)
% Problem  : Simple textbook example 5
% Version  : [Ben09] axioms.
% English  :

% Refs     : [Gol92] Goldblatt (1992), Logics of Time and Computation
%          : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    : ex5.p [Ben09]

% Status   : Theorem
% Rating   : 0.11 v7.2.0, 0.00 v7.1.0, 0.25 v7.0.0, 0.14 v6.4.0, 0.17 v6.3.0, 0.20 v6.2.0, 0.29 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.1.0, 0.40 v5.0.0, 0.20 v4.1.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :   64 (   0 unit;  32 type;  31 defn)
%            Number of atoms       :  238 (  36 equality; 137 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  138 (   4   ~;   4   |;   8   &; 114   @)
%                                         (   0 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :  172 ( 172   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   36 (  32   :;   0   =)
%            Number of variables   :   87 (   3 sgn;  30   !;   6   ?;  51   ^)
%                                         (  87   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments :
%------------------------------------------------------------------------------
%----Include embedding of quantified multimodal logic in simple type theory
include('Axioms/LCL013^0.ax').
%------------------------------------------------------------------------------
thf(conj,conjecture,(
    ! [R: $i > $i > $o] :
      ( mvalid
      @ ( mforall_prop
        @ ^ [A: $i > $o] :
            ( mforall_prop
            @ ^ [B: $i > $o] :
                ( mequiv @ ( mbox @ R @ ( mand @ A @ B ) ) @ ( mand @ ( mbox @ R @ A ) @ ( mbox @ R @ B ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
