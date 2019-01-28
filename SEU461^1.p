%------------------------------------------------------------------------------
% File     : SEU461^1 : TPTP v7.2.0. Released v3.6.0.
% Domain   : Set Theory (Binary relations)
% Problem  : The transitive closure of a binary relation is transitive, part 1
% Version  : [Nei08] axioms.
% English  :

% Refs     : [BN99]  Baader & Nipkow (1999), Term Rewriting and All That
%          : [Nei08] Neis (2008), Email to Geoff Sutcliffe
% Source   : [Nei08]
% Names    :

% Status   : Theorem
% Rating   : 0.22 v7.2.0, 0.12 v7.1.0, 0.25 v7.0.0, 0.14 v6.4.0, 0.17 v6.3.0, 0.20 v6.2.0, 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v5.1.0, 0.40 v5.0.0, 0.20 v4.1.0, 0.33 v4.0.0, 0.67 v3.7.0
% Syntax   : Number of formulae    :   59 (   0 unit;  29 type;  29 defn)
%            Number of atoms       :  252 (  33 equality; 159 variable)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :  160 (   4   ~;   4   |;  12   &; 124   @)
%                                         (   0 <=>;  16  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :  199 ( 199   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   31 (  29   :;   0   =)
%            Number of variables   :   87 (   0 sgn;  39   !;   5   ?;  43   ^)
%                                         (  87   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments : Some proofs can be found in chapter 2 of [BN99]
%          :
%------------------------------------------------------------------------------
%----Include axioms of binary relations
include('Axioms/SET009^0.ax').
%------------------------------------------------------------------------------
thf(transitive_closure_is_transitive,conjecture,(
    ! [R: $i > $i > $o] :
      ( trans @ ( tc @ R ) ) )).

%------------------------------------------------------------------------------
