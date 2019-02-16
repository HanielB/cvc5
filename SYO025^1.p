%------------------------------------------------------------------------------
% File     : SYO025^1 : TPTP v7.2.0. Released v3.7.0.
% Domain   : Syntactic
% Problem  : De Morgan by connectives and equality
% Version  : Especial.
% English  :

% Refs     : [BB05]  Benzmueller & Brown (2005), A Structured Set of Higher
%          : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    : Example 20d [BB05]

% Status   : Theorem
%          : Without Boolean extensionality : CounterSatisfiable
%          : Without functional extensionality : CounterSatisfiable
% Rating   : 0.33 v7.2.0, 0.12 v7.0.0, 0.14 v6.4.0, 0.17 v6.3.0, 0.20 v6.2.0, 0.29 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v3.7.0
% Syntax   : Number of formulae    :    1 (   0 unit;   0 type;   0 defn)
%            Number of atoms       :    4 (   1 equality;   2 variable)
%            Maximal formula depth :    7 (   7 average)
%            Number of connectives :    4 (   3   ~;   1   |;   0   &;   0   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    2 (   0   :;   0   =)
%            Number of variables   :    2 (   0 sgn;   0   !;   0   ?;   2   ^)
%                                         (   2   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments :
%------------------------------------------------------------------------------
thf(conj,conjecture,
    ( (&)
    = ( ^ [X: $o,Y: $o] :
          ~ ( ~ X
            | ~ Y ) ) )).

%------------------------------------------------------------------------------
