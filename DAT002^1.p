%------------------------------------------------------------------------------
% File     : DAT002^1 : TPTP v7.2.0. Released v6.4.0.
% Domain   : Data Structures
% Problem  : Recursive list Fibonacci sort
% Version  : Especial.
% English  : A list is Fibonacci sorted if it is sorted, and every element is
%            greater of equal to the sum of its two predecessors (from the
%            third element onwards).

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v7.1.0, 1.00 v6.4.0
% Syntax   : Number of formulae    :    9 (   0 unit;   4 type;   0 defn)
%            Number of atoms       :   49 (   0 equality;  17 variable)
%            Maximal formula depth :   12 (   5 average)
%            Number of connectives :   44 (   0   ~;   0   |;   2   &;  40   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    3 (   3   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   15 (   4   :;   0   =)
%            Number of variables   :    7 (   0 sgn;   7   !;   0   ?;   0   ^)
%                                         (   7   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
%            Arithmetic symbols    :   14 (   2 prd;   1 fun;   5 num;   6 var)
% SPC      : TH0_THM_NEQ_ARI

% Comments :
%------------------------------------------------------------------------------
thf(list_type,type,(
    list: $tType )).

thf(nil_type,type,(
    nil: list )).

thf(mycons_type,type,(
    mycons: $int > list > list )).

thf(sorted_type,type,(
    fib_sorted: list > $o )).

thf(empty_fib_sorted,axiom,(
    ( fib_sorted @ nil ) )).

thf(single_is_fib_sorted,axiom,(
    ! [X: $int] :
      ( fib_sorted @ ( mycons @ X @ nil ) ) )).

thf(double_is_fib_sorted_if_ordered,axiom,(
    ! [X: $int,Y: $int] :
      ( ( $less @ X @ Y )
     => ( fib_sorted @ ( mycons @ X @ ( mycons @ Y @ nil ) ) ) ) )).

thf(recursive_fib_sort,axiom,(
    ! [X: $int,Y: $int,Z: $int,R: list] :
      ( ( ( $less @ X @ Y )
        & ( $greatereq @ Z @ ( $sum @ X @ Y ) )
        & ( fib_sorted @ ( mycons @ Y @ ( mycons @ Z @ R ) ) ) )
     => ( fib_sorted @ ( mycons @ X @ ( mycons @ Y @ ( mycons @ Z @ R ) ) ) ) ) )).

thf(check_list,conjecture,
    ( fib_sorted @ ( mycons @ 1 @ ( mycons @ 2 @ ( mycons @ 4 @ ( mycons @ 7 @ ( mycons @ 100 @ nil ) ) ) ) ) )).

%------------------------------------------------------------------------------
