% Conflict-Free
{confree(X): arg(X)}.
:- att(X,Y), confree(X), confree(Y).
#show confree/1.

%%-----------------------------------------------

% Admissible
{set_item(X): arg(X)}.
:- att(X,Y), set_item(X), set_item(Y).
attacked_by_set_item(A) :- set_item(B), att(B, A).
undefended(A) :- set_item(A), att(B, A), not attacked_by_set_item(B).
:- undefended(A).
#show set_item/1.

%%-----------------------------------------------

% Stable
{set_item(X): arg(X)}.
:- att(X,Y), set_item(X), set_item(Y).
attacked_by_set_item(A) :- set_item(B), att(B, A).
% Admissibility
undefended(A) :- set_item(A), att(B, A), not attacked_by_set_item(B).
:- undefended(A).
% For Stable Set
not_attacked(A):- arg(A), not set_item(A), not attacked_by_set_item(A).
:- not_attacked(A).
#show set_item/1.

%%-----------------------------------------------

% Preferred 1
defended(X) | defeated(X) :- arg(X).
defended(X) :- arg(X), defeated(Y) : att(Y,X).
defeated(X) :- defended(Y), att(Y,X).
:- defended(X), not defeated(Y), att(Y,X).
:- defeated(X), not defended(Y) : att(Y,X).
in(X) :- defended(X), not defeated(X).
#show in/1.

%%-----------------------------------------------
%% an argument x defeats an argument y if x attacks y
defeat(X,Y) :- att(X,Y).

%% Guess a set S \subseteq A
in(X) :- not out(X), arg(X).
out(X) :- not in(X), arg(X).

%% S has to be conflict-free
:- in(X), in(Y), defeat(X,Y).

%% The argument x is defeated by the set S
defeated(X) :- in(Y), defeat(Y,X).

%% The argument x is not defended by S
not_defended(X) :- defeat(Y,X), not defeated(Y).

%% All arguments x \in S need to be defended by S (admissibility)
:- in(X), not_defended(X).

lt(X,Y) :- arg(X),arg(Y), X<Y.
nsucc(X,Z) :- lt(X,Y), lt(Y,Z).
succ(X,Y) :- lt(X,Y), not nsucc(X,Y).
ninf(X) :- lt(Y,X).
nsup(X) :- lt(X,Y).
inf(X) :- not ninf(X), arg(X).
sup(X) :- not nsup(X), arg(X).

inN(X) :- in(X).
inN(X) | outN(X) :- out(X).

% eq indicates whether a guess for S' is equal to the guess for S
eq_upto(Y) :- inf(Y), in(Y), inN(Y).
eq_upto(Y) :- inf(Y), out(Y), outN(Y).

eq_upto(Y) :- succ(Z,Y), in(Y), inN(Y), eq_upto(Z).
eq_upto(Y) :- succ(Z,Y), out(Y), outN(Y), eq_upto(Z).

eq :- sup(Y), eq_upto(Y). 

undefeated_upto(X,Y) :- inf(Y), outN(X), outN(Y).
undefeated_upto(X,Y) :- inf(Y), outN(X),  not defeat(Y,X).

undefeated_upto(X,Y) :- succ(Z,Y), undefeated_upto(X,Z), outN(Y).
undefeated_upto(X,Y) :- succ(Z,Y), undefeated_upto(X,Z), not defeat(Y,X).

undefeated(X) :- sup(Y), undefeated_upto(X,Y).

%% spoil if S' equals S for all preferred extensions
spoil :- eq.

%% S' has to be conflictfree - otherwise spoil
spoil :- inN(X), inN(Y), defeat(X,Y).

%% S' has to be admissible - otherwise spoil
spoil :- inN(X), outN(Y), defeat(Y,X), undefeated(Y).

inN(X) :- spoil, arg(X).
outN(X) :- spoil, arg(X).

%% do the final spoil-thing ...
:- not spoil.