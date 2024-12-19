import clingo
from typing import Set, FrozenSet, Dict, List
from main import parse_input, generate_random_argumentation_framework
import unittest


class TestArgumentationFramework(unittest.TestCase):
    def setUp(self):

        self.input_string = """
arg(1).
arg(2).
arg(3).

att(1,2).
att(2,1).
        """

        self.input_string = generate_random_argumentation_framework(15, 30)

        self.asp_conflict_free = """
        % conflict_free.lp

        {confree(X): arg(X)}.
        
        :- att(X,Y), confree(X), confree(Y).
        
        #show confree/1.
        """

        self.asp_admissible = """
        % admissible.lp

        {set_item(X): arg(X)}. 
        
        :- att(X,Y), set_item(X), set_item(Y).

        attacked_by_set_item(A) :- set_item(B), att(B, A). 

        undefended(A) :- set_item(A), att(B, A), not attacked_by_set_item(B).

        :- undefended(A).
        """

        self.asp_stable = """
        % stable.lp

        {set_item(X): arg(X)}.
        :- att(X,Y), set_item(X), set_item(Y).
        attacked_by_set_item(A) :- set_item(B), att(B, A).
        
        % Admissibility
        undefended(A) :- set_item(A), att(B, A), not attacked_by_set_item(B).
        :- undefended(A).
        
        %Stable Set
        not_attaked(A):- arg(A), not set_item(A), not attacked_by_set_item(A).
        :- not_attaked(A).
        """
        self.asp_preferred = """

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
        """

        self.graph = parse_input(self.input_string)
        self.graph.conflict_free()
        self.graph.admissible()
        self.graph.stable()
        self.graph.preferred()

    def test_conflict_free(self):

        py_conflict_free = self.graph.conflict_free

        clingo_conflict_free = run_clingo_with_predicate(
            self.asp_conflict_free, self.input_string, predicate="confree"
        )

        py_conflict_free_set = set(py_conflict_free)

        self.assertEqual(
            py_conflict_free_set,
            clingo_conflict_free,
            f"Conflict-free sets differ.\nPython: {py_conflict_free_set}\nClingo: {clingo_conflict_free}",
        )
        print("test_conflict_free--------Success--------")


    def test_admissible(self):

        py_admissible = self.graph.admissible

        clingo_admissible = run_clingo_with_predicate(
            self.asp_admissible, self.input_string, predicate="set_item"
        )

        py_admissible_set = set(py_admissible)

        self.assertEqual(
            py_admissible_set,
            clingo_admissible,
            f"Admissible sets differ.\nPython: {py_admissible_set}\nClingo: {clingo_admissible}",
        )
        print("test_admissible--------Success--------")


    def test_stable(self):

        py_stable = self.graph.stable

        clingo_stable = run_clingo_with_predicate(
            self.asp_stable, self.input_string, predicate="set_item"
        )

        py_stable_set = set(py_stable)

        self.assertEqual(
            py_stable_set,
            clingo_stable,
            f"Stable sets differ.\nPython: {py_stable_set}\nClingo: {clingo_stable}",
        )
        print("test_stable--------Success--------")


    def test_preferred(self):

        py_preferred = self.graph.preferred

        clingo_preferred = run_clingo_with_predicate(
            self.asp_preferred, self.input_string, predicate="in"
        )

        py_preferred_set = set(py_preferred)

        self.assertEqual(
            py_preferred_set,
            clingo_preferred,
            f"Preferred sets differ.\nPython: {py_preferred_set}\nClingo: {clingo_preferred}",
        )

        print("test_preferred--------Success--------")

    def tearDown(self):
        pass  # Clean up resources if needed


def run_clingo_with_predicate(
    asp_program: str, input_facts: str, predicate: str
) -> Set[FrozenSet[str]]:
    """
    Runs Clingo with the given ASP program and input facts, extracting extensions based on the specified predicate.

    Args:
        asp_program (str): The ASP encoding as a string.
        input_facts (str): The argumentation framework facts as a string.
        predicate (str): The predicate used to represent inclusion in the extension (e.g., 'in_S', 'set_item', 'in').

    Returns:
        Set[FrozenSet[str]]: A set of extensions, each represented as a frozenset of arguments.
    """
    full_program = asp_program + "\n" + input_facts

    ctl = clingo.Control(arguments=["-n", "0"])
    ctl.add("base", [], full_program)
    ctl.ground([("base", [])])

    extensions = set()

    def on_model(model):
        atoms = model.symbols(shown=True)
        current_extension = set()
        for atom in atoms:
            if atom.name == predicate:
                if len(atom.arguments) != 1:
                    continue
                arg = str(atom.arguments[0])
                current_extension.add(arg)
        extensions.add(frozenset(current_extension))

    ctl.solve(on_model=on_model)

    return extensions


taf = TestArgumentationFramework()
taf.setUp()
taf.test_conflict_free()
taf.test_admissible()
taf.test_stable()
taf.test_preferred()

