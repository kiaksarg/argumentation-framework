

import time
import clingo
from typing import Set, FrozenSet, List
import matplotlib.pyplot as plt
from main import parse_input as parse_input0, generate_random_argumentation_framework, Graph
import random
import csv

def parse_and_build_graph(input_string: str) -> Graph:
    """
    Parses the input string (with 'arg(x)' and 'att(x,y)') and builds a Graph.
    """
    graph = Graph()

    arg_lines = [line.strip() for line in input_string.splitlines() if line.strip().startswith("arg(")]
    for line in arg_lines:

        num_str = line.replace("arg(", "").replace(").", "")
        graph.add_argument(num_str)

    att_lines = [line.strip() for line in input_string.splitlines() if line.strip().startswith("att(")]
    for line in att_lines:

        parts = line.replace("att(", "").replace(").", "").split(",")
        source_id = parts[0].strip()
        target_id = parts[1].strip()
        if source_id in graph.arguments and target_id in graph.arguments:
            graph.add_attack(source_id, target_id)

    return graph

def generate_random_argumentation_framework(num_args: int, num_attacks: int) -> str:
    """
    Generates a random argumentation framework with the given number of arguments and attacks.
    Returns a string in the desired format.
    """

    arguments = [f"arg({i})" for i in range(1, num_args + 1)]

    attacks = set()
    while len(attacks) < num_attacks:
        a, b = random.sample(range(1, num_args + 1), 2)
        attacks.add((a, b))

    result = []
    for arg in arguments:
        result.append(arg + ".")
    for a, b in attacks:
        result.append(f"att({a},{b}).")

    return "\n".join(result)

def run_clingo_with_predicate(asp_program: str, input_facts: str, predicate: str) -> Set[FrozenSet[str]]:
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

def main_comparison():

    asp_preferred = """
    %% An argument x defeats an argument y if x attacks y
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

    %% Sorting for determinism in ASP
    lt(X,Y) :- arg(X),arg(Y), X < Y.
    nsucc(X,Z) :- lt(X,Y), lt(Y,Z).
    succ(X,Y) :- lt(X,Y), not nsucc(X,Y).
    ninf(X) :- lt(Y,X).
    nsup(X) :- lt(X,Y).
    inf(X) :- not ninf(X), arg(X).
    sup(X) :- not nsup(X), arg(X).

    inN(X) :- in(X).
    inN(X) | outN(X) :- out(X).

    %% eq indicates whether a guess for S' is equal to the guess for S
    eq_upto(Y) :- inf(Y), in(Y), inN(Y).
    eq_upto(Y) :- inf(Y), out(Y), outN(Y).
    eq_upto(Y) :- succ(Z,Y), in(Y), inN(Y), eq_upto(Z).
    eq_upto(Y) :- succ(Z,Y), out(Y), outN(Y), eq_upto(Z).

    eq :- sup(Y), eq_upto(Y). 

    undefeated_upto(X,Y) :- inf(Y), outN(X), outN(Y).
    undefeated_upto(X,Y) :- inf(Y), outN(X), not defeat(Y,X).

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

    %% Final condition to ensure only preferred extensions are accepted
    :- not spoil.

    """

    argument_sizes = [10, 15, 20, 22, 25, 30]       # Number of arguments
    attack_counts = [5, 10, 20, 50, 100]           # Number of attacks

    results = []

    for num_args in argument_sizes:
        for num_attacks in attack_counts:
            max_possible_attacks = num_args * (num_args - 1)

            if num_args > 20 and num_args <= 25 and num_attacks < (num_args - 5):
                num_attacks = num_attacks + 5
                
            if num_args > 25 and num_attacks < (num_args - 5):
                num_attacks = num_attacks + 15

            num_attacks = min(num_attacks, max_possible_attacks)

            input_string = generate_random_argumentation_framework(num_args, num_attacks)
            graph = parse_and_build_graph(input_string)

            start_py = time.time()
            preferred_python = graph.conflict_free()
            preferred_python = graph.admissible()
            preferred_python = graph.preferred()
            end_py = time.time()
            python_time = end_py - start_py

            start_clingo = time.time()
            preferred_clingo = run_clingo_with_predicate(asp_preferred, input_string, predicate="in")
            end_clingo = time.time()
            clingo_time = end_clingo - start_clingo

            if preferred_python == preferred_clingo:
                match = True
            else:
                match = False

            results.append({
                'num_args': num_args,
                'num_attacks': num_attacks,
                'preferred_python_count': len(preferred_python),
                'preferred_clingo_count': len(preferred_clingo),
                'match': match,
                'python_time': python_time,
                'clingo_time': clingo_time
            })

            print(f"Args: {num_args}, Attacks: {num_attacks}, "
                  f"Python Preferred: {len(preferred_python)}, "
                  f"Clingo Preferred: {len(preferred_clingo)}, Match: {match}, "
                  f"Python Time: {python_time:.4f}s, Clingo Time: {clingo_time:.4f}s")

    for num_args in argument_sizes:
        subset = [r for r in results if r['num_args'] == num_args]
        attacks = [r['num_attacks'] for r in subset]
        python_times = [r['python_time'] for r in subset]
        clingo_times = [r['clingo_time'] for r in subset]

        plt.figure(figsize=(10, 6))
        plt.plot(attacks, python_times, marker='o', label='Python Time')
        plt.plot(attacks, clingo_times, marker='x', label='Clingo Time')
        plt.title(f'Execution Time Comparison (Args: {num_args})')
        plt.xlabel('Number of Attacks')
        plt.ylabel('Time (seconds)')
        plt.legend()
        plt.grid(True)
        plt.tight_layout()
        plt.savefig(f'preferred_comparison_args_{num_args}.png')  # Save each plot
        plt.close()

    plt.figure(figsize=(12, 8))
    for num_args in argument_sizes:
        subset = [r for r in results if r['num_args'] == num_args]
        attacks = [r['num_attacks'] for r in subset]
        python_times = [r['python_time'] for r in subset]
        clingo_times = [r['clingo_time'] for r in subset]

        plt.plot(attacks, python_times, marker='o', label=f'Python Args: {num_args}')
        plt.plot(attacks, clingo_times, marker='x', linestyle='--', label=f'Clingo Args: {num_args}')

    plt.title('Execution Time Comparison for Preferred Extensions')
    plt.xlabel('Number of Attacks')
    plt.ylabel('Time (seconds)')
    plt.legend()
    plt.grid(True)
    plt.tight_layout()
    plt.savefig('preferred_comparison_execution_time.png')
    plt.close()

    with open('comparison_results.csv', 'w', newline='') as csvfile:
        fieldnames = ['num_args', 'num_attacks', 'preferred_python_count', 'preferred_clingo_count', 'match', 'python_time', 'clingo_time']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

        writer.writeheader()
        for r in results:
            writer.writerow(r)

    print("\nComparison and plotting completed. Plots saved as 'preferred_comparison_args_{num_args}.png' and 'preferred_comparison_execution_time.png'. Results saved to 'comparison_results.csv'.")
    
if __name__ == "__main__":
    main_comparison()
