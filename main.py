from typing import List, Set, Tuple, FrozenSet, Dict
from typing import List
import random
import time

class Graph:
    def __init__(self):
        self.arguments: List = []
        self.attacks: List[Tuple[str, str]] = []  # (attacker, attacked)
        self.attacks_map: Dict[str, Set[str]] = {}  # attacker -> set of attacked
        self.attackers_map: Dict[str, Set[str]] = {}  # attacked -> set of attackers
        self.s = 0

    def add_argument(self, argument):
        """Adds an argument to the graph."""
        self.arguments.append(argument)

        self.attacks_map[argument] = set()
        self.attackers_map[argument] = set()

    def add_attack(self, attacker, attacked):
        """Adds an attack relation to the graph."""
        self.attacks.append((attacker, attacked))

        self.attacks_map[attacker].add(attacked)
        self.attackers_map[attacked].add(attacker)

    def attacks_any_in_set(self, candidate: str, current_set: Set[str]) -> bool:
        """
        Checks if the candidate argument attacks any argument in the current_set.
        Returns:
            True if candidate attacks any in current_set, False otherwise.
        """
        return bool(self.attacks_map.get(candidate, set()) & current_set)

    def attacked_by_any_in_set(self, candidate: str, current_set: Set[str]) -> bool:
        """
        Checks if the candidate argument is attacked by any argument in the current_set.
        Returns:
            True if candidate is attacked by any in current_set, False otherwise.
        """
        return bool(self.attackers_map.get(candidate, set()) & current_set)

    def attacks_any_args(self, candidate: str) -> bool:
        """
        Checks if the candidate argument attacks any argument in the current_set.
        Returns:
            True if candidate attacks any in current_set, False otherwise.
        """
        return bool(self.attacks_map.get(candidate, set()))

    def attacked_by_any_args(self, candidate: str) -> bool:
        """
        Checks if the candidate argument is attacked by any argument in the current_set.
        Returns:
            True if candidate is attacked by any in current_set, False otherwise.
        """
        return bool(self.attackers_map.get(candidate, set()))

    def conflict_free(self) -> Set[FrozenSet[str]]:
        """
        Finds all conflict-free sets in the argumentation framework using a backtracking approach.
        Returns:
            A set of frozensets, each representing a conflict-free set of argument names.
        """

        arguments = [argument for argument in self.arguments]

        arguments.sort()

        conflict_free_sets = set()

        def backtrack(start_index: int, current_set: List[str]):

            conflict_free_sets.add(frozenset(current_set))

            for i in range(start_index, len(arguments)):
                candidate = arguments[i]
                
                if candidate in self.attacks_map.get(candidate, set()):

                    continue

                if self.attacks_any_in_set(candidate, set(current_set)):

                    continue

                if self.attacked_by_any_in_set(candidate, set(current_set)):

                    continue

                current_set.append(candidate)

                backtrack(i + 1, current_set)
                current_set.pop()

        backtrack(0, [])
        self.conflict_free = conflict_free_sets
        return conflict_free_sets

    def is_set_defended(self, current_set):
        def defended_by_set(item: str):
            if not self.attacked_by_any_args(item):
                return True
            else:
                return all(
                    self.attacked_by_any_in_set(attacker, current_set)
                    for attacker in self.attackers_map[item]
                )

        return all(defended_by_set(item) for item in current_set)

    def admissible(self) -> Set[FrozenSet[str]]:
        self.admissible = [
            con_free
            for con_free in self.conflict_free
            if self.is_set_defended(con_free)
        ]
        return self.admissible

    def is_admissible(self, current_set) -> Set[FrozenSet[str]]:
        return self.is_set_defended(current_set)

    def is_set_attack_out(self, current_set):
        out = set(self.arguments).difference(current_set)
        return all(self.attacked_by_any_in_set(item, current_set) for item in out)

    def stable(self) -> Set[FrozenSet[str]]:
        self.stable = [
            con_free
            for con_free in self.conflict_free
            if self.is_set_attack_out(con_free)
        ]
        return self.stable

    def can(self, current_set: Set[str]) -> bool:
        """
        Checks if there exists an argument outside current_set that is defended by adding it (and possibly others).
        If such an argument exists, then current_set is not maximal.
        """
        def defended_by_set(item: str):
            candidate_set = current_set.union({item})
            
            if self.attacks_any_in_set(item, candidate_set):
                return False
            
            if self.attacked_by_any_in_set(item, candidate_set):
                return False

            if not self.attacked_by_any_args(item):
                return True

            if all(
                self.attacked_by_any_in_set(attacker, candidate_set)
                for attacker in self.attackers_map[item]
            ):
                return True

            return self.is_defended_iterative(item, current_set)

        out = set(self.arguments).difference(current_set)

        return any(defended_by_set(item) for item in out)

    def is_con_free(self, candidate, current_set):
        if self.attacks_any_in_set(candidate, current_set):

            return False

        if self.attacked_by_any_in_set(candidate, current_set):

            return False

        return True

    def is_defended_iterative(self, candidate: str, current_set: Set[str]) -> bool:
        """
        Attempt to defend 'candidate' by possibly adding defenders iteratively.
        We start from candidate_set = current_set ∪ {candidate}, which must remain conflict-free.
        For each attacked argument in candidate_set, we ensure there is a defender in candidate_set.
        If not, we try adding a suitable defender without causing conflicts.
        We repeat this process until no more changes are possible.
        If all arguments are defended (or not attacked) at the end, return True; else False.
        """

        candidate_set = set(current_set)
        candidate_set.add(candidate)

        if not self.is_con_free_set(candidate_set):
            return False

        while True:
            changed = False

            for arg in list(candidate_set):

                if not self.attacked_by_any_args(arg):
                    continue

                undefended_attackers = []
                for attacker in self.attackers_map[arg]:

                    if not self.attacked_by_any_in_set(attacker, candidate_set):
                        undefended_attackers.append(attacker)

                if not undefended_attackers:

                    continue

                defended_arg = False
                for attacker in undefended_attackers:

                    defenders = self.attackers_map[attacker]

                    for d in defenders:
                        if d not in candidate_set:
                            new_set = candidate_set.union({d})

                            if self.is_con_free_set(new_set):
                                candidate_set = new_set
                                changed = True
                                defended_arg = True
                                break
                    if defended_arg:

                        break

                if not defended_arg:

                    return False

            if not changed:

                for a in candidate_set:
                    if self.attacked_by_any_args(a):

                        for att in self.attackers_map[a]:
                            if not self.attacked_by_any_in_set(att, candidate_set):

                                return False

                return True

    def is_con_free_set(self, subset: Set[str]) -> bool:
        """
        Check if a given set of arguments 'subset' is conflict-free.
        Conflict-free means no argument in 'subset' attacks another argument in 'subset'.
        """
        for a in subset:
            if self.attacks_map[a] & subset:
                return False
        return True

    def preferred(self) -> Set[FrozenSet[str]]:
        self.preferred = [addm for addm in self.admissible if not self.can(addm)]

        if len(self.preferred) > 1:
            self.preferred = [item for item in self.preferred if len(item) > 0]

        # Double check to eliminate any subsets
        maximal_sets = set(self.preferred)
        for s1 in self.preferred:
            for s2 in self.preferred:
                if s1 != s2 and s1.issubset(s2):
                    if s1 in maximal_sets:
                        maximal_sets.remove(s1)

        self.preferred = maximal_sets
        return maximal_sets
    
    def is_conflict_free(self, candidate_set: Set[str]) -> bool:

        for arg in candidate_set:
            if self.attacks_map[arg] & candidate_set:
                return False
        return True

def parse_input(input_string: str) -> Graph:
    graph = Graph()
    args_dict = {}

    for line in input_string.strip().splitlines():
        line = line.strip().rstrip(".")
        if line.startswith("arg("):

            arg_id = line[4:-1]
            arg = arg_id
            graph.add_argument(arg)
            args_dict[arg_id] = arg
        elif line.startswith("att("):

            attacker_id, attacked_id = line[4:-1].split(",")
            attacker = args_dict.get(attacker_id.strip())
            attacked = args_dict.get(attacked_id.strip())
            if attacker and attacked:
                graph.add_attack(attacker, attacked)
            else:
                raise ValueError(f"Invalid attack relation: {line}")

    return graph

def generate_random_argumentation_framework(num_args: int, num_attacks: int) -> str:
    """
    Generates a random argumentation framework with a given number of arguments and attacks,
    ensuring attacks are more evenly distributed among arguments.

    Args:
        num_args: Number of arguments (n).
        num_attacks: Number of attacks to generate.

    Returns:
        A string representing the random argumentation framework with arguments and attacks.
    """

    max_possible_attacks = num_args * (num_args - 1)  # No self-attacks
    if num_attacks > max_possible_attacks:
        raise ValueError(
            f"Number of attacks ({num_attacks}) exceeds the maximum possible ({max_possible_attacks}) without self-attacks."
        )

    arguments = [f"arg({i})" for i in range(1, num_args + 1)]

    if num_attacks == 0 or num_args < 2:
        return "\n".join(arg + "." for arg in arguments)

    base_attacks_per_arg = num_attacks // num_args
    remainder = num_attacks % num_args

    attacks_per_argument = [
        base_attacks_per_arg + (1 if i < remainder else 0) for i in range(num_args)
    ]

    arg_indices = list(range(num_args))
    random.shuffle(arg_indices)

    attacks = set()
    used_targets = [
        set() for _ in range(num_args)
    ]  # Track targets used by each argument to avoid duplicates

    possible_targets_list = [set(range(num_args)) - {i} for i in range(num_args)]

    for i in arg_indices:
        targets_needed = attacks_per_argument[i]

        available_targets = possible_targets_list[i] - used_targets[i]

        if len(available_targets) < targets_needed:
            targets_needed = len(available_targets)

        if targets_needed > 0:

            available_targets_list = list(available_targets)
            chosen_targets = random.sample(available_targets_list, targets_needed)

            for t in chosen_targets:
                attacks.add((i + 1, t + 1))  # Arg numbering is 1-based
                used_targets[i].add(t)

    while len(attacks) < num_attacks:
        a, b = random.sample(range(1, num_args + 1), 2)
        if a != b:
            attacks.add((a, b))

    result = []
    for arg in arguments:
        result.append(arg + ".")

    for a, b in attacks:
        result.append(f"att({a},{b}).")

    return "\n".join(result)

def display_sets(sets: Set[FrozenSet[str]]):
    print("Sets:")
    for item in sorted(sets, key=lambda x: (len(x), sorted(x))):
        if item:
            print(", ".join(sorted(item, key=lambda x: x)))
        else:
            print("{}")  # Representing the empty set

input_string = """
arg(1).
arg(2).
arg(3).
arg(4).
arg(5).
arg(6).
arg(7).
arg(8).
att(1,2).
att(2,3).
att(3,4).
att(4,5).
att(5,6).
att(6,7).
att(7,8).
att(8,1).
att(2,5).
att(4,7).
att(6,1).
"""

if __name__ == "__main__":

    num_arguments = 20  # Set number of arguments, e.g., 10
    num_attacks = 30

    input_string = generate_random_argumentation_framework(num_arguments, num_attacks)

    graph = parse_input(input_string)

    start_time = time.time()
    graph.conflict_free()
    graph.admissible()
    graph.preferred()
    print()

    end_time = time.time()
    execution_time = end_time - start_time
    print(f"Execution time: {execution_time:.6f} seconds")
    display_sets(graph.preferred)
