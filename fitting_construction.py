from dataclasses import dataclass
from itertools import chain
from typing import Dict, List, Optional, Set, Tuple


PropVar = str

@dataclass
class Literal:
	var: PropVar
	positive: bool

Label = bool
DecisionPair = Tuple[Literal, Label]

@dataclass(frozen=True)
class Example:
	assignments: Dict[PropVar, int]
	positive: Label

def legal_eliminations(lit: Literal, examples: List[Example]) -> Optional[Tuple[DecisionPair, List[Example]]]:
	# Relative assignments are 1 for positive literals, 0 for negative
	relevant_assignment = 1 if lit.positive else 0
	rel_examples = list(filter(lambda e: e.assignments[lit.var] == relevant_assignment, examples))
	labels = set([assignment.positive for assignment in rel_examples])
	if len(labels) != 1:
		return None
	# All (relevant) examples agree on label
	lab = tuple(labels)[0]
	# Return the value for (`lit`,`lab`) and all examples that can be eliminated
	return tuple([tuple([lit, lab]), rel_examples])

def build_decision_list(examples: List[Example]) -> Optional[List[DecisionPair]]:
	if examples == []:
		return []
	# Assusimg all examples have identical propositional variales
	PROP = examples[0].assignments.keys()
	literals = chain.from_iterable((Literal(p, True), Literal(p, False)) for p in PROP)
	possible_decision_pairs = filter(lambda l: l is not None, (legal_eliminations(l, examples) 
		for l in literals))
	# Order from most to least eliminable examples
	def key(p: Tuple[DecisionPair, List[Example]]) -> int:
		return 0 if p is None else -len(p[1])
	sorted_decision_pairs = sorted(possible_decision_pairs, key=key)

	# No legal eliminations, no fitting concept
	if not sorted_decision_pairs:
		raise ValueError('NOFIT')
	else:
		# Choose decision pair that removes the most examples
		decision_pair, removed_examples = sorted_decision_pairs[0]
		remaining_examples = [e for e in examples if e not in removed_examples]
		# Recursively build decision list
		return [decision_pair] + build_decision_list(remaining_examples)


def FITTING_EXISTENCE(examples: List[Example]) -> bool:
	try:
		build_decision_list(examples)
	except ValueError:
		return False
	return True

def FITTING_CONSTRUCTION(examples: List[Example]) -> bool:
	return build_decision_list(examples)


###### EXAMPLES ######

ex_1 = [Example({'p1': 1, 'p2': 0, 'p3': 0}, True),
		Example({'p1': 1, 'p2': 0, 'p3': 1}, True),
		Example({'p1': 1, 'p2': 1, 'p3': 0}, False),
		Example({'p1': 0, 'p2': 1, 'p3': 0}, False),
		Example({'p1': 0, 'p2': 0, 'p3': 1}, True),
		Example({'p1': 0, 'p2': 0, 'p3': 0}, False)]

ex_2 = [Example({'p1': 0, 'p2': 0, 'p3': 0}, True),
		Example({'p1': 0, 'p2': 0, 'p3': 1}, False),
		Example({'p1': 0, 'p2': 1, 'p3': 0}, False),
		Example({'p1': 0, 'p2': 1, 'p3': 1}, True)]

ex_3 = [Example({'p1': 0}, True),
		Example({'p1': 1}, True)]

if __name__ == "__main__":
	print(FITTING_CONSTRUCTION(ex_1))
	print(FITTING_EXISTENCE(ex_1))
	print(FITTING_EXISTENCE(ex_2))
	print(FITTING_CONSTRUCTION(ex_3))


	

