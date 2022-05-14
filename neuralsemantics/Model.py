from neuralsemantics import BFNN
from pyparsing import *
import sys

ParserElement.enablePackrat()
sys.setrecursionlimit(2000)

class Model:
    def __init__(self, net, prop_map):
        """
        Constructor for a Model, i.e. an *interpreted* BFNN.

        Parameters:
            net - a BFNN
            prop_map - a dictionary mapping 'string' proposition labels
                to sets of nodes in the net
        """
        self.net = net
        self.prop_map = prop_map

    def interpret(self, formula):
        """
        Function to give the model's interpretation of a formula

        Parameters:
            'formula' - A string containing the following tokens,
                well-formed, separated by spaces:
                  'top' 'bot' 'not'
                  'and' 'or' 'implies'
                  'pref' 'up'
                any proposition label that is not one of the above
        Returns:
            A set of 'string' nodes
        """
        return self._eval(self._parse(formula)[0])

    def _eval(self, e):
        """
        Helper function to actually perform the evaluation of a parsed
        expression 'e'.

        FUTURE FUNCTIONALITY: Support for interpreting backpropagation
          as a dynamic update operator
        """
        if e in ['top', "⊤"]:
            return set()
        elif e in ['bot', "⊥"]:
            return set(self.net.nodes)
        elif type(e) == str:
            return self.prop_map[e]
        elif e[0] in ['not', '¬']:
            return set(self.net.nodes).difference(self._eval(e[1]))
        elif e[1] in ['and', '∧']:
            return self._eval(e[0]).union(self._eval(e[2]))
        elif e[1] in ['or', '∨']:
            return self._eval(e[0]).intersection(self._eval(e[2]))
        elif e[1] in ['implies', '→']:
            if self._eval(e[2]).issubset(self._eval(e[0])):
                return set()
            else:
                return set(self.net.nodes)
        elif e[1] in ['iff', '↔']:
            if (self._eval(e[2]).issubset(self._eval(e[0]))
                and self._eval(e[0]).issubset(self._eval(e[2]))):
                return set()
            else:
                return set(self.net.nodes)
        elif e[0] in ['prefers', '◻']:
            return self.net.propagate(self._eval(e[1]))
        elif e[1] in ['typicallyimplies', '⇒']:
            return self._eval([['◻', e[0]], '→', e[2]])
        elif e[1] in ['update', '+']:
            new_net = self.net.hebb_update(self._eval(e[0]))
            new_model = Model(new_net, self.prop_map)
            return new_model._eval(e[2])
        else:
            print(f"ERROR: Expression {e} is not supported.")

    def _parse(self, formula):
        """
        Helper function to parse a 'string' formula into a nested 
        list of lists.

        When parsing, we consider tokens in reverse order of their binding 
        strength, i.e.:
            implies, or, and, not, top, bot

        FUTURE FUNCTIONALITY: Support for interpreting backpropagation
          as a dynamic update operator
        """
        proposition = Word(alphas)
        grammar = infix_notation(proposition | "bot" | "top" | "⊥" | "⊤",
            [
                # Support for english longhand (easier to type)
                ('update',      2, OpAssoc.RIGHT),
                ('prefers',    1, OpAssoc.RIGHT),
                ('not',     1, OpAssoc.RIGHT),
                ('and',     2, OpAssoc.LEFT),
                ('or',      2, OpAssoc.LEFT),
                ('implies', 2, OpAssoc.RIGHT),
                ('iff',     2, OpAssoc.RIGHT),
                ('typicallyimplies', 2, OpAssoc.RIGHT),
                # Support for ascii symbols (easier to read)
                ('+', 2, OpAssoc.RIGHT),
                ('◻', 1, OpAssoc.RIGHT),
                ('¬', 1, OpAssoc.RIGHT),
                ('∧', 2, OpAssoc.LEFT),
                ('∨', 2, OpAssoc.LEFT),
                ('→', 2, OpAssoc.RIGHT),
                ('↔', 2, OpAssoc.RIGHT),
                ('⇒', 2, OpAssoc.RIGHT)
            ])

        return grammar.parse_string(formula)

    def is_model(self, formula):
        """
        Function to determine whether this model is a model of the 
        given 'formula'

        Returns True   iff   self |= formula
        """
        return self.interpret(formula) == set()

    def is_model_of_rule(self, premises, conclusion):
        """
        Function to determine whether this model is a model of a
        given *inference rule*.

        Given
             premises
            ----------
            conclusion
        and this model self, we check that
            self |= premises   implies   self |= conclusion

        Parameters:
            premises - a list of str formulas
            conclusion - a str formula
        """
        premises_sat = len(list(filter(lambda p: not(self.is_model(p)), premises))) == 0
        conclusion_sat = self.is_model(conclusion)
        return not(premises_sat) or conclusion_sat

    def construct_model(self, axioms):
        """
        Function to construct a BFNN model from a set of axioms
        (i.e. a set of formulas).
        """
        # FUTURE FUNCTIONALITY
        pass

    def extract_from_model(self):
        """
        Function to extract a set of axioms (i.e. a set of formulas)
        from a BFNN model.
        """
        # FUTURE FUNCTIONALITY
        pass

    def __str__(self):
        """
        """
        result = ""

        result += str(self.net)
        result += f"Prop Map: {self.prop_map}\n"

        return result

# Do a test of the syntax parser.
if __name__ == "__main__":
    # Testing parsing
    ParserElement.enablePackrat()
    proposition = Word(alphas)
    grammar = infix_notation(proposition | "bot" | "top" | "⊥" | "⊤",
        [
            # Support for ascii symbols (easier to read)
            ('+', 2, OpAssoc.RIGHT),
            ('◻', 1, OpAssoc.RIGHT),
            ('¬', 1, OpAssoc.RIGHT),
            ('∧', 2, OpAssoc.LEFT),
            ('∨', 2, OpAssoc.LEFT),
            ('→', 2, OpAssoc.RIGHT),
            ('↔', 2, OpAssoc.RIGHT),
            ('⇒', 2, OpAssoc.RIGHT)
        ])
    #print(grammar.parse_string("(p+ □ q) → (□ p+ q)"))
    print("Example 1: ", grammar.parse_string("(q → p) → ((q+ (◻r)) → (p+ (◻r)))"))
    print("Example 2: ", grammar.parse_string("((¬(P ∧ (P+ A)) ↔ ⊤) ∧ ((P ∧ (P+ A)) ⇒ (P+ B))) ∨ ((P ∧ (P+ A)) ↔ ⊤) ∧ ((P+ A) ⇒ (P+ B)))"))

