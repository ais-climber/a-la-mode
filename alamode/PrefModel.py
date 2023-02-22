from itertools import chain, combinations
from pyparsing import *
import sys

ParserElement.enablePackrat()
sys.setrecursionlimit(2000)

class PrefModel:
    def __init__(self, worlds, f, g, prop_map):
        """
        Constructor for a neighborhood model,
        i.e. a classical possible worlds model.

        Unlike ordinary neighborhood models, we have *two* accessibility
        functions f and g.  So we can express different interactions between
        the two (e.g. X ∈ f(w) --> X ∈ g(w))

        Parameters:
            worlds - a 'set' of 'string' world labels
            f(w) - A 'dict' that maps worlds to *lists* of *sets* of worlds
                (think: The set of all "formulas" that hold at world w)
            g(w) - A 'dict' that maps worlds to *lists* of *sets* of worlds, like f(w)
            prop_map - a dictionary assigning 'bool' truth values to 
                (proposition, world) pairs, where 'proposition' and 'world' are 'string' labels.

        TODO: This and InterpretedNet share a lot of code.  Maybe I should
          refactor and write stock interpret, parse, and eval functions that
          both of them inherit from. (e.g.:
            Model.py  --> PrefModel.py
                      --> NetModel.py (formerly InterpretedNet.py) )
        """
        self.universe = worlds
        self.f = f
        self.g = g
        self.prop_map = prop_map

        # It is expensive to compute the powerset, so we initialize it here!
        self.powerset = list(chain.from_iterable(combinations(list(worlds), r) for r in range(len(list(worlds))+1)))

    def interpret(self, formula, world):
        """
        Function to give the model's interpretation of a formula,
        in a given world.

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
        return self._eval(self._parse(formula)[0], world)

    def _eval(self, e, w):
        """
        Helper function to actually perform the evaluation of a parsed
        expression 'e' at world 'w'

        TODO: PrefModel does not currently support learning operators,
            Hebbian or otherwise!

        TODO: Add type annotations throughout the code!  This function
            actually returns a 'bool', whereas InterpretedNet's _eval
            returns a 'set'!
        """
        if e in ['top']:
            return True
        elif e in ['bot']:
            return False
        elif type(e) == str:
            return self.prop_map[(e, w)]
        
        elif e[0] in ['not']:
            return not self._eval(e[1], w)
        elif e[1] in ['and']:
            return self._eval(e[0], w) and self._eval(e[2], w)
        elif e[1] in ['or']:
            return self._eval(e[0], w) or self._eval(e[2], w)
        
        elif e[1] in ['->']:
            return (not self._eval(e[0], w)) or self._eval(e[2], w)
        elif e[1] in ['<->']:
            return self._eval(e[0], w) == self._eval(e[2], w)
            
        elif e[0] in ['<know>']:
            return self._eval(['not', ['know', ['not', e[1]]]], w)
        elif e[0] in ['<know↓>']:
            return self._eval(['not', ['know↓', ['not', e[1]]]], w)
        elif e[0] in ['<typ>']:
            return self._eval(['not', ['typ', ['not', e[1]]]], w)
            
        elif e[0] in ['know']:
            truth_set = set([u for u in self.universe if self._eval(e[1], u)])

            if truth_set in self.f[w]:
                return True
            else:
                return False
        elif e[0] in ['know↓']:
            # TODO: IMPLEMENT know↓ !!!
            # (it's a little annoying, but it should just be a for-loop)
            pass
        elif e[0] in ['typ']:
            truth_set = set([u for u in self.universe if self._eval(e[1], u)])
            
            if truth_set in self.g[w]:
                return True
            else:
                return False
        else:
            print(f"ERROR: Expression {e} is not supported.")

    def _parse(self, formula):
        """
        Helper function to parse a 'string' formula into a nested 
        list of lists.

        When parsing, we consider tokens in reverse order of their binding 
        strength, i.e.:
            <->, ->, or, and, not, top, bot
        """
        restricted_alphas = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJLMNOPQRSUVWXYZ"
        proposition = Word(restricted_alphas)
        grammar = infix_notation(proposition | "bot" | "top",
            [
                ('know',    1, OpAssoc.RIGHT),
                ('know↓',   1, OpAssoc.RIGHT),
                ('typ',     1, OpAssoc.RIGHT),
                ('<know>',  1, OpAssoc.RIGHT),
                ('<know↓>', 1, OpAssoc.RIGHT),
                ('<typ>',   1, OpAssoc.RIGHT),
                ('not',     1, OpAssoc.RIGHT),
                ('and',     2, OpAssoc.LEFT),
                ('or',      2, OpAssoc.LEFT),
                ('->',      2, OpAssoc.RIGHT),
                ('<->',     2, OpAssoc.RIGHT),
            ])

        return grammar.parse_string(formula)

    def is_model(self, formula):
        """
        Function to determine whether this model is a model of the 
        given 'formula', i.e. whether 'formula' holds at every world
        in the model.
        """
        # We look for a counterexample, i.e. a world where
        # the formula is False.  If we can't find one, we return True.
        for w in self.universe:
            if not self.interpret(formula, w):
                return False

        return True

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

    #--------------------------------------------------------------------
    # Topology definitions & properties for neighborhood frames
    # 
    # TODO: These are all static, i.e. they all call on f, g independent
    # of self.f and self.g.  So we should move these to a separate file!
    #--------------------------------------------------------------------
    def core(self, f, w):
        """
        Function to get the core of f(w), i.e. the intersection
        of all sets X ∈ f(w)

        As a convention, if f(w) is empty, then the core is
        the whole universe (the intersection of nothing). See:
        https://math.stackexchange.com/questions/370188/empty-intersection-and-empty-union
        """
        result = set(self.universe)

        for X in f[w]:
            result.intersection_update(X)

        return result

    def is_closed_under_fin_intersection(self, f):
        """
        Function to check whether f is closed under finite intersection.

        Since our universe is *finite*, this is equivalent to checking
        if every f(w) contains its core.  This is much faster to compute.
        """
        # We look for a counterexample, i.e. some w such that the core 
        # is not in f(w).  If we can't find one, we return True.
        for w in self.universe:
            # If there are no sets in f[w], then f[w] is trivially
            # closed under intersection.
            if f[w] == []:
                continue

            elif self.core(f, w) not in f[w]:
                return False

        return True

    def is_closed_under_superset(self, f):
        """
        Function to check whether f is closed under superset.

        NOTE: This check is exponential!  I can't think of a good 
          way to avoid iterating through the powerset.
        """
        # We look for a counterexample, i.e. some w and some set X in f(w)
        # with some superset Y *not* in f(w). If we can't find one,
        # we return True.
        for w in self.universe:
            for X in f[w]:
                for Y in self.powerset:
                    if set(Y).issuperset(X):
                        if set(Y) not in f[w]:
                            return False

        return True

    def is_reflexive(self, f):
        """
        Function to check whether f is reflexive, i.e.
        whether every w is in the core of w.
        """
        # We look for a counterexample, i.e. a world that is not in 
        # its own core. If we can't find one, we return True.
        for w in self.universe:
            if w not in self.core(f, w):
                return False

        return True

    def is_transitive(self, f):
        """
        Function to check whether f is transitive, i.e.
        for all w, X, if X ∈ f(w) then
                     {u | X ∈ f(u)} ∈ f(w)
        """
        # We look for a counterexample, i.e. a world w and a set X
        # such that X ∈ f(w), but the set {u | X ∈ f(u)} is not in f(w).
        for w in self.universe:
            for X in f[w]:
                X_set = set([u for u in self.universe if X in f[u]])

                if X_set not in f[w]:
                    return False
        
        return True

    def is_acyclic(self, f):
        pass

    def g_contains_f(self, f, g):
        """
        Function to check whether g contains f, i.e.
        for all w, if X ∈ f(w) then X ∈ g(w)
        """
        for w in self.universe:
            for X in f[w]:
                if X not in g[w]:
                    return False

        return True

    def f_is_skeleton_of_g(self, f, g):
        """
        Function to check whether f is a skeleton of g, i.e.
        for all w, X,
            if   {u | X ∈ g(u)} U complement(core(f, w)) ∈ g(w)
            then X ∈ g(w)

        NOTE: This check is exponential!  I can't think of a good 
          way to avoid iterating through the powerset.
        """
        # We look for a counterexample, i.e. a world w and a set X
        # such that {u | X ∈ g(u)} U complement(core(f, w)) ∈ g(w),
        # but X is *not* in g(w).

        for w in self.universe:
            for X in self.powerset:
                X_set = set([u for u in self.universe if set(X) in g[u]])
                compl_core = self.universe.difference(self.core(f, w))

                if X_set in g[w] and set(X) not in g[w]:
                    return False

        return True



    #--------------------------------------------------------------------

    def __str__(self):
        """
        """
        result = ""

        result += str(self.universe) + "\n\n"
        result += f"f map: {self.f}\n\n"
        result += f"g map: {self.g}\n\n"
        result += f"Prop Map: {self.prop_map}\n"

        return result

# Do a test of the syntax parser.
if __name__ == "__main__":
    # Testing parsing
    ParserElement.enablePackrat()
    restricted_alphas = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJLMNOPQRSUVWXYZ"
    proposition = Word(restricted_alphas)
    grammar = infix_notation(proposition | "bot" | "top" | "⊥" | "⊤",
        [
            # Support for english longhand (easier to type)
            ('up',      2, OpAssoc.RIGHT),
            ('knows',     1, OpAssoc.RIGHT),
            ('typ',     1, OpAssoc.RIGHT),
            ('not',     1, OpAssoc.RIGHT),
            ('and',     2, OpAssoc.LEFT),
            ('or',      2, OpAssoc.LEFT),
            ('implies', 2, OpAssoc.RIGHT),
            ('iff',     2, OpAssoc.RIGHT),
            # Support for ascii symbols (easier to read)
            ('+', 2, OpAssoc.RIGHT),
            ('K', 1, OpAssoc.RIGHT),
            ('T', 1, OpAssoc.RIGHT),
            ('¬', 1, OpAssoc.RIGHT),
            ('∧', 2, OpAssoc.LEFT),
            ('∨', 2, OpAssoc.LEFT),
            ('→', 2, OpAssoc.RIGHT),
            ('↔', 2, OpAssoc.RIGHT)
        ])
    #print(grammar.parse_string("(p+ □ q) → (□ p+ q)"))
    print("Example 1: ", grammar.parse_string("(q → p) → ((q+ (T r)) → (p+ (T r)))"))
    print("Example 2: ", grammar.parse_string("((¬(P ∧ (P+ A)) ↔ ⊤) ∧ ((P ∧ (P+ A)) → (P+ B))) ∨ ((P ∧ (P+ A)) ↔ ⊤) ∧ ((P+ A) → (P+ B)))"))
    print("Example 2: ", grammar.parse_string("((T oronto) implies ennessee) and otoro"))

