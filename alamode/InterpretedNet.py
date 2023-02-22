from pyparsing import *
import sys

# Packages for drawing nets
import networkx as nx
import numpy as np
from itertools import combinations
from networkx.drawing.nx_agraph import graphviz_layout
import matplotlib.pyplot as plt
from matplotlib.path import Path
from matplotlib.patches import PathPatch

from scipy.spatial.distance import cdist
from scipy.spatial.ckdtree import cKDTree
from scipy.ndimage import gaussian_filter

from netgraph import Graph, get_sugiyama_layout, get_curved_edge_paths

ParserElement.enablePackrat()
sys.setrecursionlimit(2000)

class InterpretedNet:
    def __init__(self, net, prop_map):
        """
        Constructor for an Interpreted Net

        Parameters:
            net - a FeedforwardNet
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
        if e in ['top']:
            return set(self.net.nodes)
        elif e in ['bot']:
            return set()
        elif type(e) == str:
            # NOTE: In order for the interpretation to work, we need to take
            #       the *complement* of the proposition mapping!!!
            # 
            # TODO: Explain why this is what we should expect
            #       (it seems very counterintuitive!)
            # 
            prop_eval = self.prop_map[e]
            return set(self.net.nodes).difference(prop_eval)
        
        elif e[0] in ['not']:
            return set(self.net.nodes).difference(self._eval(e[1]))
        elif e[1] in ['and']:
            return self._eval(e[0]).intersection(self._eval(e[2]))
        elif e[1] in ['or']:
            return self._eval(e[0]).union(self._eval(e[2]))
        
        elif e[1] in ['->']:
            # Rewrite: A -> B == not A or B
            return self._eval([['not', e[0]], 'or', e[2]])
        elif e[1] in ['<->']:
            # Rewrite: A <-> B == (A -> B) and (B -> A)
            return self._eval([[e[0], '->', e[2]], 'and', [e[2], '->', e[0]]])
        
        elif e[0] in ['<know>']:
            return self.net.reach(self._eval(e[1]))
        elif e[0] in ['<know↓>']:
            return self.net.inverse_reach(self._eval(e[1]))
        elif e[0] in ['<typ>']:
            return self.net.propagate(self._eval(e[1]))

        elif e[0] in ['know']:
            # Rewrite: know A == not <know> not A
            return self._eval(['not', ['<know>', ['not', e[1]]]])
        elif e[0] in ['know↓']:
            return self._eval(['not', ['<know↓>', ['not', e[1]]]])
        elif e[0] in ['typ']:
            return self._eval(['not', ['<typ>', ['not', e[1]]]])
        
        # Hebbian Update
        # TODO: Change operator to something like 'hebb' to be more readable.
        elif e[1] in ['::']:
            new_net = self.net.hebb_update(self._eval(e[0]))
            new_model = InterpretedNet(new_net, self.prop_map)
            return new_model._eval(e[2])
        else:
            print(f"ERROR: Expression {e} is not supported.")

    def _parse(self, formula):
        """
        Helper function to parse a 'string' formula into a nested 
        list of lists.

        When parsing, we consider tokens in reverse order of their binding 
        strength, i.e.:
            <->, ->, or, and, not, top, bot

        FUTURE FUNCTIONALITY: Support for interpreting backpropagation
          as a dynamic update operator
        """
        restricted_alphas = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJLMNOPQRSUVWXYZ"
        proposition = Word(restricted_alphas)
        grammar = infix_notation(proposition | "bot" | "top",
            [
                ('::',      2, OpAssoc.RIGHT),
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
        given 'formula'

        Returns True   iff   self |= formula
        """
        return bool(self.interpret(formula) == set(self.net.nodes))

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

    def draw(self, show_labels=False):
        """
        Function to draw neural net graph using networkx & matplotlib

        TODO: Implement 'show_labels' to show sets corresponding to propositions
        """
        # Draw the graph for the net and get it's node positions and axis
        node_positions, ax = self.net.draw(show_labels)

        # TODO: Draw *all* the subsets, not just the one for 'A'
        for prop, nodes in self.prop_map.items():
            subset = list(nodes)

            if len(subset) == 0:
                # This subset is empty; do nothing
                return node_positions
            elif len(subset) == 1:
                # This subset is of size 1; just draw a circle around the
                # single element.
                print("TODO")
            else:
                # Construct the minimum spanning tree for the nodes in the subset.
                xy = np.array([node_positions[node] for node in subset])
                distances = cdist(xy, xy)
                h = nx.Graph()
                h.add_weighted_edges_from([(subset[ii], subset[jj], distances[ii, jj]) for ii, jj in combinations(range(len(subset)), 2)])
                h = nx.minimum_spanning_tree(h)

                # We compute an edge routing that avoids other nodes.
                edge_paths = get_curved_edge_paths(list(h.edges), node_positions, k=0.25, origin=(-0.5, -0.5), scale=(2, 2))
                
                # Use nearest neighbour interpolation to partition the canvas into 2 regions.
                # print("EDGE PATHS: ", edge_paths.values())
                xy1 = np.concatenate(list(edge_paths.values()), axis=0)
                z1 = np.ones(len(xy1))

                xy2 = np.array([node_positions[node] for node in node_positions if node not in subset])
                z2 = np.zeros(len(xy2))

                # Add a frame around the axes.
                # This reduces the desired mask in regions where there are no nearby point from the exclusion list.
                xmin, xmax = ax.get_xlim()
                ymin, ymax = ax.get_ylim()
                xx = np.linspace(xmin, xmax, 100)
                yy = np.linspace(ymin, ymax, 100)

                left = np.c_[np.full_like(xx, xmin), yy]
                top = np.c_[xx, np.full_like(yy, ymax)]
                right = np.c_[np.full_like(xx, xmax), yy]
                bottom = np.c_[xx, np.full_like(yy, ymin)]

                xy3 = np.concatenate([left, top, right, bottom])
                z3 = np.zeros((len(xy3)))

                xy = np.concatenate([xy1, xy2, xy3])
                z = np.concatenate([z1, z2, z3])
                tree = cKDTree(xy)
                xy_grid = np.meshgrid(xx, yy)
                _, indices = tree.query(np.reshape(xy_grid, (2, -1)).T, k=1)
                z_grid = z[indices].reshape(xy_grid[0].shape)

                # smooth output
                z_smooth = gaussian_filter(z_grid, 1.5)

                # Graph(g, edge_width=0.5, node_layout=node_positions, node_color=node_color, arrows=True, ax=axes[3])
                contour = ax.contour(xy_grid[0], xy_grid[1], z_smooth, np.array([0.9]), alpha=0)
                patch = PathPatch(contour.collections[0].get_paths()[0], facecolor='red', alpha=0.2, zorder=-1)
                ax.add_patch(patch)

        return node_positions

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
            ('knows',   1, OpAssoc.RIGHT),
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

