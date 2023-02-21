import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout
import matplotlib.pyplot as plt

import numpy as np
from functools import reduce
from itertools import chain, combinations

class FeedforwardNet:
    def __init__(self, graph, activation_function, rate):
        """
        Constructor for a Net (binary feedforward neural network).
        
        NOTE: Currently our nets must be *binary* and *feedforward*.
        TODO: Plans to extend this to neural nets used in practice
              (e.g. fuzzy nets & RNNs)

        Parameters:
            'nodes' - a set of strings denoting node labels
            'layers' - a nested list manually separating the layers of the nodes
            'weights' - a dictionary mapping each node pair (i, j) to
                its weight (a float)
            'activation_function' - See 'activation_functions.py' for details
            'rate' - the learning rate (a float)
        """
        # First, make sure that the graph is actually feed-forward (acyclic)
        assert nx.is_directed_acyclic_graph(graph)

        self.nodes = list(nx.topological_sort(graph))
        self.graph = graph
        self.activation_function = activation_function
        self.rate = rate

    def reach(self, signal):
        """
        Function to get the set of nodes that are reachable from 'signal',
        in the sense of graph-reachability.
        """
        result = set(signal)

        for node in signal:
            result.update(set(nx.descendants(self.graph, node)))

        return result

    def inverse_reach(self, signal):
        """
        Function to get the set of nodes whose reach includes 'signal',
        i.e. the 'inverse' reach.
        
        Formally, we return
            {n | ∃m ∈ signal. m ∈ reach({n})}
        """
        result = set(signal)

        for node in signal:
            result.update(set(nx.ancestors(self.graph, node)))

        return result

    def propagate(self, signal):
        """
        Function to get the propagation of a signal 'signal'.
        
        We configure the net with the nodes in 'signal' all active,
        then forward-propagate these activations through the net.
        We return the resulting set of nodes that are active.

        Parameters:
            'signal' - a 'set' of neurons to be initially active
        """
        result = set(signal)

        # For each node, we check whether it is activated by preceding nodes.
        # Note that the nodes are topologically sorted (see the __init__).
        # This means we will always consider the activation of all nodes 
        # preceding 'n' before we consider 'n'.
        for node in self.nodes:
            # Skip nodes with no predecessors
            if self.graph.in_degree(node) == 0:
                continue
            
            preds = list(self.graph.predecessors(node))
            xvec = [1.0 if (m in result) else 0.0 for m in preds]
            wvec = [self.graph.get_edge_data(m, node)['weight'] for m in preds]

            # TODO: generalize for non-binary activation functions
            activation = self.activation_function(xvec, wvec)
            if activation == 1.0:
                result.add(node)

        return result

    def hebb_update(self, signal):
        """
        Function to perform one round of Hebbian learning.

        We propagate 'signal', and increase each weight W_ij by
            ΔW_ij = self.rate * x_i * x_j
        We then return the resulting net.
        """
        # TODO: ERROR -- the new net might be acyclic!
        # Fix this by only considering nodes (u, v) in the correct order,
        # given by topological sort.

        # First, populate new weights with every possible edge (including
        # those edges with weight 0 that don't show up in the edges).
        new_edges = []
        for u in self.nodes:
            for v in self.nodes:
                if (u, v) in self.graph.edges:
                    weight = self.graph.get_edge_data(u, v)['weight']
                    new_edges.append([u, v, weight])
                else:
                    new_edges.append([u, v, 0.0])
        
        # We now increase every edge (by self.rate) if it was within
        # the propagation of 'signal'
        prop = self.propagate(signal)
        for i in range(len(new_edges)):
            u = new_edges[i][0]
            v = new_edges[i][1]

            if u in prop and v in prop:
                # Update the weight
                new_edges[i][2] += self.rate

        # Finally, we filter out all of the '0' edges from the dictionary
        # (for prettiness, mostly)
        new_edges = [[u, v, weight] for [u, v, weight] in new_edges if weight != 0.0]
        
        new_graph = nx.DiGraph()
        new_graph.add_weighted_edges_from(new_edges)
        return FeedforwardNet(new_graph, self.activation_function, self.rate)

    def backprop_update(self, signal):
        """
        Function to perform one round of backpropagation.
        """
        # FUTURE FUNCTIONALTY
        pass

    def __str__(self):
        """
        String function for pretty printing
        """
        result = "\n"

        result += "Net\n"
        result += f"Act = {self.activation_function} ; rate = {self.rate}\n"
        result += f"Nodes: {self.nodes}\n"
        result += f"Graph: {str(self.graph)}\n"

        return result

    def draw(self, show_weights=True):
        """
        Function to draw neural net graph using networkx & matplotlib
        """
        # # Dynamic font sizing 
        # font = len(self.nodes)

        pos = graphviz_layout(self.graph, prog='dot', args="-Grankdir=LR")
        nx.draw(self.graph, with_labels=True, pos=pos, font_color='white', node_size=3000,font_size=45)

        if show_weights:
            labels = nx.get_edge_attributes(self.graph,'weight')
            nx.draw_networkx_edge_labels(self.graph,pos,edge_labels=labels, font_size=15)
        
        plt.show()

if __name__ == "__main__":
    # Quick sanity checks
    graph = nx.DiGraph()
    graph.add_weighted_edges_from(
        [['a', 'd', -1],
         ['a', 'e', -1],
         ['b', 'd', -1],
         ['b', 'e', -1],
         ['c', 'd', -1],
         ['c', 'e', 10],
         ['d', 'f', -1],
         ['e', 'f', 100]])

    pos = graphviz_layout(graph, prog='dot', args="-Grankdir=LR")
    nx.draw(graph, with_labels=True, pos=pos, font_weight='bold', font_color='white')

    # print(set(graph.nodes))

    # print(graph.edges)
    # print(graph.get_edge_data('a', 'd'))
    # print(dir(graph))

    net = FeedforwardNet(graph, None, None)
    
    # TEST REACH
    print(net.reach({'a', 'b'}))
    print(net.reach({'f'}))
    print(net.reach({'d', 'c'}))
    # plt.show()

    net.draw(show_weights=False)