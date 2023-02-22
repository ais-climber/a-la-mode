import networkx as nx

import numpy as np
from functools import reduce
from itertools import chain, combinations
import matplotlib.pyplot as plt

from netgraph import Graph, get_sugiyama_layout, get_curved_edge_paths

class FeedforwardNet:
    def __init__(self, nodes, graph, activation_function, rate):
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

        self.nodes = nodes
        self.graph = graph
        self.activation_function = activation_function
        self.rate = rate

    def reach(self, signal):
        """
        Function to get the set of nodes that are reachable from 'signal',
        in the sense of graph-reachability.
        """
        # TODO: Why does networkx throw an error if the length is 1??
        if len(self.nodes) == 1:
            return signal

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
        # TODO: Why does networkx throw an error if the length is 1??
        if len(self.nodes) == 1:
            return signal

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
        sorted_nodes = list(nx.topological_sort(self.graph))

        # Topological sort will give an empty set if there are no edges.
        if sorted_nodes == []:
            return signal

        for node in sorted_nodes:
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
        # TODO: We don't actually update acyclic edges -- we should,
        # but it ends up violating the fact that the net is acyclic!

        # First, populate new weights with every possible edge (u, v)
        # where u shows up before v in the topological sort.
        # (The point is to include those edges with weight 0 that didn't show 
        # up before in the edges).
        sorted_nodes = list(nx.topological_sort(self.graph))
        new_edges = []

        # Topological sort will give an empty set if there are no edges.
        if sorted_nodes == []:
            return self

        for u in sorted_nodes:
            rest = sorted_nodes[sorted_nodes.index(u)+1:]

            for v in rest:
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
        return FeedforwardNet(self.nodes, new_graph, self.activation_function, self.rate)

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

    def draw(self, show_labels=False):
        """
        Function to draw neural net graph using networkx & matplotlib

        TODO: Implement 'show_labels' to show weight labels
        """
        fig, ax = plt.subplots()

        # Get the Sugiyama layout, then rotate the picture to be horizontal.
        node_positions = get_sugiyama_layout(list(self.graph.edges)) # a.k.a 'dot'
        node_positions = {node : np.asarray((-y, x)) for node, (x, y) in node_positions.items()}

        Graph(self.graph, edge_width=0.75, edge_cmap='coolwarm', node_layout=node_positions, 
            node_labels=show_labels, edge_labels=show_labels, node_label_fontdict=dict(size=20), node_color='gainsboro', arrows=True, ax=ax)

        return node_positions, ax

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

    net = FeedforwardNet(graph, None, None, 1.0)
    net.draw(show_weights=False)