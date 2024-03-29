import tensorflow as tf
from tensorflow.keras.layers import Input, Dense
from keras import backend as K
import numpy as np
from functools import reduce
from itertools import chain, combinations

class Net:
    def __init__(self, nodes, layers, weights, activation_function, rate):
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
        self.nodes = nodes
        self.weights = weights
        self.layers = layers
        self.activation_function = activation_function 
                                   # TODO: support for separate activation function
                                   #   for each neuron; not strictly needed,
                                   #   but mentioned in paper
        self.rate = rate

        # Create the net and manually set its weights.
        self.tfnet = self.make_net()
        self._set_weights()

    def make_net(self):
        """

        """
        # Dynamically construct layered net based on our graph topology
        layer_widths = [len(layer) for layer in self.layers]
        input_layer = Input(shape=(layer_widths[0],))
        
        x = input_layer
        for width in layer_widths[1:-1]:
            x = Dense(width, activation=self.activation_function)(x)
        
        output_layer = Dense(layer_widths[-1], activation=self.activation_function)(x)
        return tf.keras.Model(inputs=input_layer, outputs=output_layer)

    def _set_weights(self):
        """
        Helper function to set the weights of 'self.tfnet' to all 0's,
        except for those weights mentioned in 'self.weights'.
        """
        for i in range(1, len(self.layers)):
            zero = np.array([0.0 for j in range(len(self.layers[i]))])
            new_weights = np.array([zero] * len(self.layers[i-1]))
            
            # Within this layer, set the weights that are mentioned in self.weights.
            for n1, n2 in self.weights.keys():
                if n1 in self.layers[i-1] and n2 in self.layers[i]:
                    index_n1 = self.layers[i-1].index(n1)
                    index_n2 = self.layers[i].index(n2)

                    new_weights[index_n1][index_n2] = self.weights[(n1, n2)]

            bias = self.tfnet.layers[i].get_weights()[1]
            self.tfnet.layers[i].set_weights([new_weights, bias])

    def _get_activation(self, xvec, layer1, layer2):
        """
        Helper function to get the activation output of 'layer' that results
        from passing 'xvec' into it.
        See:
            https://stackoverflow.com/questions/36812256/accessing-neural-network-weights-and-neuron-activations
        """
        get_nth_layer_output = K.function([self.tfnet.layers[layer1].output], # input
                                          [self.tfnet.layers[layer2].output]) # output

        inp = np.asarray([np.asarray(xvec)])
        layer_output = get_nth_layer_output(inp)[0][0]
        return list(layer_output)

    def reach(self, signal):
        """
        Function to get the set of nodes that are reachable from 'signal',
        in the sense of graph-reachability.
        """
        result = set()

        # Perform DFS on each node, and put the visited nodes in the result set.
        stack = list(signal)
        while stack != []:
            curr = stack.pop()
            if curr not in result:
                result.add(curr)
                for (e, w) in self.weights.items():
                    if e[0] == curr:
                        next = e[1]
                        stack.append(next)

        return result

    def inverse_reach(self, signal):
        """
        Function to get the set of nodes whose reach includes 'signal',
        i.e. the 'inverse' reach.
        
        Formally, we return
            {n | ∃m ∈ signal. m ∈ reach({n})}
        """
        result = set()

        for n in self.nodes:
            for m in signal:
                if m in self.reach(set({n})):
                    result.add(n)
                    break

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
        # Note:
        # Tensorflow is not designed to deal with multiple layers at once
        # (it can only consider propagations of a single layer at a time).
        # So we need to do the propagation layer by layer.  We start with
        # the first layer, propagate its signals to get the active neurons
        # in the next layer, etc.
        result = set(signal)
        for i in range(1, len(self.layers)):
            layer1 = self.layers[i-1]
            layer2 = self.layers[i]

            # We get the nodes activated in the next layer by this layer (along with
            # the original signal, since the signal may include neurons at this layer).
            xvec = [1.0 if (e in signal) or (e in result) else 0.0 for e in layer1]
            next_activation = self._get_activation(xvec, i-1, i)

            # Update result with both active neurons from the current layer
            # as well as the newly activated neurons from the next layer.
            result.update(set([layer2[k] for k in range(len(layer2)) 
                if next_activation[k] == 1.0]))

            # HELPFUL DEBUGGING OUTPUT:
            # print(f"layer1: {layer1}, layer2: {layer2}, input: {xvec}, output: {next_activation}")
            # print(f"current prop = {result}")

        return result
    
    def hebb_update(self, signal):
        """
        Function to perform one round of Hebbian learning.

        We propagate 'signal', and increase each weight W_ij by
            ΔW_ij = self.rate * x_i * x_j
        We then return the resulting net.
        """
        # First, populate new weights with every possible edge (including
        # those edges with weight 0).
        new_weights = self.weights.copy()
        for i in range(1, len(self.layers)):
            layer1 = self.layers[i-1]
            layer2 = self.layers[i]

            for n1 in layer1:
                for n2 in layer2:
                    if (n1, n2) not in new_weights.keys():
                        new_weights[(n1, n2)] = 0.0
        
        # We now increase every edge (by self.rate) if it was within
        # the propagation of 'signal'
        prop = self.propagate(signal)
        for n1, n2 in new_weights.keys():
            if n1 in prop and n2 in prop:
                new_weights[(n1, n2)] += self.rate

        # Finally, we filter out all of the '0' edges from the dictionary
        # (for prettiness, mostly)
        new_weights = {k : v for k , v in new_weights.items() if v != 0.0}

        return Net(self.nodes, self.layers, new_weights, self.activation_function, self.rate)

    def backprop_update(self, signal):
        """
        Function to perform one round of backpropagation.
        """
        # FUTURE FUNCTIONALTY
        pass

    def __str__(self):
        """
        String function for pretty printing

        TODO: Also make a function that gives us a pretty network
        diagram version of the neural net.
        """
        result = ""

        result += "Net\n"
        result += f"T = {self.activation_function} ; rate = {self.rate}\n"
        result += f"Nodes: {self.nodes}\n"
        result += f"Layers: {self.layers}\n"
        result += f"Weights: {self.weights}\n"

        return result