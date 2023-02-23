"""
A collection of activation functions.

An activation function determines the activation value of a node
'n' from the activation of its predecessors m1,...,mk.

In traditional machine learning libraries (e.g. Tensorflow),
activation functions have type:
    func(xvec: Tensor) -> Tensor
or  func(xvec: list) -> list

where the second Tensor/list is of the same size.
i.e. the activation function is applied element-wise to the layer,
and applying the weights is done *afterwards*, when transitioning
to the next layer.

Here, we have a slightly generalized type for activation functions.
We require:
    binary_step(n : str, nodes_vec : list, x_vec : list, weights_vec : list) -> bool

- n           the particular node we want to know the activation of
- nodes_vec   lists the incoming nodes m1,...,mk
- x_vec       lists the incoming node activations
- weights_vec lists the weights for the incoming nodes

And rather than giving the activations for the entire next layer, we give
the single activation value for the particular node 'n'.
"""
import networkx as nx

def binary_step(n, m_vec, x_vec, weights_vec):
    """
    A binary step activation function.

    We just take the weighted sum of 'xvec' and 'weights', and return:
        1.0 if sum > THRESHOLD
        0.0 otherwise
    """
    size = len(m_vec)
    assert len(x_vec) == size
    assert len(weights_vec) == size
    THRESHOLD = 0.0
    
    total = sum([x_vec[i]*weights_vec[i] for i in range(size)])
    if total > THRESHOLD:
        return 1.0
    else:
        return 0.0
