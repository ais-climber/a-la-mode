"""
A collection of activation functions.
"""
import tensorflow as tf
from tensorflow import Tensor
import numpy as np

def binary_step(xvec, weights):
    """
    A binary step activation function.

    We just take the weighted sum of 'xvec' and 'weights', and return:
        1.0 if sum > THRESHOLD
        0.0 otherwise
    """
    THRESHOLD = 0.0
    assert len(xvec) == len(weights)

    total = sum([xvec[i]*weights[i] for i in range(len(xvec))])
    
    if total > THRESHOLD:
        return 1.0
    else:
        return 0.0
