"""
A collection of activation functions.
"""
import tensorflow as tf
from tensorflow import Tensor
import numpy as np

def binary_relu(x : Tensor) -> Tensor:
            """
            A binary rectified linear (ReLU) activation function.

            Technically, we are using ReLU for the activation, and then we
            binarize the output (and keep it non-negative again using ReLU).  
            But tensorflow conflates activation and output, so we combine the two here.

            This function just checks whether ReLU applied to the input 
            vector 'x' exceeds 'self.thresholds'.  If so, we return a vector
            of 1's, otherwise we return a vector of 0's.
            """
            THRESHOLD = 0.0

            thres_tensor = np.full(x.get_shape()[0], THRESHOLD)

            return tf.keras.activations.relu(tf.sign(tf.subtract(tf.keras.activations.relu(x), thres_tensor)))
