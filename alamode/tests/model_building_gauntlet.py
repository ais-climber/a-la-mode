# I'm just going to randomly generate Preferential Models and make
# sure that the equivalent net still satisfies the same sentences.

import networkx as nx
import random as rand

from alamode.activation_functions import binary_step
from alamode.FeedforwardNet import FeedforwardNet
from alamode.InterpretedNet import InterpretedNet
from alamode.PrefModel import PrefModel
from alamode.model_building import *
from alamode.countermodel_search import *


# TODO