# Neural Semantics
A neuro-symbolic interface, intended for both **model extraction** (extracting knowledge from a net) as well as **model building** (building a net from a knowledge base).  The name comes from the core idea -- that the internal dynamics of neural networks can be used as formal semantics of knowledge bases.

![image](https://user-images.githubusercontent.com/7096372/168408611-afc0ed06-ade7-4854-98f8-e8d564765c33.png)

## :heavy_check_mark: Supported Features:
- Model extraction
- Countermodel generation (via a random search, no construction yet)
- Modal and conditional reasoning
- Inferring what the net has learned before and after learning

## ❗ Current Limitations:
- Nets must be feed-forward, with a binary step activation function
- Nets currently must be hand-crafted
- Nets must be used for classification tasks in discrete domains
- Nets learn via (unsupervised) Hebbian learning
- Knowledge bases are expressed in a certain restricted modal syntax (see below)

## 📝 Planned Features:
- Model building
- Counter-model building
- Proper sigmoid activation functions
- Plug-and-play with your existing Tensorflow model
- Tasks beyond classification
- Learning via backpropagation (!)
- Predicate/quantifier reasoning

# 💻 Installation


# :brain: Trying It Out
This program is currently in development, and many of the planned features involve significant research efforts.  So what the program can do right now is somewhat limited.  What you _can_ do with it is hand-craft a neural network and infer some things about what the net knows, expects, and learns.  (There is planned support for being able to plug-and-play with your own Tensorflow model.) 

To get you started, copy the following into a file within your `neural-semantics/` directory -- say `neural-semantics/penguin.py`.  Now navigate to this directory in your terminal and run `python3 penguin.py` (or `py penguin.py` for Windows).

```python
from BFNN import *
from Model import *

# An example that illustrates how Hebbian learning can learn
# a counterexample to a conditional while preserving the conditional.
# In this case, the net learns that penguins don't fly, while preserving
# the fact that typically birds *do* fly.
nodes = set(['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'])
layers = [['a', 'b', 'c', 'd', 'e'], ['f', 'g'], ['h']]
weights = {('a', 'f'): 1.0, ('a', 'g'): 0.0, ('b', 'f'): 0.0, ('b', 'g'): -2.0, 
           ('c', 'f'): 0.0, ('c', 'g'): 3.0, ('d', 'f'): 0.0, ('d', 'g'): 3.0,
           ('e', 'f'): 0.0, ('e', 'g'): 3.0, ('f', 'h'): 2.0, ('g', 'h'): -2.0}
threshold = 0.0
rate = 1.0
prop_map = {'bird': {'a'}, 'penguin': {'a', 'b'}, 
            'orca': {'b', 'c'}, 'zebra': {'b', 'd'}, 
            'panda': {'b', 'e'}, 'flies': {'h'}}
net = BFNN(nodes, layers, weights, threshold, rate)
model = Model(net, prop_map)

print("> penguin → bird \n    ", model.is_model("penguin → bird"), "\n")
print("> bird ⇒ flies \n    ", model.is_model("bird ⇒ flies"), "\n")
print("> penguin ⇒ flies \n    ", model.is_model("penguin ⇒ flies"), "\n")
print("> orca+ zebra+ panda+\n>  (bird ⇒ flies) \n    ", model.is_model("orca+ (zebra+ (panda+ (bird ⇒ flies)))"), "\n")
print("> orca+ zebra+ panda+\n>  (penguin ⇒ flies) \n    ", model.is_model("orca+ (zebra+ (panda+ (penguin ⇒ flies)))"))
```

The functions `model.is_model(expr)` and `model.interpret(expr)` accept the following syntax:
| Easy to Write | Easy to Read |
| -------------- | --------- |
| `not P`        | `¬ P`     |
| `P and Q`      | `P ∧ Q`   |
| `P or Q`       | `P ∨ Q`   |
| `P implies Q`  | `P → Q`   |
| `P iff q`      | `P ↔ Q`   |
| `knows P`      | `K P`     |
| `typ P`        | `T P`     |
|  `P up Q`      | `P+ Q`    |

`P` and `Q` can be replaced by almost any string of alphas, with one major exception:  Avoid using capital `T` and capital `K`.  The convention I recommend is to use `A`, `B`, `C`, ... for variables, and `lowercase`, `strings` when you want to use actual strings.

For logicians/knowledge engineers: `K` acts like an S4 modality (think "knows P"), `T` acts like a non-normal ENT4 modality (turns out to be "typically P" or "the typical P".  We can also express nonmonotonic (defeasible) conditionals in this language -- `Typ P implies Q` is a loop-cumulative conditional.

If you want insight into _why_ these specific modal operators, note that each modal operator corresponds directly to some internal behavior of the neural network.  The mapping is:
| Syntax      | Neural Network  |
| ----------- | ------------------------------------------- |
| `K P`       | The neurons **reachable** from the set `P`  |
| `T P`       | **Forward-Propagation** of `P`              |
|  `P+ Q`     | Do **Hebbian Update** on `P`, then eval `Q` |


# 🔗 Links and Resources
For more details on what makes this neuro-symbolic interface work, see our [paper](https://journals.flvc.org/FLAIRS/article/download/130735/133901).

What drives our program is the idea that neural networks can be used as formal semantics of knowledge bases.  If you're interested in learning more, I highly recommend starting with:

- Leitgeb, Hannes. **Neural network models of conditionals: An introduction**. [[pdf]](https://www.academia.edu/download/32793110/LeitgebSanSebastianFINAL.pdf)
- A.S. d’Avila Garcez,  K. Broda, D.M. Gabbay.  **Symbolic knowledge extraction from trained neural
networks: A sound approach**.  [[pdf]](https://www.sciencedirect.com/science/article/pii/S0004370200000771/pdf?md5=f782984da6f1244a563048b352a31ce5&pid=1-s2.0-S0004370200000771-main.pdf)
- Laura Giordano, Valentina Gliozzi, and Daniele Theseider Dupré.  **A conditional, a fuzzy and a probabilistic interpretation
of self-organising maps**. [[pdf]](https://arxiv.org/pdf/2103.06854.pdf)
