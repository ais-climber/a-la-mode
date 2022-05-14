# Neural Semantics
A neuro-symbolic interface, intended for both **model extraction** (extracting knowledge from a net) as well as **model building** (building a net from a knowledge base).  The name comes from the core idea -- that the internal dynamics of neural networks can be used as formal semantics of knowledge bases.

**NOTE:** This program is currently **very much in development**, and many of the planned features involve significant research efforts (this is my PhD).  So what the program can do right now is somewhat limited.  

![image](https://user-images.githubusercontent.com/7096372/168408611-afc0ed06-ade7-4854-98f8-e8d564765c33.png)

## :heavy_check_mark: Supported Features:
- Model extraction (assuming we know the meaning of base atoms)
- Countermodel generation (via a random search, no construction yet)
- Modal and conditional reasoning
- Inferring what the net has learned before and after learning

## ❗ Current Limitations:
- Nets must be feed-forward, with a binary step activation function
- Nets currently must be hand-crafted
- Nets must be used for classification tasks in discrete domains
- Nets learn via (unsupervised) Hebbian learning
- Knowledge bases are expressed in a certain restricted modal syntax (see below)
- Base atoms (input, output, and perhaps hidden states) must be given as input

## 📝 Planned Features:
- Model building
- Counter-model building
- Proper sigmoid activation functions
- Plug-and-play with your existing Tensorflow model
- Learning via backpropagation (!)
- (stretch goal) Nice user interface for editing/updating knowledge bases
- (stretch goal) Tasks beyond classification
- (stretch goal) Automatically producing base atoms from a dataset and net
- (extreme stretch goal) Predicate/quantifier reasoning

# 💻 Installation
This program runs on Python3 and Tensorflow.  So first make sure you have these installed:
- **Python:** [Download](https://www.python.org/downloads/) and install any version >= 3.x
- **Tensorflow 2.x:** [Installation Instructions](https://www.tensorflow.org/install/pip)
    - Make sure to install any version 2.x
    - This should also install the Keras front-end.
      For development I'm using the `tf-nightly`, which is probably your best bet for getting this to work.

In addition, you will need the following Python libraries:
- **Pyparsing** >= 3.0.x  via  `python3 -m pip install pyparsing`
    - I used version 3.0.7 for development.  Note that older versions
      (<= 3.0.x) use deprecated function names, and are not compatible
      with our scripts at present.
- **Numpy** >= 1.22.x  via  `python3 -m pip install numpy`
    - Older versions will probably do just fine.

Once you have all of the dependencies installed, clone this repo and run (within this directory):
```
python3 setup.py install
```
If this is successful, you can now `import neuralsemantics.*` in your Python programs!


# :brain: Trying It Out
At the moment, this program lets you hand-craft a neural network and infer some things about what the net knows, expects, and learns.  (There is planned support for being able to plug-and-play with your own Tensorflow model.) 

To get you started, try running the example program
```
python3 examples/penguin.py
```
```python
from neuralsemantics.BFNN import BFNN
from neuralsemantics.Model import Model

nodes = set(['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'])
layers = [['a', 'b', 'c', 'd', 'e'], ['f', 'g'], ['h']]
weights = {('a', 'f'): 1.0, ('a', 'g'): 0.0, 
           ('b', 'f'): 0.0, ('b', 'g'): -2.0, 
           ('c', 'f'): 0.0, ('c', 'g'): 3.0, 
           ('d', 'f'): 0.0, ('d', 'g'): 3.0,
           ('e', 'f'): 0.0, ('e', 'g'): 3.0,
           ('f', 'h'): 2.0, ('g', 'h'): -2.0}
threshold = 0.0
rate = 1.0
prop_map = {'bird': {'a'}, 'penguin': {'a', 'b'}, 
            'orca': {'b', 'c'}, 'zebra': {'b', 'd'}, 
            'panda': {'b', 'e'}, 'flies': {'h'}}

net = BFNN(nodes, layers, weights, threshold, rate)
model = Model(net, prop_map)

print("penguin → bird : ", model.is_model("penguin implies bird"))
print("bird ⇒ flies : ", model.is_model("(typ bird) implies flies"))
print("penguin ⇒ flies : ", model.is_model("(typ penguin) implies flies"))
print("orca+ zebra+ panda+ (bird ⇒ flies) : ", model.is_model("orca+ (zebra+ (panda+ ((typ bird) implies flies)))")) # should be True
print("orca+ zebra+ panda+ (penguin ⇒ flies) : ", model.is_model("orca+ (zebra+ (panda+ ((typ penguin) implies flies)))")) # should be False
```

This file shows how you can hand-code a small feed-forward network model and evaluate its expectations (about whether penguins fly) before and after learning.  Notice that we need to give `prop_map` as input to the net.  The keys of `prop_map` are atomic facts that _we know ahead of time_ produce a specific activation.  e.g. `'penguin': {'a', 'b'}` indicates that a 'penguin' image will always activate `'a'` and `'b'`.  Usually these atomic facts are inputs and outputs, although occasionally we have prior knowledge of hidden states as well.

## Language Syntax
The key functions for you to use are 
- `model.is_model(expr)` (checks if `expr` is follows in the net) 
- `model.interpret(expr)` (gives the set of neurons denoting `expr`).  

Here, `expr` accepts the following syntax:
| Easy to Write | Easy to Read |
| -------------- | --------- |
| `top`, `bot`   | `⊤`, `⊥` |
| `not P`        | `¬ P`     |
| `P and Q`      | `P ∧ Q`   |
| `P or Q`       | `P ∨ Q`   |
| `P implies Q`  | `P → Q`   |
| `P iff q`      | `P ↔ Q`   |
| `knows P`      | `K P`     |
| `typ P`        | `T P`     |
|  `P up Q`      | `P+ Q`    |

`P` and `Q` can be replaced by almost any string of alphas, with one major exception:  Avoid using capital `T` and capital `K`.  The convention I recommend is to use `A`, `B`, `C`, ... for variables, and `lowercase`, `strings` when you want to use actual strings.  Also, parsing is somewhat experimental, so be generous with parentheses.

## What the Syntax Means
Each operator has an interpretation 1) as an operator in logic, and 2) as some internal behavior of the neural network:

### Logical Interpretation
| Syntax      | Properties  | Reading |
| ----------- | -------------------|------------------------ |
| `K P`       | S4 modality  | "knows P" |
| `T P`       | non-normal ENT4 modality | "typically P"/"the typical P"  |
|  `P+ Q`     | dynamic modality that only meaningfully interacts with `T` | "upgrade preference for P, eval Q" |

### Neural Interpretation 
| Syntax      | Neural Network  |
| ----------- | ------------------------------------------- |
| `K P`       | The neurons **reachable** from the set `P`  |
| `T P`       | **Forward-Propagation** of `P`              |
|  `P+ Q`     | Do **Hebbian Update** on `P`, then eval `Q` |


# 🔗 Links and Resources
For more details on what makes this neuro-symbolic interface work, see our [paper](https://journals.flvc.org/FLAIRS/article/download/130735/133901).

What drives our program is the idea that neural networks can be used as formal semantics of knowledge bases.  If you're interested in learning more, I highly recommend starting with:

- Leitgeb, Hannes. **Neural network models of conditionals: An introduction**. [[link to pdf]](https://scholar.google.com/scholar?cluster=2702081425114400974&hl=en&as_sdt=0,15)
- A.S. d’Avila Garcez,  K. Broda, D.M. Gabbay.  **Symbolic knowledge extraction from trained neural
networks: A sound approach**.  [[pdf]](https://www.sciencedirect.com/science/article/pii/S0004370200000771/pdf?md5=f782984da6f1244a563048b352a31ce5&pid=1-s2.0-S0004370200000771-main.pdf)
- Laura Giordano, Valentina Gliozzi, and Daniele Theseider Dupré.  **A conditional, a fuzzy and a probabilistic interpretation
of self-organising maps**. [[pdf]](https://arxiv.org/pdf/2103.06854.pdf)

# :incoming_envelope: Contact
- Is something broken?  You can't run the program?  Suggestions for features?  Feel free to file an issue!
- Want to contribute to bug fixes/quality of life improvements?  Submit a pull request!  (I'd be surprised and flattered!)
- Interested in collaborating on the bigger (i.e. open research question) TODOs?  Head over to my [contact](https://ais-climber.github.io/contact/) page!
