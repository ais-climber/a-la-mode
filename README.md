# Neural Semantics
A neuro-symbolic interface, intended for both **model extraction** (extracting knowledge from a net) as well as **model building** (building a net from a knowledge base).  The name comes from the core idea -- that the internal dynamics of neural networks can be used as formal semantics of knowledge bases.

Our system currently supports:
- :heavy_check_mark: model extraction
- :heavy_check_mark: countermodel generation (via a random search, no construction yet)
- :heavy_check_mark: Hebbian learning -- with syntax for inferring _what a net learns_.
- ❗ feedforward neural networks with binary step activation functions
- ❗ knowledge bases with a certain restricted modal logic syntax (see below)
- ❗ Nets currently must be hand-crafted
- ❗ Nets must be used for classification tasks in discrete domains

Planned features include:
- 📝 model building
- 📝 counter-model building
- 📝 Proper sigmoid activation functions
- 📝 Learning via backpropagation (!)
- 📝 Plug-and-play with your existing Tensorflow model
- 📝 Tasks beyond classification

# :brain: The Translation
( so sentences in a knowledge base correspond to the dynamics of the net)

# 💻 How to Install and Use




# 🔗 Links and Resources
For more details on what makes this neuro-symbolic interface work, see our [paper](https://journals.flvc.org/FLAIRS/article/download/130735/133901).

What drives our program is the idea that neural networks can be used as formal semantics of knowledge bases.  If you're interested in learning more, I highly recommend starting with:

- Leitgeb, Hannes. **Neural network models of conditionals: An introduction**. [[pdf]](https://www.academia.edu/download/32793110/LeitgebSanSebastianFINAL.pdf)
- A.S. d’Avila Garcez,  K. Broda, D.M. Gabbay.  **Symbolic knowledge extraction from trained neural
networks: A sound approach**.  [[pdf]](https://www.sciencedirect.com/science/article/pii/S0004370200000771/pdf?md5=f782984da6f1244a563048b352a31ce5&pid=1-s2.0-S0004370200000771-main.pdf)
- Laura Giordano, Valentina Gliozzi, and Daniele Theseider Dupré.  **A conditional, a fuzzy and a probabilistic interpretation
of self-organising maps**. [[pdf]](https://arxiv.org/pdf/2103.06854.pdf)
