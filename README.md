# Neural Semantics
A neuro-symbolic interface, intended for both **model extraction** (extracting knowledge from a net) as well as **model building** (building a net from a knowledge base).  The Neural Semantics is a budding alternative approach to 

It currently supports:
- ✅ model extraction
- ✅ countermodel generation (via a random search, no construction yet)
- ✅ Hebbian learning -- with syntax for inferring _what a net learns_.
- ❗ feedforward neural networks with binary step activation functions
- ❗ knowledge bases with a certain restricted modal logic syntax (see below)
- ❗ Nets currently must be hand-crafted
- ❗ Nets must be used for classification tasks in discrete domains

Planned features include:
- 📝 model building -- build a net from _any_ knowledge base!
- 📝 Proper sigmoid activation functions
- 📝 Learning via backpropagation (!)
- 📝 Plug-and-play with your existing Tensorflow model
- 📝 Tasks beyond classification

# The Translation


# How to Install and Use


# Demo



# 🔗 Links and Resources
For more details on what makes this neuro-symbolic interface work, see our [paper](https://journals.flvc.org/FLAIRS/article/download/130735/133901).

What drives our program is the idea that neural networks can be used as formal semantics of knowledge bases.  If you're interested in learning more, I highly recommend reading:

- Leitgeb, Hannes. **Neural network models of conditionals: An introduction**. [pdf](https://www.academia.edu/download/32793110/LeitgebSanSebastianFINAL.pdf)
- A.S. d’Avila Garcez,  K. Broda, D.M. Gabbay.  **Symbolic knowledge extraction from trained neural
networks: A sound approach**.  [pdf](https://www.sciencedirect.com/science/article/pii/S0004370200000771/pdf?md5=f782984da6f1244a563048b352a31ce5&pid=1-s2.0-S0004370200000771-main.pdf)
- Laura Giordano, Valentina Gliozzi, and Daniele Theseider Dupré.  **A conditional, a fuzzy and a probabilistic interpretation
of self-organising maps**. [pdf](https://arxiv.org/pdf/2103.06854.pdf)
