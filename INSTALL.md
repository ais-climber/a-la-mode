# Installation Instructions

To run the scripts, you will need the following packages and libraries installed:

- Python (obviously), any version >= 3.x
- tensorflow 2.x
    - Installation instructions:
      https://www.tensorflow.org/install/pip
      This should also install the Keras front-end.
- pyparsing >= 3.0.x
    - `python3 -m pip install pyparsing`
      I used version 3.0.7 for development.  Note that older versions
      (<= 3.0.x) use deprecated function names, and are not compatible
      with our scripts at present.
- numpy >= 1.22.x
    - `python3 -m pip install numpy`
      Older versions will probably do just fine.
      