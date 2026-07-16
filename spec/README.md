# Huffman Specification

Given a sequence of symbols (e.g., characters):

1. Construct a [frequency table](#frequency-table) from the input sequence.

## Definitions

### Vocabulary

The set of all symbols in the input sequence.
Typically referred to as $V$.

Example for the input sequence `abracadabra`.

| symbol |
|--------|
| a      |
| b      |
| r      |
| c      |
| d      |

### Frequency Table

A set mapping each symbol $s \in V$ to a frequency $f \in \mathbb{N}$
where $V$ is the [vocabulary](#vocabulary).

Each element is of type $V \times \mathbb{N}$.

Example for the input sequence `abracadabra`.

| symbol | frequency |
|--------|-----------|
| a      | 5         |
| b      | 2         |
| r      | 2         |
| c      | 1         |
| d      | 1         |

