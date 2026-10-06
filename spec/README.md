# Huffman Specification

## Encoding

Given a sequence of symbols (e.g., characters):

1. Construct a [frequency table](#frequency-table) from the input sequence.

## Decoding

## Definitions

### Vocabulary

The set of all symbols present in the input sequence.
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

### Prefix Code Table

A set mapping each symbol $s \in V$ to a binary codeword (code) $c$.
No code is a prefix of any other code in the same code table.

$\forall (s_1, c_1), (s_2, c_2) \in P:\quad c_1 \sqsubseteq c_2 \implies c_1 = c_2$

> For every entry in a code table $P$, if a code is a prefix of another code, they are equal.

The prefix relation $\sqsubseteq$ is defined as:

$c_1 \sqsubseteq c_2 \iff \exists\, t \in {0,1}^*, c_1 \cdot t = c_2$

> There exists a binary code $t$ such that $c_1$ concatenated ($\cdot$) with $t$ equals $c_2$.

## Proofs

## Prefix Free Encoding

Code tables are prefix free.
A code table is prefix free if no code is a prefix of any other code in the same table.

## Prefix Code Optimality

A prefix code table can always achieve the optimal data compression among any character code.

## Tree Optimality

> An optimal code for a file is always represented by a _full_ binary tree,
in which every nonleaf node has two children (see Exercise 16.3-2).

