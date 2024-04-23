
# CFML for Lean

This project aims at developing a tool for interactive program verification in Lean,
by porting the technology of the CFML tool implemented in Coq. This tool leverages
a bunch of tactics from the TLC library. Those general-purpose tactics would also
be precious for any Lean user.

https://github.com/charguer/cfml and https://github.com/charguer/tlc

The techniques used in CFML are described in:

  - The Separation Logic Foundations course, part of Software Foundation
    https://softwarefoundations.cis.upenn.edu/
  - The companion course notes
    https://www.chargueraud.org/teach/verif/slf_notes.pdf
  - The lifting technique and the foundational approach are described in:
    https://www.chargueraud.org/research/2023/hdr/chargueraud_hdr.pdf

The necessary steps to port CFML in Lean can be summarized as follows.

  1. Port several key TLC tactics to Lean.
  2. Add a file to the CFML characteristic formula generator for producing
     Lean files instead of Coq files. The generator takes OCaml files as input.
  3. First step is to check the ability to verify purely functional programs.
  4. Second step is to put in place the Separation Logic simplification tactic,
     and the tactics for manipulating representation predicates.
  4. To develop a Rust front-end, one would need to extract a typed AST from
     Rust source files. This AST could be mapped to the characteristic formulae
     AST used internally by CFML. An alternative route would be to go through
     Charguéraud's OptiTrust tool, which aims to integrate CFML at some point.
  5. A longer-term objective is to make the characteristic formulae foundational,
     by proving them sound with respect to an operational semantics.

Details follows.


## TLC Tactics

All TLC tactics are defined in the file:
https://github.com/charguer/tlc/blob/master/src/LibTactics.v
and come with unit tests in the file:
https://github.com/charguer/tlc/blob/master/src/LibTacticsDemos.v

We will need in particular:

- `applys`, `lets`, `forwards`, `specializes`: their implementation is
  carefully described in the file `coq_templates/tlc_tactics/instantiation.v`
- `inverts`: inversion with appropriate substitutions, and possibility to
  name the fresh names introduced.
- `rew_list`, `rew_map`: normalization tactics with respect to a set of rewrite rules.
- `case_if`: a simple wrapper `for case`.
- `induction_wf`: a simple wrapper for well-founded induction.

## TLC Libraries

All TLC libraries are available from:
https://github.com/charguer/tlc/blob/master/src

We will need in particular:

- Classical logic and extensionality axioms, and conversion functions
  between `bool` and `Prop`.
- Formalization of operations on lists with index in Z instead of nat.
- Type-class based overloading of operations like `L[i:=v][j]` for updating
  and reading in a list.
- Formalization of all useful operations and predicates on lists.
- Formalization of finite multisets and finite maps.

## CFML

The first step is to define the characteristic formulae constructors
(e.g. `Wpgen_let`). These definitions come from:
https://github.com/charguer/cfml/blob/master/lib/coq/WPLifted.v

The second step is to implement the characteristic formula generator.
At this stage, we can check that the generate fomulae indeed typecheck.

The third step is to define the x-tactics (e.g. `xlet`). These tactics
are documented in the file:
https://github.com/charguer/cfml/blob/master/lib/coq/WPTactics.v
To begin with, we can axiomatize the x-lemmas, which correspond to
reformulation of the reasoning rules of the program logic.
At this stage, we are ready to verify purely functional code.

The fourth step is to define the separation logic operators.
The relevant file for the definitions is:
https://github.com/charguer/cfml/blob/master/lib/coq/LibSepFunctor.v
and for the tactics
https://github.com/charguer/cfml/blob/master/lib/coq/LibSepSimpl.v
A high-level specification of `xsimpl` is available in appendix K from:
https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf
A commented version of the Ltac implementation should made available soon.

I expect the Lean implementation to be vastly simpler than the
Ltac-based implementation.
At this stage, we are ready to verify basic imperative code.

The fifth step is to port the formalization of records and arrays.
At this stage, we are ready to verify OCaml-style imperative code.
The files
https://github.com/charguer/cfml/blob/master/lib/coq/WPRecord.v
https://github.com/charguer/cfml/blob/master/lib/coq/WPArray.v
contain a bunch of definitions, however the SF course material
describes more recent, improved definitions.

The fifth step is to decrease the TCB. First, by proving the
reasoning rules--the easier part. Second, by realizing the
axioms--the harder part, not yet automated in CFML-for-Coq.

Note: several files have been copied locally into `coq_templates/pure/`
and `coq_templates/effects/` for convenience.

## Case studies

For purely functional code, a good case study is the purely functional implementation
of pairing heaps. See line 206 from the file:
https://github.com/charguer/cfml/blob/master/_attic/VariantPairingHeap.v

For effectful code, a good case study is the imperative implementation of pairing
heaps. See:
https://github.com/charguer/cfml/blob/master/examples/PairingHeap/PairingHeap.ml
https://github.com/charguer/cfml/blob/master/examples/PairingHeap/PairingHeap_proof.v

In the case of a Rust implementation, two routes are interesting to test:
- translate Rust code to functional code, then use CFML on the pure code
- apply CFML directly to the imperative code.

