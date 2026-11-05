# Programming in Fibril

This tutorial is an introduction to **using** Fibril, inspired by the structure
and hands-on approach of the [community Idris 2 tutorial](https://idris-community.github.io/idris2-tutorial/).
It is original Fibril material, not a translation or a description of all Idris
features. You should be comfortable running commands and editing text files; no
Idris experience is required.

Fibril is experimental. Its checked subset changes, and the language does not
yet support recursive functions or recursive data such as lists. IO is a hosted
console prototype, not a general effect system. Examples below point to source
files in this repository so you can read and modify real programs. Commands
assume the repository root and the executable `./build/exec/fibril`.

## Contents

1. [Getting started](01-getting-started.md): build, check, evaluate and run.
2. [Values and functions](02-functions.md): declarations, applications and branches.
3. [Types and quantities](03-types-and-quantities.md): generic functions and resource use.
4. [Data and pattern matching](04-data.md): choices, constructors and cases.
5. [Records and interfaces](05-abstraction.md): grouping data and supplying operations.
6. [Console programs and projects](06-projects.md): IO, modules and tests.

Each chapter includes exercises. The [feature guide](../use-cases.md) and linked
reference pages explain exact supported syntax and limitations. To learn how
Fibril itself is implemented, see [Building Fibril](../book/00-orientation.md).
