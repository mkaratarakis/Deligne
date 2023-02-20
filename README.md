# Toward a formalisation of the statement of Deligne’s Theorem

This repository contains the source code for the short paper "Toward a formalisation of the statement of
Deligne’s Theorem", submitted to [ITP 2023](https://mizar.uwb.edu.pl/ITP2023/). The code runs over Lean 3.49.1 and mathlib's version [4e42a9d0a7](https://github.com/leanprover-community/mathlib/tree/4e42a9d0a79d151ee359c270e498b1a00cc6fa4e) (Nov 28, 2022).

# Installation instructions

The formalization has been developed over Lean 3 and its matemathical library mathlib. For detailed instructions to install Lean, mathlib, and supporting tools, visit the [Lean Community website](https://leanprover-community.github.io/get_started.html).

After installation, run the command leanproject get mkaratarakis/Deligne to obtain a copy of the project's source files and dependencies. To open the project in VS Code, either run path/to/Deligne on the command line, or use the "Open Folder" menu option to open the project's root directory. To compile the project locally, use the command lean --make src.

Copyright (C) 2023, Michail Karatarakis
