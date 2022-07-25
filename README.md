# indonesian-mo-formalization
Formalization of Indonesian Mathematical Olympiad problems using Lean | Formalisasi soal-soal OSN/KSN Matematika menggunakan Lean

## File Organization

This repository contains two main folders, `src` and `problems`. The `problems` folder contains the informal statements in Markdown format.  The `src` folder contains the Lean sources of the formalizations.

The `problems` folder contains year folders, where each contains the Markdown files for the informal problem statements. The Markdown filename convention is `<stage>-<year>.md`. 

The `src` folder contain year folders, which contains the stage folders, which contains the Lean files. The Lean filename convention is `<number-2d>-<year>-<stage>.lean`

```
├───problems
│   ├───2002
|   |   ├───osk-2002.md
|   |   ├───osp-2002.md
|   |   └───osn-2002.md
|   ├───...
|   ...
└───src
    ├───2002
    |   ├───osk
    |       ├───01-2002-osk.lean
    |       ├───02-2002-osk.lean
    |       ├───...
    |       ...
    |   ├───osp
    |       ├───01-2002-osp.lean
    |       ├───02-2002-osp.lean
    |       ├───...
    |       ...
    |   └───osn
    |       ├───01-2002-osn.lean
    |       ├───02-2002-osn.lean
    |       ├───...
    |       ...
    ...
```

## Contributing

Before working on a particular problem, search for the issue first to make sure anyone hasn't worked on it yet. If there's no issue, you can create it yourself using the template. If the issue already exists and there's no one assigned yet, you can comment on the issue and wait to be assigned. If someone is already assigned, you may ask that person if you wish to collaborate.