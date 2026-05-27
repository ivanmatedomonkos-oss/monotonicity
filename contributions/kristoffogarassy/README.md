# Contribution: definability of images of definable functions

Group: Dancs Bálint, Ronyecz Erik, Renácz József, Csilling Dániel, Fogarassy Kristóf
Contributor: Fogarassy Kristóf
GitHub username: kristoffogarassy

## Task

We worked on the task from the board: if `f : X -> Y` is a definable function, then `Im(f)` is definable.

## What was added

The Lean file `OMinimalStructure_LocalMonotonicity_Image.lean` extends the existing minimal o-minimal framework with a formalization of the image theorem for definable functions.

Main additions:

- `FunctionImage`
- coordinate reindexing for swapping graph variables
- `functionImage_mem_of_graph_mem`
- `functionImage_mem`
- `DefinableFunction.image`
- `DefinableFunction.image_mem`
- `DefinableFunction.image_subset_codomain`

The proof uses the existing closure principles of the framework, especially reindexing and existential projection. It does not use an external library or a ready-made definability theorem.

## Documentation

The file `OMinimalStructure_DetailedWriteup_WithImage.tex` explains the mathematical idea and records the current development.
