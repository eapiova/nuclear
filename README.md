# Nuclei for substructural logics

Agda formalisation of nuclei and conservation theorems for substructural entailment relations, accompanying the paper:

> E. Apiova, D. Fellin, P. Schuster. *Nuclei for substructural logics*.

## Structure

- `Substructural/Core/` — abstract entailment relations, nuclei, extensions, conservation
- `Substructural/FL/` — Full Lambek logic and its structural extensions (Glivenko, open nuclei)
- `Substructural/Everything.agda` — imports all modules

## Building

Requires [Agda](https://github.com/agda/agda) with the [cubical](https://github.com/agda/cubical) library (version 0.9).

```
agda Substructural/Everything.agda
```

## HTML rendering

A browsable HTML rendering is available at https://eapiova.github.io/nuclear.
