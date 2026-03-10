# Glivenko's theorem underneath structure — Agda formalisation

Agda formalisation accompanying the paper:

> R. Borsetto, G. Fellin, T. Uustalu, C.-S. Wan. *Glivenko's theorem underneath structure*.

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
