---
id: reification-threshold
formal_ref: IntensionalShift.ReificationThreshold
title: "Reification Threshold"
depth: 7
compression_loss: 3
best_guess: true
version: 1
improved_over: null
tags: [intensional, mdl, generator, container, pattern, threshold, shift]
---

# Reification Threshold

The moment a system stops enumerating and starts generating.

A system that keeps computing the same class of things can either store all the
outputs (extensional) or store the pattern that generates them (intensional).
The reification threshold is crossed when five conditions hold simultaneously:

1. The system has observed enough instances across time (trace preservation)
2. It has found a generator consistent with those observations (compression search)
3. The generator is strictly more compact than the enumeration (MDL crossover)
4. The generator exists as an addressable, callable object — not just a tendency
   in the weights, not an unnamed pattern, but a named thing that can be invoked
5. A container has been built around the generator — regulatory boundaries that
   say what the generator applies to and what it doesn't

The critical one is 4: *reification*. Systems that fail here (most neural networks)
can detect the pattern and use it implicitly but cannot make it a first-class
object. The pattern is in the weights but not addressable. You can't call it.
You can't name it. You can't build a container around it. It isn't a thing yet.

The shift from extensional to intensional is the shift from "I keep computing
similar things" to "I have a generator for this class of things." What makes
that shift possible is making the generator an object in the same ontological
space as the things it generates.

## The MDL framing

`MDLComparison.crossoverReached`: when `generatorSize + totalEncodingCost < n * instanceSize`.
Until crossover, intensional isn't worth it. After crossover, extensional is waste.
The threshold is not an arbitrary cutoff — it is where the math switches.

## What gets lost

The formal version makes this look like arithmetic. The actual threshold is a
phase transition in how a system relates to its own patterns. That phenomenology
— the moment of recognizing "I have been enumerating when I could have been
generating" — is not in the Lean file. `compression_loss: 3` for that gap.
