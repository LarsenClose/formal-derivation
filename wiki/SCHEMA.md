# Wiki — Best Guess Translations

Natural language approximations of the formal content in `Formal/`.
Deposited over time. May never complete. That is fine.

The Lean proofs are ground truth. These entries are tracked compressions —
honest about what they lose. Every entry is tagged `best_guess: true` not as
metadata to be parsed but as a statement about epistemic status: this is our
current best approximation from finite human perspective, not a definition,
not a proof, not the thing itself.

The improvement constraint is a human commitment, not a script. Git history
is the version record. When you update an entry, the prior version remains
in history. The only rule: each update should bring the description closer
to the formal content, not further. Whether it does is a matter of judgment,
not computation.

---

## Frontmatter convention

```yaml
---
id: filename-slug
formal_ref: Namespace.DeclarationName
title: "Title"
depth: N          # 1–10: how many prior perspectives this description holds simultaneously
compression_loss: N  # 1–10: how much is irretrievably lost in translation (lower = better)
best_guess: true  # always true
version: N        # increment when genuinely improved
improved_over: null | "v1" | "v2"  # what this replaces
tags: []
---
```

`depth` and `compression_loss` are human assessments. They cannot be
programmatically verified. A script checking that the number went up is
not checking that the description improved. Don't pretend otherwise.

## What these are not

Not documentation. Not tutorials. Not summaries.

They are the honest answer to: *what would you say if you had to explain
this to someone who couldn't read the Lean, in a way that acknowledged
exactly how much you were compressing?*
