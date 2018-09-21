# Yggdrasil

![Yggdrasil - The Mundane Tree](/phd/yggdrasil/raw/branch/master/yggdrasil.jpg)

Yggdrasil is a UC-based system for modelling security protocols.

## Not Asked Questions

Q: Why Haskell?

A: In an environment where things behave adversarially, having a very powerful
type system is useful to reason about what things *can* do. Further, pure,
functional languages allow restricting the communication between components
that should not communicate, and lend themselves more easily to formal
reasoning. Eventually the goal is to formally prove statements about execution
as well, but we are a long way off.

Q: Why AGPL?

A: AGPL is actually less strong than I'd like here, but stronger would be
unreasonable. I usually prefer permissive licenses, however it is crucial for
security protocols - and their implementation - to be available for public
scrutiny. If the use of AGPL results in one more protocol being made public, I
consider that a gain.
