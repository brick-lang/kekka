Kekka - 結果
============
Kekka is a λ-k implementation ported from Daan Leijen's Kōka compiler, that will eventually act as Brick's type-inference engine. Kōka (効果) means 'effect' or 'effective', and in recognition of both that and the ultimate purpose of the type system, the name Kekka (結果) was chosen, meaning 'effect' (in the sense of a result or consequence of an action, a slightly different connotation).

Unlike Kōka, which is a complete language, Kekka only strives to act as an inference and unification system, an intermediary step in the full process of compilation. Because of that, the goal is to have a completely AST-independent typing module that is not just usable by Brick/Kiln, but in other projects as well, like for error-checking and semantic analysis tools.

## Documentation
Part of the reason I am porting this is to have a much better understanding of the internals of the system, as it is relatively complex when compared to something like a [simple HM engine](https://github.com/toroidal-code/hm-rb). I also want to explore the possibility of integrating function fragmentation and calling semantics similar to my experimentation in [HMc](https://github.com/toroidal-code/hm-ml), and see how far the effect recogniction can go in the area of concurrency and parallelization.

As I go, I will be documenting what I learn and understand, in hopes that it may also be helpful for other people. Documentation will be sparsely annotated with LaTeX, which can (will be able to) be formatted using [YODA](https://github.com/toroidal-code/yoda). This will not be literate programming, but I hope to add a large amount of documentation on the things that I _do_ understand, as being very new to the field of programming language/type theory, I know from experience how hard it can be to get into.

## Licensing
Kōka is licensed under the Apache License version 2.0. Because this is currently a direct port from Haskell to OCaml (for now), I consider Kekka to be a true derivative work, so it is also licensed under the APLv2.
