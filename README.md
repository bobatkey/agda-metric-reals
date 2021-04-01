# agda-metric-reals

This is all work in progress, but here's the table of contents / plan / aspirations:

- "Upper" real numbers, defined as closed upper subsets of positive rationals [upper-reals](upper-reals.agda)
  - Each number is represented similarly to an upper Dedekind cut
  - These form a semiring and a complete lattice
- Metric spaces, with distances valued in the upper reals [metric2/base](metric2/base.agda)
  - Form a category with non-expansive maps as morphisms
  - This category has a terminal object [metric2/terminal](metric2/terminal.agda).
  - It has binary products [metric2/product](metric2/product.agda), with distances given by maximum.
  - It has another monoidal structure [metric2/monoidal](metric2/monoidal.agda), with distance given by addition, which is closed [metric2/internal-hom](metric2/internal-hom.agda).
  - It has a graded "scaling" comonad, which allows the expression of all Lipschitz continuous functions by making their Lipschitz constant explicit [metric2/scaling](metric2/scaling.agda).
  - It has a completion monad, which completes a metric space by adding all limit points [metric2/completion](metric2/completion.agda). This is implemented using regular functions as in Russell O'Connor's work (see references below).
  - The rationals form a metric space [metric2/rationals](metric2/rationals.agda), whose completion is the (full) real numbers. This is mostly unfinished.
  - It has a monad of convex combinations [metric2/convex-alg](metric2/convex-alg.agda), i.e. a probability distribution monad. The basic idea follows the Quantitative Algebraic Theories of Mardare, Panangaden and Plotkin. This should allow an integration operator, following the work of O'Connor and Spitters.

The Agda files are being developed with Agda 2.6.1 and standard library 1.5.

## References

- Russell O'Connor: [A monadic, functional implementation of real numbers](https://arxiv.org/abs/cs/0605058). Math. Struct. Comput. Sci. 17(1): 129-159 (2007)
- Russell O'Connor, Bas Spitters: [A computer-verified monadic functional implementation of the integral](https://doi.org/10.1016/j.tcs.2010.05.031). Theor. Comput. Sci. 411(37): 3386-3402 (2010)
- Radu Mardare, Prakash Panangaden, Gordon D. Plotkin: [Quantitative Algebraic Reasoning](https://homepages.inf.ed.ac.uk/gdp/publications/Quantitative_Alg_Reasoning.pdf). LICS 2016: 700-709
