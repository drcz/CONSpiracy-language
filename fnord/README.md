a very dirty prototype to explore the problem space.
many things can go wrong, and also i'm 93% sure this is not the way.
BUT the idea was as follows:
(1) convert cpr to d3, a simple lexically-scoped lisp variant
(2) convert d3 to yarr, a fully-inlined (using Y combinator) mystical form where a program is always a single expression.
    [here is also a place where cps-transformation could be done...]
(3) convert yarr-expression to d0/kleene ("lisp with no free vars", as in DERC project) by defunctionalization.
(4) use DERC partial evaluator to propagate as much as possible, thus automatically converting some calls to APPLY into
   normal calls ("lambda lifting"), and propagating some known parts of labels/args where they belong.
   but of course we'd first need to add partially-static expressions to DERC ["easy"].
(6) this simple d0 code we can compile to DRC machine "as always", or -- if it was CPSized -- to FCL code.


