below-the-top
=============

#### What is this?
``below-the-top'' is two pieces of code.  The first piece is an engine for interpreting code in sexpression
languages, commonly lisp.  The front end of the engine is a tokenizor (that is capable of handling read macros).
On top of the tokenizor is the transformation machine.  This machine takes a set of sexpressions and maps them into
some result set (often another set of sexpressions).  In this implementation you can see me use several different
transformers which feed into one another: 'type, 'expand, 'eval.  Take a look at transform(...),
back-talk-sexpr(...) and back-talk-arg(...) to get an idea of how the system works at a high level.

The goal of the machine is to dispatch on the type of the first subexpression in the sexpression (called the lead or
head or car).  This dispatching effort allows us to control if the lead gets it's arguments before or after they've
been transformed; and it also allows us to do function application for each data type differently.

This dispatching requires that each type of transformer implements inform(...) and pass(...) for each data type that
it supports.  For example, the 'expand transform should implement inform(...)/pass(...) for the Form (macro) data type;
but probably not for the Number data type.  A fundamental part of maru is that this behavior can be changed at runtime
through the *applicators* variable; the backend of this is the :around hook on the 'eval pass(...) for ``basic-object''.
If an *applicators* exists for the given data type we dispatch here instead of to the hardcoded behavior.

#### What is maru?
``Maru is a symbolic expression evaluator that can compile its own implementation language.''
You can read more about it here http://piumarta.com/software/maru/
