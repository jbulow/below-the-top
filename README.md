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
through the \*applicators\* variable; the backend of this is the :around hook on the 'eval pass(...) for ``basic-object''.
If an \*applicators\* exists for the given data type we dispatch here instead of to the hardcoded behavior.

#### What is maru?
``Maru is a symbolic expression evaluator that can compile its own implementation language.''
You can read more about it here http://piumarta.com/software/maru/

#### How do I bootstrap maru with below-the-top?
First get the code from here http://code.google.com/p/maru/.

Due to some differences between the original boot-eval.c and below-the-top you have to make some small adjustments.
+ emit.l
  + \*globals\* is not implemented in below-the-top; so you have to use _global-environment(...).
  + In the function ``compile-end'' you should change what was originally <code>(cdr \*globals\*)</code> (and is not
    <code>(cdr (\_global-environment))</code>) just <code>(_global-environment)</code>.  The cdr skips \*globals\*; but we don't have
    it.
  + variable ``forms'' does not quote {let, and, or, if, while, set, return} and variable ``operators'' unquotes
    {-, not, +, -, *, /, &, |, ^, <, <=, =, !=, >, <<, >>, oop-at, string-at, set-oop-at, set-string-at}.  All of these
    symbols must be quoted. imaru (ian's maru) uses a function called ``encode'' that replaces symbols binded to
    Fixed and Expr before evaluation occurs; this is the behavior that emit.l is expecting.  below-the-top does not use
    an 'encode transformer.
  + In variable ``forms'' you must also change ``set'' to ``seth''; bmaru (burrows maru) expands set expressions into a
    function called ``seth'' because I didn't want to use the same symbol name for a Form and an Expr.
  + In the function <code>(define-method gen <pair> (comp) ...)</code> there is a syntax error.  The innermost
    ``let'' should be a ``let*''.  
+ At one point I also had to put spaces between symbols and doublequotes because the tokenizor wasn't up to the challenge; but I think this issue is now resolved.

You will also need this code https://github.com/burrows-labs/lisp/blob/master/repl-utils.lisp.  repl-utils are an assortment of misc helper functions.

Open metalang.lisp in your vimitor. Search for ``defparameter \*boot\*''; change the definitions for \*boot\*, \*emit\* and \*eval\* to match your system.

Start your lisp environment and load repl-utils.lisp and metalang.lisp.  In sbcl you'll probably get a bunch of warnings that you should just ``continue'' through.  Next time you load it this shouldn't happen.

If you issue <code>(test)</code> you should pass something like 164/166 tests (as of December 8, 2013).  Now you should be able to build ``seval.s''; but be warned that the process is very slow.  Looking up symbols in bmaru is a pitifully slow endeavor that needs to be reworked; but such is the state of things.

Issue <code>(all)</code>.

