=================
Introduction
=================

reFORM is a symbolic manipulation toolkit with the goal to handle expressions with billions
of terms, taking up terabytes of diskspace. In the future, it may be an alternative to `FORM <https://github.com/vermaseren/form>`_.

At the moment reFORM is in early development and cannot handle a large workload yet. However,
there are many components that work. Specifically, the C and Python API for multivariate polynomials is fully functional.
For an overview of all the reFORM features, see the `manual <https://reform.readthedocs.io/en/latest/>`_.


The basic element of reFORM is a term. Each term in the input is treated sequentially.
The reason for this is that the expression (a collection of terms) may not fit in memory.

reFORM works with modules, which are contained in an ``apply`` statement. In every module,
each term in the input will go through all the statements one by one until they
are merged at the end. Choosing when to split a module is up to the user,
and can greatly affect performance: when there are a lot of duplicate terms, double work
can be avoided by splitting the operations over multiple modules. On the other hand, if there are millions of terms,
the overhead of sorting may be larger than the gain.