reFORM
---------

reFORM is a symbolic manipulation toolkit with the goal to handle expressions with billions
of terms, taking up terabytes of diskspace. In the future, it may be an alternative to [FORM](https://github.com/vermaseren/form).

At the moment reFORM is in early development and cannot handle a large workload yet. However,
there are many components that work. Specifically, the C and Python API for multivariate polynomials is fully functional.

For an overview of all the reFORM features, see the [manual](https://reform.readthedocs.io/en/latest/).

Quick example
----

````
expr F = f(x,2,3,y);
apply {
    id f(?a,x?{>2},?b) = f(?b,?a);
}
````
This program creates an expression `F` and applies an `id` statement to its term. This statement matches a pattern on the left hand side and modifies it. `?a` and `?b` matches any number of arguments, and `x?{>2}` will match a number larger than two.

The ouput is:
```
F = f(y,x,2);
```
