reFORM
---------

reFORM is a symbolic manipulation toolkit with the goal to handle expressions with billions
of terms, taking up terabytes of diskspace. In the future, it may be an alternative to FORM.

At the moment reFORM is in early development and cannot handle a large workload yet. However,
the pattern matcher can match some nice patterns.

An example
----

The basic element of reFORM is a term. Each term in the input is treated sequentially.
The reason for this is that the expression (a collection of terms) may not fit in memory.

reFORM works with modules, which are ended by the `sort` statement. In every module,
each term in the input will go through all the statements one by one until they
are merged in the `sort' command. Choosing when to terminate a module is up to the user,
and can greatly affect performance: when there are a lot of duplicate terms, double work
can be avoided by merging them in the `sort`. On the other hand, if there are millions of terms,
the overhead of sorting may be larger than the gain.

Pattern matching
----

````
IN = f(5);
id f(x?) = f(x? + 1);
sort;
````

will match the wildcard `x` to `5`, consequently add 1 to it, and yield

```
f(6)
```

A wildcard will match any function argument if it occurs by itself 

````
IN = f(1+x,3);
id f(x?,3) = x?;
sort;
````

yields
```
1+x
```

A pattern at the ground level (not inside functions) can match to 
a subpart of the factors:

````
IN = f(1)*f(f(4*x));
id f(f(y?)) = y?;
sort;
````

yields
```
f(1)*x*4
```


If the pattern contains a term with multiple wildcards, the number needs
to match exactly.

````
IN = f(x1*x2);
id f(y1?*y2?) = f(y1,y2);
sort;
````

yields
```
1+x
```

So, 
````
IN = f(x1*x2*x3);
id f(y1?*y2?) = f(y1,y2);
sort;
````
does not match. In this previous case, there are multiple options. `y1` could have matched to 
`x1` and to `x2`. The match that reFORM picks is deterministic. If you want to obtain *all* options,
see the `id all` option.



A wildcard can be restricted to a certain set of options:

````
IN = f(f(4))*f(f(3));
id f(x1?{f(4)}) = f(x1);
sort;
````
will only match to `f(4)`. The restriction can be any expression. However, at the moment
they are not allowed to include any wildcards. Additionally, for numbers you can use
number ranges in the sets: `<=5,>=5,<5,>5` to match a number in a range relative to a
reference number (5 in this example.)

````
IN = f(1)*f(4);
id f(x?{>3}) = f(x1 + 1);
sort;
````
will only change `f(4)`.

Fractional numbers are allowed, i.e., `f(x?{>1/2}) will work as intended.


Ranged wilcards
------
The pattern matcher can also match ranges of function arguments using
ranged wilcards `?a`, where `a` is the name of the ranged wildcard.

For example:
````
IN = f(1,2,3,4);
id f(?a,4) = f(?a);
sort;
````
yields
````
f(1,2,3)
````

Using a combination of ranged wildcards and wilcards, some complex patterns can
be matches:
````
IN = f(1,2,f(3),4)*f(1,2,f(3));
id f(?a,x?,?b)*f(?c,x?,?d) = f(?a,?b,?c,?d);
sort;
````
yields
````
f(1,2,4,1,2)
````
Note that ranged wilcards can be empty.

Obtaining all matches
-----

All matches can be obtained using the `all` option to `id`.
For example:

````
IN = f(1,2,f(x1*x2,x3*x4,x5*x6),x1*x3,x3*x5);
id all f(1,2,f(?a,x1?*x2?,?b),?c,x1?*x3?) = f(x1,x2,x3);
sort;
````
yields
````
f(x3,x4,x5)+f(x5,x6,x3)
````

Note that patterns can be nested without problems. The following is an example
of a complex pattern:

f(1,2,f(?a,x1?*x2?,?b))


Repeat
---
A useful statement is repeat, which repeats statements until there is no change anymore.
For example:

````
IN = f(5);
repeat id f(x?{>0}) = x?*f(x?-1);
id f(0) = 1;
````
yields the factorial function 5! = 120.
