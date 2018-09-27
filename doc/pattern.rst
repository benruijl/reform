Pattern matching
================

Pattern matching is an essential part of a term manipulation system. It provides a way to
modify a term by its shape and relations instead of by the actual contents. 
We introduce `wildcards`, which are denoted
as letters followed by a question mark, to match to variables, numbers, and subexpressions.

.. note::

    To see the output for the following examples, either a ``print`` has to be added to the source code,
    or reFORM must be run with the ``-v`` command line option.

For example:

.. code-block:: reform

    expr F = f(5);
    apply {
        id f(x?) = f(x? + 1);
    }

will match the wildcard ``x?`` to ``5``, consequently add 1 to it, and yield

.. code-block:: reform

    f(6)

.. note::

    Contrary to Form, the question mark is repeated on the right hand side!

A wildcard will match any function argument if it occurs by itself 


.. code-block:: reform

    expr F = f(1+x,3);
    apply {
        id f(x?,3) = x?;
    }

yields

.. code-block:: reform

    1+x

A pattern at the ground level (not inside functions) can match to 
a subpart of the factors:

.. code-block:: reform

    expr F = f(1)*f(f(4*x));
    apply {
        id f(f(y?)) = y?;
    }

yields

.. code-block:: reform

    f(1)*x*4


If the pattern contains a term with multiple wildcards, the number needs
to match exactly.

.. code-block:: reform

    expr F = f(x1*x2);
    apply {
        id f(y1?*y2?) = f(y1,y2);
    }


yields

.. code-block:: reform

    1+x

So, 

.. code-block:: reform

    expr F = f(x1*x2*x3);
    apply {
        id f(y1?*y2?) = f(y1,y2);
    }

does not match. In this previous case, there are multiple options. ``y1`` could have matched to 
``x1`` and to ``x2``. The match that reFORM picks is deterministic. If you want to obtain `all` options,
see the ``id all`` option.


A wildcard can be restricted to a certain set of options:

.. code-block:: reform

    expr F = f(f(4))*f(f(3));
    apply {
        id f(x1?{f(4)}) = f(x1);
    }

will only match to ``f(4)``. The restriction can be any expression. However, at the moment
they are not allowed to include any wildcards. Additionally, for numbers you can use
number ranges in the sets: ``<=5,>=5,<5,>5`` to match a number in a range relative to a
reference number (5 in this example.)

.. code-block:: reform

    expr F = f(1)*f(4);
    apply {
        id f(x?{>3}) = f(x1 + 1);
    }

will only change ``f(4)``.

Fractional numbers are allowed, i.e., ``f(x?{>1/2})`` will work as intended.

A function name can also be a wildcard:

.. code-block:: reform

    expr F = g(4);
    apply {
        id f?(x?) = f?(x? + 1);
    }

yields ``g(5)``.

Ranged wildcards
----------------

The pattern matcher can also match ranges of function arguments using
ranged wildcards. These wildcard have a question mark on the front: e.g., ``?a``.

For example:

.. code-block:: reform

    expr F = f(1,2,3,4);
    apply {
        id f(?a,4) = f(?a);
    }

yields

.. code-block:: reform

    f(1,2,3)

Using a combination of ranged wildcards and wildcards, some complex patterns can
be matched:

.. code-block:: reform

    expr F = f(1,2,f(3),4)*f(1,2,f(3));
    apply {
        id f(?a,x?,?b)*f(?c,x?,?d) = f(?a,?b,?c,?d);
    }

yields

.. code-block:: reform

    f(1,2,4,1,2)

Note that ranged wildcards can be empty.

Many-mode
----------------

The ``many`` option can be used to let reFORM apply a pattern to the input
as often as possible.

.. code-block:: reform

    expr F = x^2;
    apply {
        id many x = 5;
    }

yields

.. code-block:: reform

    25

A more complicated example is shown below:

.. code-block:: reform

    expr F = x*y^4*z;
    apply {
        id many x?*y^2 = f(x?);
    }

yields

.. code-block:: reform

    f(x)*f(z)



Obtaining all matches
---------------------

All matches can be obtained using the ``all`` option to ``id``.
For example:

.. code-block:: reform

    expr F = f(1,2,f(x1*x2,x3*x4,x5*x6),x1*x3,x3*x5);
    apply {
        id all f(1,2,f(?a,x1?*x2?,?b),?c,x1?*x3?) = f(x1,x2,x3);
    }

yields

.. code-block:: reform

    f(x3,x4,x5)+f(x5,x6,x3)
