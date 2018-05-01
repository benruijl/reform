Variables
=========

reFORM has variables (not to be confused with the algebraic variables of the input), which are expressions that must fit in memory.
They are shared between terms and between the global and the local scope.

They start with a ``$`` sign.


For example:

.. code-block:: reform

    $a = 5;
    print $a;

yields ``5``.

Variables can be used for many things as this chapter will show. Below we give an example where the variable gives
each term a unique id (if not run in parallel):

.. code-block:: reform

    expr F = x + y + z;

    $counter = 0;
    apply {
        Multiply f($counter);
        $counter = $counter + 1;
        print;
    }

yields

.. code-block:: reform

    x*f(1) + y*f(2) + z*f(3)


Pattern matching
----------------

Parts of a pattern can be stored in a dollar variable using :frm:st:`matchassign`:

.. code-block:: reform

    expr F = f(x,1,2,3);

    $a = 0;
    apply {
        matchassign f(y?,?b) {
            $a = 2*y?*f(?b);
        }
    }
    print $a;

yields

.. code-block:: reform

    2*f(1,2,3)*x


Control flow
------------
Variables are also used as loop parameters in :frm:st:`for`:

.. code-block:: reform

    $a = 0;
    for $i in 1..3 {
        $a = $a + $i;
    }
    print $a;

yields ``2``.

Indexing
--------

Variables can be indexed as if they were functions. Combined with loops this is very flexible:

.. code-block:: reform

    for $i in 1..3 {
        $a[$i+x,2] = $i;
    }

    $b = $a[2+x,4] + f(x);

    inside $b {
        id f(x?) = $a[1+x?,2];
        id $a[x?,?a,y?] = $a[x?,?a,y?-2];
    }

    print $b;

yields ``3``.

As this example shows, variables will be automatically substituted.


Between modules
---------------

Variables can be used to collect global information about an expression, like the maximum value of a certain functions
argument over all the terms. This information can be used in a later module. For example:

.. code-block:: reform

    expr F = f(10) + f(20) + f(30);
    $a = 0;

    apply {
        matchassign f(x?) {
            $a = x?;
        }

        maximum $a;
    }

    apply {
        id f(x?) = f($a);
    }


yields ``3*f(30)``. This piece of code stores the maximum value of ``$a`` over all terms (see :frm:st:`maximum`).
In the next module, ``$a`` will be set to 30.
