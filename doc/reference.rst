===============
Reference Guide
===============

Statements
==========

.. TODO: order alphabetically, use custom reform domain

.. c:function:: apply [name for F1,...,F2 excluding F3,...,] { [statements] };

    :param name: Optional name of the module
    :param statements: A list of statements that will be applied

    Apply a list of statements (a module) to all active expressions.
    If ``for F1,...,F2`` is specified, the module is only applied to these
    expressions. It is also possible to apply the module to all expressions
    excluding some by using ``excluding F3,...``. The ``apply`` statement
    cannot be nested.

    For example:

    .. code-block:: reform

        expr F = f(5);
        apply {
            id f(x?) = f(x? + 1);
            id f(6) = f(3);
        }

    The statements will be processed term by term.
    

.. c:function:: expr name = expression;

    :param name: The name of a new expression
    :param expression: Any valid reFORM expression.

    Create a new `expression`. An expression is processed term-by-term
    and can be larger than memory. Use `apply`_ to operate on the terms of
    the expression.

.. c:function:: id lhs = rhs;

    :param lhs: Any valid reFORM expression with `wildcards`.
    :param rhs: Any valid reFORM expression with `wildcards`.

    Apply the lhs to an active term (therefore an ``id`` statement needs to
    be in an ``inside`` or ``apply`` block (module).

    See :doc:`Pattern matching <pattern>` for the patterns that are allowed to match.

    For example:

    .. code-block:: reform

        expr F = f(5);

        apply {
            id f(x?) = f(x? + 1);
        }


..  c:function:: splitarg fn

    :param fn: A function

    Split a subexpression in a function argument into new function arguments.
    For example:

    .. code-block:: reform

        expr F = f(1+x+2*y);

        apply {
            splitarg f;
        }

    yields
    
    .. code-block:: reform

        F = f(1,x,2*y)


..  c:function:: repeat { [statements] }

    :param statements: Statement block to be repeated until no terms change anymore.

    Repeat a block of statements until the term does not change anymore.


    The code below does a naive Fibonacci series evaluation. The repeat
    block will continue until none of the three ``id`` statements match.

    .. code-block:: reform

        expr F = f(30);

        apply {
            repeat {
                id f(x?{>1}) = f(x? - 1) + f(x? - 2);
                id f(1) = 1;
                id f(0) = 0;
            }
        }

    yields
    
    .. code-block:: reform

        F = f(1,x,2*y)

.. c:function:: argument f1,f2,... { [statements] }

    :param f1,...: Functions the statements should be applied to.
    :param statements: Statement block to be executed on function arguments

    Execute a block of statements on the arguments of specific functions.

    .. code-block:: reform

        expr F = f(1+x,y*x);

        apply {
            argument f {
                id y = 5;
            }
        }

    yields
    
    .. code-block:: reform

        F = f(1+x,5*x)

.. c:function:: inside x1,x2,... { [statements] }

    :param x1,...: Variables the statements should be applied to.
    :param statements: Statement block to be executed on the terms in variables.

    Execute a block of statements on specific variables.

    .. code-block:: reform

        $x = 1 + x + y*x;

        inside $x {
            id x = 5;
        }
        print $x;

    yields
    
    .. code-block:: reform

        6 + 5*y

.. c:function:: if cond { [statements] } [else { [statements] } ]

    :param cond: A boolean condition
    :param statements: Statement block to be executed

    Only execute if the condition ``cond`` holds. If there is an
    ``else`` block, that will only be executed if ``cond`` does not hold.

    .. code-block:: reform

        $x = 5;

        if $x > 3 {
            $x = $x + 1;
        } else {
            $x = $x - 1;
        }
        print $x;

    yields
    
    .. code-block:: reform

        6

.. c:function:: expand

    Expand all structures. For example, ```(1+x)^5```,
    and ```(1+x)*(1+y)``` will be completely written out.

    .. code-block:: reform

        expr F = (1+x)^2*(1+y);
        apply {
            expand;
        }

    yields
    
    .. code-block:: reform

        +x*y*2
        +x*2
        +x^2
        +x^2*y
        +y
        +1

.. c:function:: print [format] args
    
    :param format: The format for printing. It can either be ``Form`` or ``Mathematica``.
    :param args: a list of objects to print. If empty, it will print all active terms.

    Print the structures listed in ``args``. If the ``Print`` is used in a module block without
    arguments, it will print the
    current term. If it is used outside a module without arguments, it will print all active expressions.

    .. code-block:: reform

        $a = f(x);
        print mathematica $a;

        expr F = 1 + x;
        apply {
            print;
        }

.. c:function:: multiply expr
    
    :param expr: An expression to multiply.
    
    Multiply the expression into the current active term. ``Multiply`` can only be used in a module.

    .. code-block:: reform
        
        expr F = y;
        apply {
            Multiply 1 + x;
        }

    yields
    
    .. code-block:: reform

        y*(1+x)

TODO:
ForIn(Element<ID>, Vec<Element<ID>>, Vec<Statement<ID>>),
ForInRange(Element<ID>, Element<ID>, Element<ID>, Vec<Statement<ID>>),
Multiply(Element<ID>),
Symmetrize(ID),
Collect(ID),
Extract(Vec<ID>),
Assign(Element<ID>, Element<ID>),
Maximum(Element<ID>),
Call(String, Vec<Element<ID>>),
Attrib(Element<ID>, Vec<FunctionAttributes>),


Functions
=========

.. c:function:: rat_(num, den)

    :param num: A multivariate polynomial with integer numbers as coefficients
    :param den: A multivariate polynomial with integer numbers as coefficients

    The ``rat_`` function can be used to have a ratio of multivariate polynomials as a coefficient
    . It will compute multivariate gcds to make sure the fraction does not grow more than necessary.

    If the arguments are not valid polynomials, no replacement will be made.

    .. code-block:: reform

        expr F = rat_(x^2+2*x+1,1)*rat_(1,1+x)+rat_(2,1);

    yields
    
    .. code-block:: reform
    
        rat_(3+x,1)


.. c:function:: gcd_(p1, p2)

    :param p1: A multivariate polynomial with integer numbers as coefficients
    :param p2: A multivariate polynomial with integer numbers as coefficients

    Compute the greatest common divisor of two multivariate polynomials with integer numbers as a coefficient.
    
    If the arguments are not valid polynomials, no replacement will be made.

    .. code-block:: reform

        expr F = gcd_(100+100*x-90*x^3-90*x^4+12*y+12*x*y+3*x^3*y^2+3*x^4*y^2,
                      100-100*x-90*x^3+90*x^4+12*y-12*x*y+3*x^3*y^2-3*x^4*y^2);

    yields
    
    .. code-block:: reform
    
        +x^3*y^2*3
        +x^3*-90
        +y*12
        +100

.. c:function:: delta_(x1)

    :param x1: A reFORM expression

    Returns 1 if ``x1`` is 0. If it is a number other than 0, it will return 0.

    If ``x1`` is not a number, nothing happens.

    .. code-block:: reform

        expr F = delta_(0)*x + delta_(1)*y + delta_(x);

    yields
    
    .. code-block:: reform
    
        x + delta_(x)

.. c:function:: nargs_(a1,...an)

    :param a1,...,an: A list of expressions

    Returns the number of arguments the function has.
    It is especially useful in combination with the
    :doc:`ranged wildcards <pattern>`.

    .. code-block:: reform

        expr F = f(1,2,3,4,5);

        apply {
            id f(?a) = nargs_(?a);
        }

    yields
    
    .. code-block:: reform
    
        5

.. c:function:: sum_(i, lb, ub, expr)

    :param i: A variable used as a counter
    :param lb: A numeric lower bound for ``i``
    :param ub: A numeric upper bound for ``i``

    Return the sum of ``i`` going from ``lb`` to ``ub``.

    .. code-block:: reform

        expr F = sum_($i, 2, 5, $i^2);

    yields
    
    .. code-block:: reform
    
        29
         
.. c:function:: mul_(i, lb, ub, expr)

    :param i: A variable used as a counter
    :param lb: A numeric lower bound for ``i``
    :param ub: A numeric upper bound for ``i``

    Return the product of ``i`` going from ``lb`` to ``ub``.

    .. code-block:: reform

        expr F = mul_($i, 2, 5, $i^2);

    yields
    
    .. code-block:: reform
    
        576