===============
Reference Guide
===============

Procedures
==========

A procedure is a code block that will be inlined at the call-site.

.. frm:statement:: procedure name(args; localargs) { [statements] }

    :param args: arguments to the function
    :param localargs: variables local to the procedure. They will shadow
                      existing variables.

    .. code-block:: reform

        procedure derivative(x, n) {
            for $i in 1..(n+1) {
                id x^m? = m? * x^(m? - 1);
            }
        }

        expr F = u^5;

        apply {
            call derivative(u, 2);
        }

    yields

    .. code-block:: reform

        u^3*20


Statements
==========

.. frm:statement:: apply [name for F1,...,F2 excluding F3,...,] { [statements] };

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

.. frm:statement:: argument f1,f2,... { [statements] }

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

.. frm:statement:: assign x = expr;

    :param x: A variable
    :param expr: A reFORM expression

    Assign the expression to the variable ``x``.

    .. code-block:: reform

        $a = 1 + x;
        print $a;

    yields

    .. code-block:: reform

        1 + x

.. frm:statement:: attrib f = Linear + NonCommutative + Symmetric;

    :param f: A function name.

    Assign attributes to a function. At the moment the options are
    ``Linear``, ``NonCommutative``, and ``Symmetric``. Multiple options
    can be given with a ``+``.

    .. code-block:: reform

        expr F = f(x, y);

        attrib f = Linear;

        apply {
            id f(x1?,x2?) = f(x1?+2,x2?+5);
        }

    yields

    .. code-block:: reform

        +f(x,y)
        +f(x,5)
        +f(2,y)
        +f(2,5)

.. frm:statement:: call proc(args);

    :param proc: A procedure
    :param args: Arguments to the procedure

    Call a procedure with arguments.

    .. code-block:: reform

        procedure derivative(x, n) {
            for $i in 1..(n+1) {
                id x^m? = m? * x^(m? - 1);
            }
        }

        expr F = u^5;

        apply {
            call derivative(u, 2);
        }

    yields

    .. code-block:: reform

        u^3*20


.. frm:statement:: collect fn;

    :param fn: A function name.

    If this statement is called `inside` a module, it will wrap the entire term in a function ``fn``.
    if this statement is called outside the module, it will wrap the entire expression in a function ``fn``.
    The latter is only possible if the expression fits in memory.

    .. code-block:: reform

        expr F = (1+x)^4;

        apply {
            expand;
        }
        collect f;
        print;

    yields

    .. code-block:: reform

        +f(x*4+x^2*6+x^3*4+x^4+1)

.. frm:statement:: expand;

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


.. frm:statement:: expr name = expression;

    :param name: The name of a new expression
    :param expression: Any valid reFORM expression.

    Create a new `expression`. An expression is processed term-by-term
    and can be larger than memory. Use :frm:st:`apply` to operate on the terms of
    the expression.

.. frm:statement:: extract $i x1,...,xn;

    :param $i: A reFORM variable.
    :param x1,...,xn: A list of algebraic variables.

    Construct a Horner scheme in the variables ``x1`` to ``xn`` for
    the expression in variable ``$i``.

    .. code-block:: reform

        $a = x + x*y + x*y*z + y*z + x^2 + x^2*y + 2;

        extract $a x,y;
        print $a;

    yields

    .. code-block:: reform

        (y+1)*x^2+y*z+2+((z+1)*y+1)*x

.. frm:statement:: for i in lb..ub { [statements] };
                   for i in {s1,s2,...} { [statements] };

    :param i: The loop variable.
    :param lb..ub: A numerical range.
    :param {s1,s2,...}: A list of expressions.

    Loop over a numerical range or over a list of expressions.
    Loops can be made both inside and outside of modules.

    .. code-block:: reform

        expr F = f(2);

        for $i in 1..4 {
            print;
            apply {
                id f($i) = f($i+1);
            }
        }

    yields
    
    .. code-block:: reform

        F = f(2);
        F = f(3);
        F = f(4);

.. frm:statement:: id lhs = rhs;

    :param lhs: Any valid reFORM expression with `wildcards`.
    :param rhs: Any valid reFORM expression with `wildcards`.

    Apply the lhs to an active term (therefore an :frm:st:`id` statement needs to
    be in an :frm:st:`inside` or :frm:st:`apply` block (module).

    See :doc:`Pattern matching <pattern>` for the patterns that are allowed to match.

    For example:

    .. code-block:: reform

        expr F = f(5);

        apply {
            id f(x?) = f(x? + 1);
        }

.. frm:statement:: if cond { [statements] } [else { [statements] } ]
                   if match(expr) { [statements] } [else { [statements] } ]

    :param cond: A boolean condition
    :param match(expr): A test to see if an expression matches
    :param statements: Statement block to be executed

    Only execute if a condition holds. If there is an
    ``else`` block, that will only be executed if ``cond`` does not hold.

    .. note:

        At the moment, only the ``match`` variant is activated.

    .. code-block:: reform

        expr F = f(1);

        if match(f(1)) {
            id f(1) = f(2);
        } else {
            id f(x?) = f(1);
        }

    yields
    
    .. code-block:: reform

        f(2)

.. frm:statement:: inside x1,x2,... { [statements] }

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

.. frm:statement:: maximum x;

    :param x: A variable

    Get the maximum of the variable ``x`` over all terms in the module.

    .. code-block:: reform

        $a = 0;
        apply {
            if (match(f(1))) {
                $a = 2;
            } else {
                $a = 1;
            }

            maximum $a;
        }
        print $a;

    yields
    
    .. code-block:: reform

        2

.. frm:statement:: multiply expr;

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

.. frm:statement:: print [format] args;
    
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

.. frm:statement:: repeat { [statements] }

    :param statements: Statement block to be repeated until no terms change anymore.

    Repeat a block of statements until the term does not change anymore.


    The code below does a naive Fibonacci series evaluation. The repeat
    block will continue until none of the three :frm:st:`id` statements match.

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

.. frm:statement:: splitarg fn;

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

.. frm:statement:: symmetrize fn;

    :param fn: A function name.

    Symmetrize the function arguments based on reFORM's internal ordering.

    .. code-block:: reform
        
        expr F = f(3,2,x,1+y,g(5));

        apply {
            symmetrize f;
        }

    yields
    
    .. code-block:: reform

        f(g(5),y+1,x,2,3)


Functions
=========

.. frm:function:: delta_(x1)

    :param x1: A reFORM expression

    Returns 1 if ``x1`` is 0. If it is a number other than 0, it will return 0.

    If ``x1`` is not a number, nothing happens.

    .. code-block:: reform

        expr F = delta_(0)*x + delta_(1)*y + delta_(x);

    yields
    
    .. code-block:: reform
    
        x + delta_(x)

.. frm:function:: gcd_(p1, p2)

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

.. frm:function:: mul_(i, lb, ub, expr)

    :param i: A variable used as a counter
    :param lb: A numeric lower bound for ``i``
    :param ub: A numeric upper bound for ``i``

    Return the product of ``i`` going from ``lb`` to ``ub``.

    .. code-block:: reform

        expr F = mul_($i, 2, 5, $i^2);

    yields
    
    .. code-block:: reform
    
        576

.. frm:function:: nargs_(a1,...an)

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

.. frm:function:: rat_(num, den)

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

.. frm:function:: sum_(i, lb, ub, expr)

    :param i: A variable used as a counter
    :param lb: A numeric lower bound for ``i``
    :param ub: A numeric upper bound for ``i``

    Return the sum of ``i`` going from ``lb`` to ``ub``.

    .. code-block:: reform

        expr F = sum_($i, 2, 5, $i^2);

    yields
    
    .. code-block:: reform
    
        29