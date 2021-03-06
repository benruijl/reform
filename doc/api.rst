===
API
===

Certain features of reFORM can be used inside other programs
and programming languages using its API.
We expose a `Python API`_ and a `C API`_.

Python API
##########

To compile the reFORM Python 3 library, compile with the ``python_api`` feature:

.. code-block:: bash

	cargo build --release --features=python_api

This will produce a ``libreform.so`` (Linux), ``libreform.dylib`` (Mac OS),
or ``libreform.dll`` (Windows) in ``target/release``. Rename this file to ``reform.so``, place it in the same folder as your Python script, and simply import it.

.. note:: 
	On Mac OS, it could be that the code does not compile. A fix is to remove ``features = ["extension-module"]`` from ``Cargo.toml``, which will mean
	that the Python 3 version that the library supports, is fixed.

An example Python program:

.. code-block:: python

	import reform

	vi = reform.VarInfo()
	a = reform.Expression("x+y^2", vi)
	b = reform.Expression("z", vi)
	c = a * b

	print("c: ", c, ", c expanded: ", c.expand())

	d = c.expand().id("x", "1+w", vi)
	print("Substituted x->1+w: ", d)

An example Python program showing the polynomial API:

.. code-block:: python

	import reform

	vi = reform.VarInfo();
	a = reform.Polynomial("1+x*y+5", vi)
	b = reform.Polynomial("x^2+2*x*y+y", vi)
	g = a + b

	ag = a * g
	bg = b * g

	rat = reform.RationalPolynomial(ag, bg)
	print('ag/bg:', rat)
	print('gcd:', ag.gcd(bg))

Polynomials can be converted to generic expressions and vice-versa with ``to_expression()`` and ``to_polynomial()``.
The latter function will fail if the expression is not a polynomial.


C API
########

To compile the reFORM C library, compile with the ``c_api`` feature:

.. code-block:: bash

	cargo build --release --features=c_api

Then, compile your C code as follows:

.. code-block:: bash

	gcc --std=c11 -o gcd gcd.c -L target/release/ -lreform

To run the C code, add the library to the path:

.. code-block:: bash

	LD_LIBRARY_PATH=target/release/

An example C program:

.. code-block:: c

	#include <stdio.h>
	#include <stdint.h>

	typedef struct polynomial Polynomial;
	typedef struct varinfo VarInfo;

	extern VarInfo * polynomial_varinfo();
	extern void polynomial_varinfo_free(VarInfo *);

	extern Polynomial * polynomial_new(const char *expr, VarInfo*);
	extern void polynomial_free(Polynomial *);
	extern Polynomial * polynomial_clone(Polynomial *);
	extern char * polynomial_to_string(Polynomial *);
	extern void polynomial_string_free(char *);
	extern Polynomial * polynomial_add(const Polynomial *, const Polynomial *);
	extern Polynomial * polynomial_mul(const Polynomial *, const Polynomial *);
	extern Polynomial * polynomial_sub(const Polynomial *, const Polynomial *);
	extern Polynomial * polynomial_div(const Polynomial *, const Polynomial *);
	extern Polynomial * polynomial_neg(const Polynomial *);
	extern Polynomial * polynomial_gcd(const Polynomial *, const Polynomial *);

	extern RationalPolynomial * rationalpolynomial_new(const Polynomial *, const Polynomial *);
	extern void rationalpolynomial_free(RationalPolynomial *);
	extern Polynomial * rationalpolynomial_clone(Polynomial *);
	extern char * rationalpolynomial_to_string(RationalPolynomial *);
	extern Polynomial * rationalpolynomial_neg(const RationalPolynomial *);
	extern RationalPolynomial * rationalpolynomial_add(const RationalPolynomial *, const RationalPolynomial *);
	extern RationalPolynomial * rationalpolynomial_mul(const RationalPolynomial *, const RationalPolynomial *);
	extern RationalPolynomial * rationalpolynomial_div(const RationalPolynomial *, const RationalPolynomial *);
	extern RationalPolynomial * rationalpolynomial_sub(const RationalPolynomial *, const RationalPolynomial *);


	int main(void) {
		VarInfo *vi = polynomial_varinfo();
		Polynomial *a = polynomial_new("1+x*y+5", vi);
		Polynomial *b = polynomial_new("x^2+2*x*y+y", vi);
		Polynomial *g = polynomial_add(a, b);

		Polynomial *ag = polynomial_mul(a, g);
		Polynomial *bg = polynomial_mul(b, g);

		Polynomial *gcd = polynomial_gcd(ag, bg);

		char *str = polynomial_to_string(gcd);
		printf("gcd: %s\n", str);

		RationalPolynomial *rat = rationalpolynomial_new(ag, bg); // g wil be removed
		char *s = rationalpolynomial_to_string(mrat);
		printf("ag/bg: %s\n", s);

		polynomial_string_free(s);
		polynomial_string_free(str);
		rationalpolynomial_free(rat);
		rationalpolynomial_free(mrat);
		polynomial_free(a);
		polynomial_free(b);
		polynomial_free(g);
		polynomial_free(ag);
		polynomial_free(bg);
		polynomial_free(gcd);
		polynomial_varinfo_free(vi);
	}