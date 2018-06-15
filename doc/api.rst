===
API
===

Certain features of reFORM can be used inside other programs
and programming languages using its API. At the moment only
the library for multivariate polynomials is exposed.

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

	a = reform.Polynomial("1+x*y+5")
	b = reform.Polynomial("x^2+2*x*y+y")
	g = a + b

	ag = a * g
	bg = b * g

	print(ag.gcd(bg))


C API
########

To compile the reFORM C library, compile with the ``c_api`` feature:

.. code-block:: bash

	cargo build --release --features=python_api

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

	extern Polynomial* polynomial_new(const char *expr);
	extern void polynomial_free(Polynomial *);
	extern char* polynomial_to_string(Polynomial *);
	extern void polynomial_string_free(char *);
	extern Polynomial* polynomial_add(Polynomial *, Polynomial *);
	extern Polynomial* polynomial_mul(Polynomial *, Polynomial *);
	extern Polynomial* polynomial_sub(Polynomial *, Polynomial *);
	extern Polynomial* polynomial_neg(Polynomial *);
	extern Polynomial* polynomial_gcd(Polynomial *, Polynomial *);


	int main(void) {
	  Polynomial *a = polynomial_new("1+x*y+5");
	  Polynomial *b = polynomial_new("x^2+2*x*y+y");
	  Polynomial *g = polynomial_add(a, b);

	  Polynomial *ag = polynomial_mul(a, g);
	  Polynomial *bg = polynomial_mul(b, g);

	  Polynomial *gcd = polynomial_gcd(ag, bg);

	  char *str = polynomial_to_string(gcd);
	  printf("%s\n", str);

	  polynomial_string_free(str);
	  polynomial_free(a);
	  polynomial_free(b);
	  polynomial_free(g);
	  polynomial_free(ag);
	  polynomial_free(bg);
	  polynomial_free(gcd);
	}