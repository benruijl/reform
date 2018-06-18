=================
Quick start
=================

We will start with a simple reFORM program that adds one to an argument of a function:

.. testcode:: reform

	expr F = f(5);

	apply {
	    id f(x?) = f(x? + 1);
	}
	print;

This code creates an expression `F`, and applies a list of instructions (a *module*) to every term in the expression.
This example will yield:

.. testoutput:: reform

	F = f(6)


Save the code in a file called ``add.rfm`` and use 

.. code-block:: bash

	reform add.rfm

to run it and check the result for yourself.


A big difference between reFORM and languages such as Mathematica and Maple is that every operation inside a 
module will be applied to each term independently.


If you want to run with multiple cores, you can specify them with the ``-w`` flag.