=================
Installation
=================

reFORM is written in Rust, so one first needs to install the Rust compiler.
The easiest way is to install Rustup, using:

.. code-block:: bash

    curl https://sh.rustup.rs -sSf | sh

For more information, see the official `Rust installation guide <https://www.rust-lang.org/en-US/install.html>`_.


The reFORM source code can be obtained from Bitbucket:

.. code-block:: bash

    git clone git@bitbucket.org:benruyl/reform.git

To compile in release mode, use:

.. code-block:: bash

    cargo build --release

You will find the binary ``reform`` in ``target/release``.

To compile the with API support, please see the :doc:`api` section.
