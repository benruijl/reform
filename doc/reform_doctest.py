"""Test reFORM code snippets and check their results."""

import re
import shutil
import subprocess
import tempfile
from os import path

from docutils import nodes
from docutils.parsers.rst import Directive

from six import PY2

from sphinx.builders import Builder
from sphinx.util import logging, status_iterator
from sphinx.util.console import colorize
from sphinx.util.nodes import set_source_info
from sphinx.util.osutil import fs_encoding, relpath


logger = logging.getLogger(__name__)


def ensure_tempdir(app):
    """Create a temporary directory."""
    if not hasattr(app, '_doctest_tempdir'):
        app._doctest_tempdir = tempfile.mkdtemp()
    return app._doctest_tempdir


def cleanup_tempdir(app, exc):
    """Clean up the temporary directory."""
    if exc:
        return
    if not hasattr(app, '_doctest_tempdir'):
        return
    try:
        shutil.rmtree(app._doctest_tempdir)
    except Exception:
        pass
    delattr(app, '_doctest_tempdir')


def remove_whitespace(text):
    """Remove irrelevant white space."""
    punct = r'[\+\-\*\/\^\=\:\(\)\[\]\?\!]'
    text = re.sub(r'\s+', ' ', text)
    text = re.sub(r'\s(?=' + punct + ')', '', text)
    text = re.sub(r'(?<=' + punct + ')\s', '', text)
    return text.strip()


class TestDirective(Directive):
    """Base class for doctest-related directives."""

    has_content = True
    required_arguments = 0
    optional_arguments = 1
    final_argument_whitespace = True
    option_spec = {}

    def run(self):
        """Return a literal docutils node."""
        code = '\n'.join(self.content)
        nodetype = nodes.literal_block
        if self.arguments:
            groups = [x.strip() for x in self.arguments[0].split(',')]
        else:
            groups = ['default']
        node = nodetype(code, code, testnodetype=self.name, groups=groups)
        set_source_info(self, node)
        if self.name == 'testcode' or self.name == 'testoutput':
            node['language'] = 'reform'
        return [node]


class DoctestBuilder(Builder):
    """Doctest builder."""

    name = 'doctest'

    def init(self):
        """Perform initialization."""
        self.total_tries = 0
        self.total_failures = 0

    def get_outdated_docs(self):
        """Return outdated output files."""
        return self.env.found_docs

    def get_target_uri(self, docname, typ=None):
        """Return the target URI for a document."""
        return ''

    def write(self, build_docnames, updated_docnames, method='update'):
        """Run the code snippets (instead of writing documents)."""
        if build_docnames is None:
            build_docnames = sorted(self.env.all_docs)

        with logging.pending_warnings():
            for docname in status_iterator(
                    build_docnames,
                    'running tests... ',
                    'darkgreen',
                    len(build_docnames),
                    self.app.verbosity):
                doctree = self.env.get_and_resolve_doctree(docname, self)
                self._test_doc(docname, doctree)

    def finish(self):
        """Write the summary."""
        def s(v):
            return v != 1 and 's' or ''
        test_line = '{0:>5} test{1}'.format(self.total_tries,
                                            s(self.total_tries))
        fail_line = '{0:>5} failure{1} in tests'.format(self.total_failures,
                                                        s(self.total_failures))
        if self.total_failures == 0:
            fail_line = colorize('darkgreen', fail_line)
        else:
            fail_line = colorize('red', fail_line)
        self._out('''
Doctest summary
===============
{0}
{1}
'''.format(test_line, fail_line))
        if self.total_failures:
            self.app.statuscode = 1

    def _out(self, text):
        logger.info(text, nonl=True)

    def _test_doc(self, docname, doctree):
        def condition(node):
            return (isinstance(node, nodes.literal_block) and
                    'testnodetype' in node)

        def hr(line=None):
            linewidth = 79
            if line is None:
                return '=' * linewidth
            w = len(line) + 2
            if w <= linewidth:
                w1 = (linewidth - w) // 2
                w2 = linewidth - w - w1
                return '=' * w1 + ' ' + line + ' ' + '=' * w2
            else:
                return '= ' + line + ' ='

        last_source = None
        last_filename = None
        last_line_number = None
        last_output = None

        for node in doctree.traverse(condition):
            source = node['test'] if 'test' in node else node.astext()
            filename = self.get_filename_for_node(node, docname)
            line_number = self.get_line_number(node)

            typ = node.get('testnodetype')
            if typ == 'testcode':
                tempfilename = path.join(
                    ensure_tempdir(self.app),
                    '{0}-{1}.rfm'.format(docname, line_number))
                with open(tempfilename, 'w') as f:
                    f.write(source)
                p = subprocess.Popen(
                    ['reform', tempfilename],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE)
                out, err = p.communicate()
                out = out.decode('ascii')
                err = err.decode('ascii')
                returncode = p.returncode
                self.total_tries += 1
                if returncode != 0 or err:
                    self.total_failures += 1

                    last_source = None
                    last_filename = None
                    last_line_number = None
                    last_output = None

                    text = ''
                    if returncode != 0:
                        text += hr('{0}:{1} returned {2}'.format(
                            filename, line_number, returncode))
                    else:
                        text += hr('{0}:{1} put text into stderr'.format(
                            filename, line_number))
                    if source:
                        text += '\n' + source.rstrip()
                    if out:
                        text += '\n' + hr('stdout') + '\n' + out.rstrip()
                    if err:
                        text += '\n' + hr('stderr') + '\n' + err.rstrip()
                    if text:
                        text += '\n' + hr() + '\n\n'
                    self._out(colorize('red', text))
                else:
                    last_source = source
                    last_filename = filename
                    last_line_number = line_number
                    last_output = out
            elif typ == 'testoutput':
                if last_output is not None:
                    if (remove_whitespace(source) !=
                            remove_whitespace(last_output)):
                        self.total_failures += 1
                    text = hr('{0}:{1} failed'.format(
                        last_filename, last_line_number))
                    if last_source:
                        text += '\n' + last_source.rstrip()
                    text += '\n' + hr('stdout') + '\n' + last_output.rstrip()
                    text += ('\n' + hr('must be') + '\n' + source.rstrip())
                    if text:
                        text += '\n' + hr() + '\n\n'
                    self._out(colorize('red', text))

                last_source = None
                last_filename = None
                last_line_number = None
                last_output = None

    # The following two methods are taken from sphinx.ext.doctest.

    def get_filename_for_node(self, node, docname):
        # type: (nodes.Node, unicode) -> str
        """Get get the file which actually contains the doctest."""
        try:
            filename = relpath(node.source, self.env.srcdir)\
                .rsplit(':docstring of ', maxsplit=1)[0]
        except Exception:
            filename = self.env.doc2path(docname, base=None)
        if PY2:
            return filename.encode(fs_encoding)
        return filename

    @staticmethod
    def get_line_number(node):
        # type: (nodes.Node) -> Optional[int]
        """Get the real line number or admit we don't know."""
        # TODO:  Work out how to store or calculate real (file-relative)
        #       line numbers for doctest blocks in docstrings.
        if ':docstring of ' in path.basename(node.source or ''):
            # The line number is given relative to the stripped docstring,
            # not the file.  This is correct where it is set, in
            # `docutils.nodes.Node.setup_child`, but Sphinx should report
            # relative to the file, not the docstring.
            return None
        if node.line is not None:
            # TODO: find the root cause of this off by one error.
            return node.line - 1
        return None


def setup(app):
    """Set up the extension."""
    app.add_directive('testcode', TestDirective)
    app.add_directive('testoutput', TestDirective)
    app.add_builder(DoctestBuilder)
    app.connect('build-finished', cleanup_tempdir)
    return {'version': '0.1.0'}
