from pygments.lexer import RegexLexer, bygroups, include, default, words, using, this
from pygments.token import \
    Text, Comment, Literal, Operator, Keyword, Name, String, Number, Punctuation

# Inspiration: https://bitbucket.org/birkenfeld/pygments-main/src/default/pygments/lexers/c_cpp.py


class ReformLexer(RegexLexer):
    name = 'reform'

    tokens = {
        'whitespace': [
            (r'\n', Text),
            (r'\s+', Text),
            (r'//(\n|[\w\W]*?[^\\]\n)', Comment.Single),
            (r'/(\\\n)?[*][\w\W]*?[*](\\\n)?/', Comment.Multiline),
            # Open until EOF, so no ending delimeter
            (r'/(\\\n)?[*][\w\W]*', Comment.Multiline),
        ],
        'statements': [
            (r'(L?)(")', bygroups(String.Affix, String), 'string'),
            (r'\d+', Number.Integer),
            (r'\.\.', Operator),
            (r'[;(),]', Punctuation),
            (r'[~!%^&*+=|?:<>/-]', Operator),
            (words(('expr', 'id', 'apply', 'splitarg', 'inside', 'matchassign', 'if', 'else',
                    'multiply', 'mularg', 'argument', 'print'), suffix=r'\b'), Keyword),
            include('expressions')
        ],
        'expressions': [
            (r'\d+', Number.Integer),
            include('function'),
            (r'([a-zA-Z_]\w*)\?', Name.Builtin),  # wildcard
            (r'\$([a-zA-Z_]\w*)', Name.Variable.Global),  # dollar variable
            (r'([a-zA-Z_]\w*)(\s*)(\()',
             bygroups(Name.Function, String, Punctuation)),  # function
            (r'([a-zA-Z_]\w*)', Name.Variable),  # variable
        ],
        'root': [
            default('statement'),
        ],
        'statement': [
            include('whitespace'),
            include('statements'),
            (r'\{', Punctuation, '#push'),
            (r'\}', Punctuation, '#pop'),
        ],
        'string': [
            (r'"', String, '#pop'),
            (r'\\([\\abfnrtv"\']|x[a-fA-F0-9]{2,4}|'
             r'u[a-fA-F0-9]{4}|U[a-fA-F0-9]{8}|[0-7]{1,3})', String.Escape),
            (r'[^\\"\n]+', String),  # all other characters
            (r'\\\n', String),  # line continuation
            (r'\\', String),  # stray backslash
        ],
        'function': [
            (r'\(', Punctuation, '#push'),
            (r'\)', Punctuation, '#pop'),
        ]
    }
