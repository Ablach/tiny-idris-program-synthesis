# TinyIdris Program Synthesis

## Installation
The system is built using the Idris2 programming language, due to
a lack of backwards comparability the required version is
\texttt{0.2.1} which can be located from the Idris2 GitHub,
\href{https://github.com/idris-lang/Idris2/tree/compat-0.2.1}.

The installation of idris2 requires either chez scheme or racket,
details of how to install this can be found at
\href{https://www.scheme.com/}.

To install Idris2 the commands \texttt{make bootstrap SCHEME=chez}
then \texttt{make install} are run. Depending on the version of
scheme and operating system the first command may change to
\texttt{SCHEME=scheme} or \texttt{SCHEME=chezscheme}. 

The system can be accessed from Github \href{https://github.com/Ablach/tiny-idris-program-synthesis}. The tool is built using the command
\texttt{idris2 --install tinyidris.ipkg} while in the TinyIdris
directory. 

## Usage
TinyIdris can be run using the \texttt{tinyidris}
executable located in the \texttt{build/exec} directory, and passing
the name of a '.tidr' test file. Test files are located within the \texttt{/Test/TestFiles} directory.
If a new TinyIdris source file is created, then it
should be stored within the \texttt{Test/TestFiles}
directory, and an answer file of the same name created in the
\texttt{AnswerFiles} directory using the extension \texttt{.ans}.
The answer file may be left blank. 

While in the TinyIdris repl tree 4 commands may be issued. To evaluate
and type check an expression type the expression, with nothing before
it. To synthesise a definition or term, use the command \texttt{auto},
followed by the name of the hole or the function.
To test synthesis of an individual term run the command \texttt{t},
with the hole name as an argument, or to batch test a group of holes
within a file, simply run \texttt{test}, with no arguments.

In order for the last two commands to work the answer file must contain
solutions for the problem, any holes that do not habe a solution will
be skipped. Solutions are written in the answer file as
\texttt{<name> ! <solution>}.

To exit the tinyidris repl press Ctrl-C.

