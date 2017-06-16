## A bytecode compiler and interpreter for FOOL+ language
Course project of ANALISI STATICA DI PROGRAMMI

In this course project, we have implemented a bytecode compiler and interpreter for an object-oriented (OO) language called FOOL+, which is based on a toy
 programming language called FOOL, given by professor. Various types of syntactic and semantic analysis are implemented, including scope and type checkings.
 The OO extension is single-inheritance, and is based on generic function instead of message-passing model. Multi-methods, polymorphic types, and
 dynamic method dispatching are supported. Beside the OO extension, tail-recursion optimization of function calls is also implemented.
To compile and run source code written in this new language, we have also defined a set of bytecode instructions and implemented a stack-based interpreter.
Finally the compiler has ability to save the compiled bytecode into disk files and execute the saved bytecode.
The whole project is written in Java programming language, and the only dependent external library is ANTLR (version 4.7 and later).
