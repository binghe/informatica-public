/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #12: Local function chains with pars
 */

public final class LocalFunsProgTest extends ProgTest {
	public static void main(String[] args) {
		prog = "let int foo(int x) let int bar(int y) x+y; in bar(1); in print foo(2);\n";
		run();
	}
}

/*
5. Emit Bytecode:
defining function foo [nargs: 1(0 + 1), nlocals: 0]
defining function bar [nargs: 2(1 + 1), nlocals: 0]
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         38
0005:	br         22
0010:	load       0
0015:	load       1
0020:	iadd         
0021:	ret          
0022:	load       0
0027:	iconst     1
0032:	call       #1:bar()@10
0037:	ret          
0038:	iconst     2
0043:	call       #0:foo()@5
0048:	print        
0049:	halt         

7. Run Bytecode:
3
 */
