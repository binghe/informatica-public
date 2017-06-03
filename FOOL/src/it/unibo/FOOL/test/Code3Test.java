/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #15: code/3.fool
 */

public final class Code3Test extends ProgTest {
	public static void main(String[] args) {
		prog = "let bool foo(int x)\n if (x==0) then { true }\n else { false };\n in print(foo(3));\n";
		run();
	}
}

/*
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         35
0005:	load       0
0010:	iconst     0
0015:	ieq          
0016:	null         
0017:	ieq          
0018:	brt        33
0023:	iconst     1
0028:	br         34
0033:	null         
0034:	ret          
0035:	iconst     3
0040:	call       #0:foo()@5
0045:	print        
0046:	halt         

7. Run Bytecode:
0
 */
