/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.*;
import org.junit.*;

public final class TailRecursiveTest extends UnitTest {
    @Test
    public void testRecursiveFunction() {
	prog = "let int fact(int n, int acc)					\n"
		+ "     if (n==1) then {acc} else {fact(n + -1, n*acc)};		\n"
		+ " in fact(10, 1);						\n";
	result = 3628800;
	trace = true;
	tail_rec = true;
	use_indirect = true;
	assertEquals(run(), result);
    }
}

/** @formatter:off
1. original code:
let int fib(int n, int acc)					
     if (n==1) then {acc} else {fib(n + -1, n*acc)};		
 in fib(10, 1);						

2. Symbol Analysis:
base ID of <fib():int> is 0
defined variable n in <fib(int):int>
defined variable acc in <fib(int,int):int>
defined function: <fib(int,int):int>
locals: []
created new generic function: fib
added new method fib(int,int) into generic function fib
 done.
3. Type Analysis:
type of prog is: int
4. Emit Bytecode:
emiting function fib(int,int) [nargs: 2(0+2), nlocals: 0]
nlocals for top-level LET: 0
24 instructs generated totally.
5. Disassemble Bytecode:
Disassembly:
.global 0
  0000:	br         71 [end_fib(int,int)]
.fib(int,int) nargs=2 nlocals=0
begin_fib(int,int):
  0005:	load       0
  0010:	iconst     1
  0015:	ieq          
  0016:	null         
  0017:	ieq          
  0018:	brt        33 [else]
  0023:	load       1
  0028:	br         70 [endif]
else:
  0033:	load       0
  0038:	iconst     -1
  0043:	iadd         
  0044:	load       0
  0049:	load       1
  0054:	imul         
  0055:	store      1
  0060:	store      0
  0065:	br         5 [begin_fib(int,int)]
endif:
  0070:	ret          
end_fib(int,int):
  0071:	iconst     10
  0076:	iconst     1
  0081:	call       #0:fib(int,int)@5
  0086:	halt         

6. Run Bytecode:
Trace:
  0000:	br         71		stack=[ ], calls=[ _main ]
  0071:	iconst     10		stack=[ ], calls=[ _main ]
  0076:	iconst     1		stack=[ 10 ], calls=[ _main ]
  0081:	call       #0:fib(int,int)@5		stack=[ 10 1 ], calls=[ _main ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 10 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 10 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 10 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 10 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 9 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 9 10 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 9 10 1 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 9 10 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 9 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 9 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 9 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 9 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 9 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 8 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 8 9 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 8 9 10 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 8 90 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 8 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 8 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 8 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 8 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 8 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 7 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 7 8 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 7 8 90 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 7 720 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 7 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 7 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 7 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 7 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 7 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 6 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 6 7 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 6 7 720 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 6 5040 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 6 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 6 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 6 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 6 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 6 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 5 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 5 6 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 5 6 5040 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 5 30240 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 5 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 5 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 5 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 5 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 5 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 4 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 4 5 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 4 5 30240 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 4 151200 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 4 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 4 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 4 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 4 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 4 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 3 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 3 4 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 3 4 151200 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 3 604800 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 3 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 3 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 3 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 3 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 3 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 2 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 2 3 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 2 3 604800 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 2 1814400 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 2 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 2 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 2 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 0 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0033:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0038:	iconst     -1		stack=[ 2 ], calls=[ _main fib(int,int) ]
  0043:	iadd         		stack=[ 2 -1 ], calls=[ _main fib(int,int) ]
  0044:	load       0		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0049:	load       1		stack=[ 1 2 ], calls=[ _main fib(int,int) ]
  0054:	imul         		stack=[ 1 2 1814400 ], calls=[ _main fib(int,int) ]
  0055:	store      1		stack=[ 1 3628800 ], calls=[ _main fib(int,int) ]
  0060:	store      0		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0065:	br         5		stack=[ ], calls=[ _main fib(int,int) ]
.fib(int,int) nargs=2 nlocals=0
  0005:	load       0		stack=[ ], calls=[ _main fib(int,int) ]
  0010:	iconst     1		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0015:	ieq          		stack=[ 1 1 ], calls=[ _main fib(int,int) ]
  0016:	null         		stack=[ 1 ], calls=[ _main fib(int,int) ]
  0017:	ieq          		stack=[ 1 0 ], calls=[ _main fib(int,int) ]
  0018:	brt        33		stack=[ 0 ], calls=[ _main fib(int,int) ]
  0023:	load       1		stack=[ ], calls=[ _main fib(int,int) ]
  0028:	br         70		stack=[ 3628800 ], calls=[ _main fib(int,int) ]
  0070:	ret          		stack=[ 3628800 ], calls=[ _main fib(int,int) ]
3628800
 */
